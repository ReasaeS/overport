#!/usr/bin/perl
use strict;
use warnings;
use Socket;
use File::Basename;
use File::Spec;
use POSIX qw(strftime :termios_h);
use Errno qw(EINTR);
use Cwd 'realpath';
use URI::Escape;
use File::Find;
use Digest::MD5 qw(md5_hex);

# ======================
# Configuration
# ======================
my $PORT        = 9001;
my $HOST        = '127.0.0.1';
my $WEB_ROOT    = $ARGV[0] // File::Spec->catdir(dirname(__FILE__), './src' );

my $REAL_WEB_ROOT = realpath($WEB_ROOT);
die "Invalid web root: $WEB_ROOT\n" unless defined $REAL_WEB_ROOT && -d $REAL_WEB_ROOT;

my $ROOT_PREFIX = $REAL_WEB_ROOT =~ m{/$} ? $REAL_WEB_ROOT : $REAL_WEB_ROOT . '/';

my $INDEX_FILE  = File::Spec->catfile($REAL_WEB_ROOT, 'index.html');
my $PAGE_404    = File::Spec->catfile(dirname(__FILE__), 'status', 'status.html');
my $REAL_PAGE_404 = eval { realpath($PAGE_404) };
my $BUFFER_SIZE = 8192;
my $MAX_REQUEST_SIZE = 16384;
my $READ_TIMEOUT = 5;
my $SEND_STALL_TIMEOUT = 30;

my $HOT_RELOAD         = 1;
my $HOT_RELOAD_PATH    = '/__hotreload';
my $HOT_RELOAD_POLL_MS = 1000;

my $HOT_RELOAD_SCRIPT = <<"END_SCRIPT";
<script>
(function () {
    var current = null;
    function poll() {
        fetch('$HOT_RELOAD_PATH', { cache: 'no-store' })
            .then(function (res) { return res.text(); })
            .then(function (sig) {
                if (current === null) {
                    current = sig;
                } else if (sig !== current) {
                    location.reload();
                    return;
                }
                setTimeout(poll, $HOT_RELOAD_POLL_MS);
            })
            .catch(function () { setTimeout(poll, $HOT_RELOAD_POLL_MS); });
    }
    poll();
})();
</script>
END_SCRIPT

my %MIME_TYPES = (
    html  => 'text/html',
    htm   => 'text/html',
    txt   => 'text/plain',
    css   => 'text/css',
    js    => 'application/javascript',
    json  => 'application/json',
    png   => 'image/png',
    jpg   => 'image/jpeg',
    jpeg  => 'image/jpeg',
    gif   => 'image/gif',
    svg   => 'image/svg+xml',
    ico   => 'image/x-icon',
    pdf   => 'application/pdf',
    zip   => 'application/zip',
    gz    => 'application/gzip',
    mp3   => 'audio/mpeg',
    mp4   => 'video/mp4',
    webm  => 'video/webm',
    woff  => 'font/woff',
    woff2 => 'font/woff2',
    ttf   => 'font/ttf',
    otf   => 'font/otf',
);

# ======================
# TUI color scheme
#   FRAME - structural chrome: borders, separators, rules
#   LABEL - section titles and field names
#   VALUE - data: paths, IPs, sizes, timestamps, URLs
#   GOOD  - healthy/live state, 2xx-3xx responses, follow mode
#   WARN  - degraded state, 4xx responses, scrolled mode, warnings
#   BAD   - errors/dead state, 5xx responses
#   MUTED - secondary text: hints, ages, counters
# ======================
my $RESET = "\e[0m";
my $FRAME = "\e[95m";
my $LABEL = "\e[1;96m";
my $VALUE = "\e[97m";
my $GOOD  = "\e[92m";
my $WARN  = "\e[93m";
my $BAD   = "\e[91m";
my $MUTED = "\e[90m";

$| = 1;

my $IS_TTY = -t STDOUT;
my ($TERM_ROWS, $TERM_COLS) = terminal_size();
my $BAR_HEIGHT = 5;
my $LOG_WIDTH  = 80;

my $last_hot_reload;
my $last_poll_epoch;
my $poll_count    = 0;
my $request_count = 0;

my @log_lines;
my $scroll_offset  = 0;
my $MAX_LOG_LINES  = 2000;
my $termios_orig;

# Star colors are deliberately kept off the TUI color scheme (bright magenta/
# cyan/white/green/yellow/red/grey): blues, indigo, teal, violet, and orange
# tones only, dimmer for far layers and brighter for near ones.
my @STAR_LAYERS = (
    {
        speed   => 0.25,
        char    => '.',
        density => 35,
        colors  => ["\e[2;34m", "\e[38;5;60m", "\e[38;5;66m", "\e[38;5;95m"],
    },
    {
        speed   => 0.50,
        char    => '+',
        density => 24,
        colors  => ["\e[34m", "\e[38;5;104m", "\e[38;5;130m", "\e[38;5;96m"],
    },
    {
        speed   => 0.75,
        char    => '*',
        density => 15,
        colors  => ["\e[94m", "\e[38;5;111m", "\e[38;5;208m", "\e[38;5;135m"],
    },
);

$SIG{WINCH} = sub {
    ($TERM_ROWS, $TERM_COLS) = terminal_size();
    clamp_scroll();
    redraw_screen();
};

my $SECURITY_HEADERS =
    "X-Content-Type-Options: nosniff\r\n" .
    "X-Frame-Options: DENY\r\n";

# ======================
# Socket setup
# ======================
$SIG{PIPE} = 'IGNORE';

socket(my $server, PF_INET, SOCK_STREAM, getprotobyname('tcp')) or die "socket: $!";
setsockopt($server, SOL_SOCKET, SO_REUSEADDR, 1) or die "setsockopt: $!";
bind($server, sockaddr_in($PORT, inet_aton($HOST))) or die "bind: $!";
listen($server, SOMAXCONN) or die "listen: $!";

tui_init();

push_log_records(
    make_rule('#'),
    make_line("${LABEL}Server running at$RESET ${VALUE}http://$HOST:$PORT/$RESET", 'center'),
    make_line("${LABEL}Web root:$RESET $VALUE$REAL_WEB_ROOT$RESET", 'center'),
    make_line("${LABEL}Listening for requests...$RESET", 'center'),
    make_line("${WARN}WARNING: For local development only!$RESET", 'center'),
    make_rule('#'),
    make_line(''),
);

# ======================
# Main loop
# ======================

my $stream_counter = 0;
my $last_time = time() - 5;

my $rin = '';
vec($rin, fileno($server), 1) = 1;
vec($rin, fileno(STDIN), 1) = 1 if $IS_TTY;

while (1) {
    my $rout = $rin;
    my $ready = select($rout, undef, undef, 1);
    next if !defined $ready || $ready < 0;

    if ($ready == 0) {
        draw_status_bar();
        next;
    }

    handle_keys() if $IS_TTY && vec($rout, fileno(STDIN), 1);

    if (vec($rout, fileno($server), 1)) {
        my $client;
        my $client_addr = accept($client, $server) or next;

        handle_client($client, $client_addr);

        close $client if $client;
    }
}

sub handle_client {
    my ($client, $client_addr) = @_;

    my $client_ip = 'unknown';

    eval {
        local $SIG{ALRM} = sub { die "timeout\n" };

        binmode($client);
        setsockopt($client, SOL_SOCKET, SO_SNDTIMEO, pack('l!l!', $SEND_STALL_TIMEOUT, 0));
        $client_ip = inet_ntoa((sockaddr_in($client_addr))[1]) // 'unknown';

        my $request = '';
        my $total_read = 0;

        alarm($READ_TIMEOUT);

        while ($total_read < $MAX_REQUEST_SIZE) {
            my $buffer = '';
            my $bytes = sysread($client, $buffer, $BUFFER_SIZE);

            unless (defined $bytes) {
                last;
            }

            last if $bytes == 0;

            $request .= $buffer;
            $total_read += $bytes;

            last if $request =~ /\r\n\r\n|\n\n/;
        }

        alarm(0);

        if ($total_read >= $MAX_REQUEST_SIZE && !($request =~ /\r\n\r\n|\n\n/)) {
            send_response($client, 413, "Request Entity Too Large", "text/plain", "Request too large", $client_ip, undef);
            return;
        }

        if (!$total_read) {
            return;
        }

        my ($method, $path) = parse_request($request);

        if (!$method || !$path) {
            send_response($client, 400, "Bad Request", "text/plain", "Invalid request", $client_ip, undef);
            return;
        }

        if ($method ne 'GET') {
            send_response($client, 405, "Method Not Allowed", "text/plain", "Method not allowed", $client_ip, undef);
            return;
        }

        if ($path =~ /[^\x20-\x7E]/) {
            send_response($client, 400, "Bad Request", "text/plain", "Invalid characters in path", $client_ip, undef);
            return;
        }

        if ($HOT_RELOAD && $path =~ m{^\Q$HOT_RELOAD_PATH\E(?:[?#]|$)}) {
            $last_hot_reload = strftime("%Y-%m-%d %H:%M:%S", localtime);
            $last_poll_epoch = time();
            $poll_count++;
            send_response($client, 200, "OK", "text/plain", web_root_signature(), $client_ip, $path, quiet => 1);
            draw_status_bar();
            return;
        }

        $request_count++;

        my $file_path = sanitize_path($path);
        if (!$file_path) {
            send_response($client, 403, "Forbidden", "text/plain", "Access denied", $client_ip, $path);
            return;
        }

        serve_file($client, $file_path, $client_ip);
        return;
    };

    my $error = $@;
    alarm(0);

    return unless $error;

    if ($error =~ /timeout/) {
        log_output("${WARN}Request timeout from client$RESET\n");
        send_response($client, 408, "Request Timeout", "text/plain", "Timeout", 'unknown', undef);
    }
    else {
        send_response($client, 500, "Internal Server Error", "text/plain", "Internal error", $client_ip, undef);
    }
}

# ======================
# Terminal utility
# ======================

sub start_stream_banner {
    my ($stream_message) = @_;

    $stream_message =~ s/\e//g;

    push_log_records(
        make_line(''),
        make_line(''),
        make_rule('='),
        make_line($LABEL . "STARTING STREAM..." . $RESET, 'center'),
        make_line($VALUE . $stream_message . $RESET, 'center'),
        make_rule('='),
        make_line(''),
        make_line(''),
    );
}

sub terminal_size {
    return (24, 80) unless -t STDOUT;
    my $size = qx(stty size 2>/dev/null);
    return ($size && $size =~ /^(\d+)\s+(\d+)/) ? ($1, $2) : (24, 80);
}

sub tui_init {
    return unless $IS_TTY;

    $termios_orig = POSIX::Termios->new;
    $termios_orig->getattr(fileno(STDIN));

    my $raw = POSIX::Termios->new;
    $raw->getattr(fileno(STDIN));
    $raw->setlflag($raw->getlflag & ~(ECHO | ICANON));
    $raw->setcc(VMIN, 0);
    $raw->setcc(VTIME, 0);
    $raw->setattr(fileno(STDIN), TCSANOW);

    $SIG{INT} = $SIG{TERM} = sub { exit 0 };

    print "\e[?1049h\e[?25l\e[?7l\e[2J";
    redraw_screen();
}

sub log_height {
    my $height = $TERM_ROWS - $BAR_HEIGHT;
    return $height < 1 ? 1 : $height;
}

sub clamp_scroll {
    my $max = @log_lines - log_height();
    $max = 0 if $max < 0;
    $scroll_offset = $max if $scroll_offset > $max;
    $scroll_offset = 0 if $scroll_offset < 0;
}

sub make_line {
    my ($text, $align) = @_;
    return { text => $text // '', align => $align // 'block' };
}

sub make_rule {
    my ($char) = @_;
    return { rule => $char };
}

sub star_field_row {
    my ($row) = @_;

    my $out = '';
    for my $layer (0 .. $#STAR_LAYERS) {
        my $l = $STAR_LAYERS[$layer];
        my $world = $row - int($scroll_offset * $l->{speed});
        my $hash = md5_hex("stars:$layer:$world");

        for my $i (0 .. 2) {
            my $v = hex(substr($hash, $i * 8, 8));
            next unless ($v % 100) < $l->{density};
            my $col = int($v / 100) % $TERM_COLS + 1;

            my $color = $l->{colors}[hex(substr($hash, 28 + $i, 1)) % @{$l->{colors}}];

            $out .= "\e[${row};${col}H$color$l->{char}$RESET";
        }
    }
    return $out;
}

sub redraw_screen {
    return unless $IS_TTY;

    my $height = log_height();
    my $end    = $#log_lines - $scroll_offset;
    my $start  = $end - $height + 1;

    my $out = '';
    for my $row (1 .. $height) {
        my $idx = $start + $row - 1;
        my $rec = ($idx >= 0 && $idx <= $end) ? $log_lines[$idx] : undef;

        $out .= "\e[${row};1H\e[0m\e[2K";

        if ($rec && $rec->{rule}) {
            $out .= $FRAME . ($rec->{rule} x $TERM_COLS) . $RESET;
            next;
        }

        $out .= star_field_row($row);

        if ($rec && length $rec->{text}) {
            my $width = $rec->{align} eq 'center' ? strip_len($rec->{text}) : $LOG_WIDTH;
            my $col = int(($TERM_COLS - $width) / 2) + 1;
            $col = 1 if $col < 1;
            $out .= "\e[${row};${col}H" . $rec->{text};
        }
    }
    print $out;

    draw_status_bar();
}

sub strip_len {
    my ($text) = @_;
    $text =~ s/\e\[[0-9;]*m//g;
    return length $text;
}

sub bar_content {
    my ($left, $right) = @_;
    $right //= '';

    my $inner = $TERM_COLS - 2;
    my $pad   = $inner - 2 - strip_len($left) - strip_len($right);
    $pad = 1 if $pad < 1;

    return $FRAME . '|' . $RESET . ' ' . $left
         . (' ' x $pad)
         . $right . ' ' . $FRAME . '|' . $RESET;
}

sub draw_status_bar {
    return unless $IS_TTY;

    my $inner = $TERM_COLS - 2;

    my $poll;
    if (defined $last_poll_epoch) {
        my $age = time() - $last_poll_epoch;
        my $age_str = $age < 2  ? 'just now'
                    : $age < 60 ? "${age}s ago"
                    : sprintf('%dm %ds ago', $age / 60, $age % 60);
        my $dot_color = $age <= 3 ? $GOOD : $age <= 10 ? $WARN : $BAD;
        $poll = "$dot_color*$RESET ${LABEL}Hot reload$RESET "
              . "${MUTED}- last poll$RESET $VALUE$last_hot_reload$RESET "
              . "$MUTED($age_str)$RESET";
    }
    else {
        $poll = "${MUTED}o$RESET ${LABEL}Hot reload$RESET "
              . "${MUTED}- waiting for first poll...$RESET";
    }

    my $title  = "${LABEL}OVERPORT DEV SERVER$RESET";
    my $url    = "\e[4m${VALUE}http://$HOST:$PORT/$RESET";
    my $counts = "${MUTED}polls $poll_count | reqs $request_count$RESET";

    my $keys = "${MUTED}Up/Down PgUp/PgDn scroll | Home top | End follow | q quit$RESET";
    my $mode = $scroll_offset > 0
        ? "$WARN^ SCROLLED +$scroll_offset$RESET"
        : "$GOOD>> FOLLOWING$RESET";

    my @rows = (
        $FRAME . '+' . ('-' x $inner) . '+' . $RESET,
        bar_content($title, $url),
        bar_content($poll,  $counts),
        bar_content($keys,  $mode),
        $FRAME . '+' . ('-' x $inner) . '+' . $RESET,
    );

    my $top = $TERM_ROWS - $BAR_HEIGHT + 1;
    my $out = '';
    for my $i (0 .. $#rows) {
        my $row = $top + $i;
        $out .= "\e[${row};1H\e[0m\e[2K" . $rows[$i];
    }
    print $out;
}

sub handle_keys {
    my $buf = '';
    sysread(STDIN, $buf, 256);
    return unless length $buf;

    my $page = log_height() - 1;
    $page = 1 if $page < 1;
    my $before = $scroll_offset;

    while (length $buf) {
        if    ($buf =~ s/^\e\[5~//)              { $scroll_offset += $page; }
        elsif ($buf =~ s/^\e\[6~//)              { $scroll_offset -= $page; }
        elsif ($buf =~ s/^(?:\e\[A|\eOA)//)      { $scroll_offset += 1; }
        elsif ($buf =~ s/^(?:\e\[B|\eOB)//)      { $scroll_offset -= 1; }
        elsif ($buf =~ s/^(?:\e\[H|\e\[1~|\eOH)//) { $scroll_offset = scalar @log_lines; }
        elsif ($buf =~ s/^(?:\e\[F|\e\[4~|\eOF)//) { $scroll_offset = 0; }
        elsif ($buf =~ s/^q//)                   { exit 0; }
        else                                     { substr($buf, 0, 1, ''); }
    }

    clamp_scroll();
    redraw_screen() if $scroll_offset != $before;
}

sub push_log_records {
    my (@records) = @_;

    unless ($IS_TTY) {
        for my $rec (@records) {
            print $rec->{rule}
                ? $FRAME . ($rec->{rule} x $LOG_WIDTH) . $RESET . "\n"
                : $rec->{text} . "\n";
        }
        return;
    }

    push @log_lines, @records;
    $scroll_offset += @records if $scroll_offset > 0;

    if (@log_lines > $MAX_LOG_LINES) {
        splice(@log_lines, 0, @log_lines - $MAX_LOG_LINES);
    }

    clamp_scroll();
    redraw_screen();
}

sub log_output {
    my ($content, $align) = @_;

    my @lines = split(/\n/, $content, -1);
    pop @lines if @lines && $lines[-1] eq '';

    push_log_records(map { make_line($_, $align) } @lines);
}

# ======================
# Request parsing
# ======================
sub parse_request {
    my ($request) = @_;

    if ($request =~ /^([A-Z]+)\s+([^\s]+)\s+HTTP\/1\.[01]\r?\n/) {
        my ($method, $path) = ($1, $2);

        $path = uri_unescape($path);

        return undef if $path =~ /\0/;

        return ($method, $path);
    }
    return;
}

# ======================
# Path sanitization
# ======================
sub path_within_root {
    my ($path) = @_;

    return 0 unless defined $path;
    return 1 if $path eq $REAL_WEB_ROOT;
    return index($path, $ROOT_PREFIX) == 0 ? 1 : 0;
}

sub sanitize_path {
    my ($path) = @_;

    $path = '/' if !defined $path || $path eq '';

    $path =~ s/[?#].*$//;

    $path =~ s{\\}{/}g;
    $path =~ s{/+}{/}g;

    return undef if $path =~ /\.\./;

    my $full_path = File::Spec->catfile($REAL_WEB_ROOT, $path);

    my $real_path = eval { realpath($full_path) };

    if (!$real_path) {
        my @components = split('/', $path);
        my $depth = 0;
        for my $comp (@components) {
            if ($comp eq '..') {
                $depth--;
                return undef if $depth < 0;
            } elsif ($comp ne '.' && $comp ne '') {
                $depth++;
            }
        }

        $real_path = $full_path;
    }

    return undef unless path_within_root($real_path);

    my $relative_path = substr($real_path, length($REAL_WEB_ROOT));
    return undef if $relative_path =~ m{/\.} || $relative_path =~ /^\./;

    if (-d $real_path) {
        return $INDEX_FILE;
    }

    return $real_path;
}

# ======================
# Hot reload
# ======================
sub web_root_signature {
    my @entries;

    find({
        no_chdir => 1,
        wanted   => sub {
            my @st = lstat($_);
            return unless @st;
            push @entries, "$File::Find::name|$st[9]|$st[7]";
        },
    }, $REAL_WEB_ROOT);

    return md5_hex(join("\n", sort @entries));
}

# ======================
# File serving
# ======================
sub write_all {
    my ($client, $data) = @_;

    my $length = length($data);
    my $offset = 0;

    while ($offset < $length) {
        my $written = syswrite($client, $data, $length - $offset, $offset);

        unless (defined $written) {
            next if $! == EINTR;
            return 0;
        }

        last if $written == 0;
        $offset += $written;
    }

    return $offset == $length ? 1 : 0;
}

sub serve_file {
    my ($client, $file_path, $client_ip) = @_;

    return serve_403($client, $client_ip, $file_path) unless path_within_root($file_path);

    unless (-f $file_path && -r _) {
        serve_404($client, $client_ip, $file_path);
        return;
    }

    serve_static($client, $file_path, $client_ip, 200, "OK");
}

sub serve_static {
    my ($client, $file_path, $client_ip, $code, $status) = @_;

    my ($ext) = $file_path =~ /\.([^.]+)$/;
    my $mime_type = $MIME_TYPES{lc($ext // '')} || 'application/octet-stream';

    open(my $fh, '<', $file_path) or do {
        send_response($client, 500, "Internal Server Error", "text/plain", "Cannot open file", $client_ip, $file_path);
        return;
    };
    binmode($fh);

    if ($HOT_RELOAD && $mime_type eq 'text/html') {
        my $body = do { local $/; <$fh> };
        close $fh;

        unless ($body =~ s{</body>}{$HOT_RELOAD_SCRIPT</body>}i) {
            $body .= $HOT_RELOAD_SCRIPT;
        }

        my $headers =
            "HTTP/1.1 $code $status\r\n" .
            "Content-Type: $mime_type\r\n" .
            "Content-Length: " . length($body) . "\r\n" .
            "Cache-Control: no-store\r\n" .
            $SECURITY_HEADERS .
            "Connection: close\r\n\r\n";

        log_packet(
            type       => 'HEADERS',
            client_ip  => $client_ip,
            file_path  => $file_path,
            size       => length($headers),
            mime_type  => $mime_type,
            file_size  => length($body),
            content    => $headers
        );

        return unless write_all($client, $headers);
        write_all($client, $body);
        return;
    }

    my $file_size = -s $fh;
    my $cache_control = $code == 200 ? "public, max-age=3600" : "no-store";

    my $headers =
        "HTTP/1.1 $code $status\r\n" .
        "Content-Type: $mime_type\r\n" .
        "Content-Length: $file_size\r\n" .
        "Cache-Control: $cache_control\r\n" .
        $SECURITY_HEADERS .
        "Connection: close\r\n\r\n";

    log_packet(
        type       => 'HEADERS',
        client_ip  => $client_ip,
        file_path  => $file_path,
        size       => length($headers),
        mime_type  => $mime_type,
        file_size  => $file_size,
        content    => $headers
    );

    unless (write_all($client, $headers)) {
        close $fh;
        return;
    }

    my $sent = 0;
    my $packet_num = 1;

    while (my $read = sysread($fh, my $buffer, $BUFFER_SIZE)) {
        last unless write_all($client, $buffer);
        $sent += $read;

        log_packet(
            type       => 'DATA',
            client_ip  => $client_ip,
            file_path  => $file_path,
            size       => $read,
            packet_num => $packet_num++,
            total_size => $file_size,
            progress   => int(($sent / $file_size) * 100),
            mime_type  => $mime_type
        );
    }

    close $fh;
}

# ======================
# 403 handling
# ======================
sub serve_403 {
    my ($client, $client_ip, $requested_path) = @_;
    send_response($client, 403, "Forbidden", "text/plain", "Access denied", $client_ip, $requested_path);
}

# ======================
# 404 handling
# ======================
sub serve_404 {
    my ($client, $client_ip, $requested_path) = @_;

    my ($ext) = ($requested_path // '') =~ /\.([^.\/]+)$/;
    my $wants_html = defined $ext && lc($ext) =~ /^html?$/;

    if ($wants_html) {
        my $real_404 = eval { realpath($PAGE_404) };
        if ($real_404 && -f $real_404 && -r _) {
            serve_static($client, $real_404, $client_ip, 404, "Not Found");
            return;
        }
    }

    send_response($client, 404, "Not Found", "text/plain", "File not found", $client_ip, $requested_path);
}

# ======================
# Generic responses
# ======================
sub send_response {
    my ($client, $code, $status, $type, $body, $client_ip, $file_path, %opts) = @_;

    my $response =
        "HTTP/1.1 $code $status\r\n" .
        "Content-Type: $type\r\n" .
        "Content-Length: " . length($body) . "\r\n" .
        $SECURITY_HEADERS .
        "Connection: close\r\n\r\n" .
        $body;

    log_packet(
        type       => 'FULL_RESPONSE',
        client_ip  => $client_ip,
        file_path  => $file_path,
        size       => length($response),
        code       => $code,
        status     => $status,
        content    => $response
    ) unless $opts{quiet};

    syswrite($client, $response);
}

# ======================
# Packet logger
# ======================
sub truncate_text {
    my ($text, $max) = @_;
    return $text if length($text) <= $max;
    $max = 3 if $max < 3;
    return substr($text, 0, $max - 3) . '...';
}

sub log_row {
    my ($content) = @_;
    my $pad = $LOG_WIDTH - 4 - strip_len($content);
    $pad = 0 if $pad < 0;
    return "$FRAME|$RESET " . $content . (' ' x $pad) . " $FRAME|$RESET\n";
}

sub field_row {
    my ($label, $value, $color) = @_;
    $color //= $VALUE;

    my $value_max = $LOG_WIDTH - 4 - 12;
    $value = truncate_text("$value", $value_max);

    return log_row($LABEL . sprintf('%-12s', $label) . $RESET . $color . $value . $RESET);
}

sub log_packet {
    my %params = @_;

    my $now = time();
    if ($now - $last_time >= 5) {
        start_stream_banner("STREAM ID: #$stream_counter");
        $stream_counter++;
    }
    $last_time = $now;

    my $timestamp = strftime("%Y-%m-%d %H:%M:%S", localtime);

    my $safe_file_path = $params{file_path} // '';
    $safe_file_path =~ s/\e//g;

    if ($safe_file_path eq $REAL_WEB_ROOT) {
        $safe_file_path = '/';
    }
    elsif (index($safe_file_path, $ROOT_PREFIX) == 0) {
        $safe_file_path = '/' . substr($safe_file_path, length($ROOT_PREFIX));
    }

    my $separator    = '=' x $LOG_WIDTH;
    my $subseparator = '-' x $LOG_WIDTH;

    my $output = '';

    $output .= "\n$FRAME$separator$RESET\n";
    $output .= log_row("${LABEL}PACKET DETAILS ($RESET$VALUE$params{type}$RESET$LABEL) at $RESET$VALUE$timestamp$RESET");
    $output .= "$FRAME$subseparator$RESET\n";

    $output .= field_row('Client:', $params{client_ip});

    if (exists $params{file_path}) {
        if (defined $REAL_PAGE_404 && $safe_file_path eq $REAL_PAGE_404) {
            $output .= field_row('File:', '[404 status page]', $WARN);
        }
        else {
            $output .= field_row('File:', $safe_file_path);
        }
    }

    if (exists $params{code}) {
        my $status_color = $params{code} >= 500 ? $BAD
                         : $params{code} >= 400 ? $WARN
                         : $GOOD;
        $output .= field_row('Status:', "$params{code} $params{status}", $status_color);
    }

    $output .= field_row('MIME Type:', $params{mime_type})
        if exists $params{mime_type};

    $output .= field_row('Size:', "$params{size} bytes");

    $output .= field_row('File Size:', "$params{file_size} bytes")
        if exists $params{file_size};

    $output .= field_row('Packet #:', $params{packet_num})
        if exists $params{packet_num};

    $output .= field_row('Progress:', "$params{progress}%")
        if exists $params{progress};

    $output .= "$FRAME$separator$RESET\n\n";

    log_output($output);
}

END {
    if ($IS_TTY) {
        print "\e[?7h\e[?25h\e[0m\e[?1049l";
        $termios_orig->setattr(fileno(STDIN), TCSANOW) if $termios_orig;
    }
    close $server if $server;
}