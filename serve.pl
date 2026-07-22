#!/usr/bin/perl
use strict;
use warnings;
use Socket;
use File::Basename;
use File::Spec;
use File::Path qw(make_path);
use POSIX qw(strftime :termios_h);
use Errno qw(EINTR);
use Cwd qw(realpath getcwd);
use URI::Escape;
use File::Find;
use Digest::MD5 qw(md5_hex);
use Digest::SHA qw(sha1);
use MIME::Base64 qw(encode_base64);
use Storable qw(nstore retrieve);
use Time::HiRes ();

# ======================
# Configuration
# ======================
my $PORT        = 9001;
my $HOST        = '127.0.0.1';

my $SCRIPT_DIR  = dirname(realpath($0));

my $WEB_ROOT    = $ARGV[0] // File::Spec->catdir(getcwd(), 'src');

my $REAL_WEB_ROOT = realpath($WEB_ROOT);
die "Invalid web root: $WEB_ROOT\n" unless defined $REAL_WEB_ROOT && -d $REAL_WEB_ROOT;

my $ROOT_PREFIX = $REAL_WEB_ROOT =~ m{/$} ? $REAL_WEB_ROOT : $REAL_WEB_ROOT . '/';

my $INDEX_FILE  = File::Spec->catfile($REAL_WEB_ROOT, 'index.html');
my $PAGE_404    = File::Spec->catfile($SCRIPT_DIR, 'status', 'status.html');
my $REAL_PAGE_404 = eval { realpath($PAGE_404) };

my $STATE_HOME = (defined $ENV{XDG_STATE_HOME} && length $ENV{XDG_STATE_HOME})
    ? $ENV{XDG_STATE_HOME}
    : File::Spec->catdir($ENV{HOME} // (getpwuid($<))[7], '.local', 'state');
my $HISTORY_DIR      = File::Spec->catdir($STATE_HOME, 'overport');
my $SETTINGS_FILE    = File::Spec->catfile($HISTORY_DIR, 'settings.pref');
my $BUFFER_SIZE = 8192;
my $MAX_REQUEST_SIZE = 16384;
my $READ_TIMEOUT = 5;
my $SEND_STALL_TIMEOUT = 30;

my $HOT_RELOAD         = 1;
my $HOT_RELOAD_PATH    = '/__hotreload';
my $HOT_RELOAD_POLL_MS = 1000;
my $HOT_RELOAD_MODE    = 'poll';          # 'poll' (client polls) or 'push' (server pushes over a WebSocket)

# ---- WebSocket push mode state ----
my $WS_GUID            = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';   # RFC 6455 handshake magic
my $WS_SCAN_INTERVAL   = 1;               # seconds between web-root scans while clients are connected

my @ws_clients;                           # live WebSocket connections: { fh, ip, buf }
my $last_ws_signature;                    # web-root signature the monitor last observed
my $last_ws_scan_at    = 0;
my $ws_reload_count    = 0;
my $last_ws_reload;                       # human-readable timestamp of the last pushed reload
my $last_ws_reload_epoch;

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
my $BAR_HEIGHT = 7;
my $LOG_WIDTH  = 80;

my $last_hot_reload;
my $last_poll_epoch;
my $poll_count       = 0;
my $request_count    = 0;
my $total_bytes_sent = 0;
my @xfer_window;
my $XFER_WINDOW_SECS = 60;

my $power_watts           = undef;
my $power_source          = undef;
my $last_power_sample_at  = 0;
my $POWER_SAMPLE_INTERVAL = 5;
my $power_ever_ok         = 0;
my $POWER_ROOT_HINT_AFTER = 20;
my $SERVER_START_TIME     = time();
my $power_monitor_enabled = 1;

my $last_rapl_uj;
my $last_rapl_time;

my $stream_counter = 0;
my $last_time      = time() - 5;
my $star_seed      = int(rand(0x7FFFFFFF));
my $history_ready  = 0;

my @log_lines;
my $scroll_offset  = 0;
my $MAX_LOG_LINES  = 2000;
my $termios_orig;
my $tui_active     = 0;

my $target_fps      = 15;
my $last_redraw_at  = 0;
my $redraw_pending  = 0;

my $confirm_open   = 0;
my $confirm_choice = 0;

my $notice_open = 0;
my @notice_text = ();

my $muted       = 0;
my $tone_volume = 1.0;

my $stars_enabled       = 1;
my $star_density_scale  = 1.0;
my $star_colors_enabled = 1;

my $kwh_cost = undef;

my $stress_test_rate     = 10;
my $stress_test_duration = 10;
my $stress_test_running   = 0;
my $stress_test_read_fh;
my $stress_test_child_pid;

my $log_cleanup_enabled = 0;
my $log_max_age         = 3600;

my $settings_open    = 0;
my $settings_index   = 0;
my $settings_editing = 0;
my $settings_edit_buffer = '';
my $settings_flash   = '';

my $MAIN_PID = $$;

my @STAR_LAYERS = (
    {
        speed   => 0.25,
        char    => '.',
        density => 35,
        colors  => ["\e[2;34m", "\e[38;5;60m", "\e[38;5;66m", "\e[38;5;95m"],
        twinkle => "\e[94m",
    },
    {
        speed   => 0.50,
        char    => '+',
        density => 24,
        colors  => ["\e[34m", "\e[38;5;104m", "\e[38;5;130m", "\e[38;5;96m"],
        twinkle => "\e[1;94m",
    },
    {
        speed   => 0.75,
        char    => '*',
        density => 15,
        colors  => ["\e[94m", "\e[38;5;111m", "\e[38;5;208m", "\e[38;5;135m"],
        twinkle => "\e[1;38;5;153m",
    },
);

$SIG{WINCH} = sub {
    ($TERM_ROWS, $TERM_COLS) = terminal_size();
    clamp_scroll();
    request_redraw();
};

# ======================
# Sound synthesis
# ======================

use constant SAMPLE_RATE => 22050;
use constant PI          => 3.14159265358979;

my @PLAYER_CANDIDATES = (
    ['paplay'],
    ['aplay',  '-q', '-'],
    ['play',   '-q', '-t', 'wav', '-'],
);

my %TONE_SPEC = (
    error => [
        { freq => 160, freq_end => 110, duration => 0.11, wave => 'square', volume => 0.20, gap => 0.06 },
        { freq => 160, freq_end => 110, duration => 0.11, wave => 'square', volume => 0.20 },
    ],
    warn => [
        { freq => 420, freq_end => 450, duration => 0.08, wave => 'sine', volume => 0.18, gap => 0.05 },
        { freq => 520, freq_end => 560, duration => 0.10, wave => 'sine', volume => 0.18 },
    ],
    packet => [
        { freq => 480, duration => 0.06, wave => 'sine', volume => 0.13 },
    ],
    stream => [
        { freq => 260, duration => 0.08, wave => 'sine', vibrato_hz => 8, vibrato_depth => 0.02, volume => 0.16, gap => 0.025 },
        { freq => 330, duration => 0.08, wave => 'sine', vibrato_hz => 8, vibrato_depth => 0.02, volume => 0.16, gap => 0.025 },
        { freq => 392, duration => 0.14, wave => 'sine', vibrato_hz => 8, vibrato_depth => 0.02, volume => 0.18 },
    ],
    browser => [
        { freq => 200, freq_end => 520, duration => 0.32, wave => 'sine', vibrato_hz => 10, vibrato_depth => 0.015, volume => 0.18 },
    ],
);

sub detect_audio_player {
    my @dirs = split(':', $ENV{PATH} // '');
    for my $cand (@PLAYER_CANDIDATES) {
        return @$cand if grep { -x "$_/$cand->[0]" } @dirs;
    }
    return ();
}

sub synth_segment {
    my (%o) = @_;
    my $freq0     = $o{freq};
    my $freq1     = $o{freq_end} // $o{freq};
    my $dur       = $o{duration};
    my $wave      = $o{wave} // 'sine';
    my $vib_hz    = $o{vibrato_hz} // 0;
    my $vib_depth = $o{vibrato_depth} // 0;
    my $vol       = ($o{volume} // 0.5) * $tone_volume;

    my $n = int(SAMPLE_RATE * $dur);
    return () if $n < 1;

    my $attack  = int($n * 0.08) || 1;
    my $release = int($n * 0.15) || 1;

    my @samples;
    my $phase = 0;
    for my $i (0 .. $n - 1) {
        my $t    = $i / SAMPLE_RATE;
        my $pos  = $n > 1 ? $i / ($n - 1) : 0;
        my $freq = $freq0 + ($freq1 - $freq0) * $pos;
        $freq += $vib_depth * $freq0 * sin(2 * PI * $vib_hz * $t) if $vib_hz;

        $phase += 2 * PI * $freq / SAMPLE_RATE;

        my $s;
        if ($wave eq 'square') {
            $s = sin($phase) >= 0 ? 1 : -1;
        }
        elsif ($wave eq 'saw') {
            my $cycles = $phase / (2 * PI);
            $s = 2 * ($cycles - int($cycles + 0.5));
        }
        else {
            $s = sin($phase);
        }

        my $env = 1;
        $env = $i / $attack if $i < $attack;
        $env = ($n - 1 - $i) / $release if $i >= $n - $release;
        $env = 0 if $env < 0;
        $env = 1 if $env > 1;

        push @samples, $s * $env * $vol;
    }

    return @samples;
}

sub synth_tone {
    my (@segments) = @_;
    my @samples;
    for my $seg (@segments) {
        push @samples, synth_segment(%$seg);
        push @samples, (0) x int(SAMPLE_RATE * ($seg->{gap} // 0));
    }
    return @samples;
}

sub wav_bytes {
    my (@samples) = @_;

    my $data = join('', map {
        my $v = int($_ * 32767);
        $v = 32767  if $v > 32767;
        $v = -32768 if $v < -32768;
        pack('s<', $v);
    } @samples);

    my $byte_rate = SAMPLE_RATE * 2;
    my $data_len  = length($data);
    my $riff_len  = 36 + $data_len;

    return "RIFF" . pack('V', $riff_len) . "WAVE"
         . "fmt " . pack('V', 16) . pack('v', 1) . pack('v', 1)
         . pack('V', SAMPLE_RATE) . pack('V', $byte_rate)
         . pack('v', 2) . pack('v', 16)
         . "data" . pack('V', $data_len) . $data;
}

my @AUDIO_CMD = detect_audio_player();
my %TONE_WAV;
my %LAST_TONE_AT;
my $TONE_MIN_GAP = 0.15;

sub rebuild_tone_wav {
    %TONE_WAV = map { ($_ => wav_bytes(synth_tone(@{ $TONE_SPEC{$_} }))) } keys %TONE_SPEC;
}

rebuild_tone_wav();

sub drop_root_privileges {
    return unless $> == 0;
    return unless defined $ENV{SUDO_UID} && defined $ENV{SUDO_GID};

    my $uid = $ENV{SUDO_UID} + 0;
    my $gid = $ENV{SUDO_GID} + 0;

    eval {
        POSIX::setgid($gid);
        POSIX::setuid($uid);
    };
    return if $@;

    my @pw = getpwuid($uid);
    if (@pw) {
        $ENV{HOME}    = $pw[7];
        $ENV{USER}    = $pw[0];
        $ENV{LOGNAME} = $pw[0];
    }
    $ENV{XDG_RUNTIME_DIR} = "/run/user/$uid";
}

sub play_tone {
    my ($category) = @_;
    return if $muted || $tone_volume == 0;
    return unless @AUDIO_CMD && $TONE_WAV{$category};

    my $now = time();
    return if defined $LAST_TONE_AT{$category} && ($now - $LAST_TONE_AT{$category}) < $TONE_MIN_GAP;
    $LAST_TONE_AT{$category} = $now;

    my $pid = fork();
    return unless defined $pid;

    if ($pid == 0) {
        my $grandchild = fork();
        POSIX::_exit(0) if !defined $grandchild || $grandchild;

        drop_root_privileges();

        my $devnull = File::Spec->devnull;
        open(STDIN,  '<', $devnull);
        open(STDOUT, '>', $devnull);
        open(STDERR, '>', $devnull);

        open(my $fh, '|-', @AUDIO_CMD) or POSIX::_exit(1);
        binmode($fh);
        print $fh $TONE_WAV{$category};
        close $fh;
        POSIX::_exit(0);
    }

    waitpid($pid, 0);
}

# ======================
# Bandwidth tracking
# ======================

sub record_transfer {
    my ($bytes) = @_;
    return unless $bytes && $bytes > 0;

    $total_bytes_sent += $bytes;
    push @xfer_window, [time(), $bytes];
}

sub bytes_per_window {
    my $cutoff = time() - $XFER_WINDOW_SECS;
    shift @xfer_window while @xfer_window && $xfer_window[0][0] < $cutoff;

    my $sum = 0;
    $sum += $_->[1] for @xfer_window;
    return $sum;
}

sub format_data_size {
    my ($bytes) = @_;
    $bytes = 0 if !defined $bytes || $bytes < 0;

    my $bits = $bytes * 8;
    return $bits == 1 ? '1 bit' : "$bits bits" if $bits < 8;

    my @units = ('B', 'KiB', 'MiB', 'GiB', 'TiB', 'PiB', 'EiB');
    my $value = $bytes;
    my $unit  = shift @units;
    while ($value >= 1024 && @units) {
        $value /= 1024;
        $unit = shift @units;
    }

    return $unit eq 'B' ? "$value $unit" : sprintf('%.2f %s', $value, $unit);
}

# ======================
# Power monitoring
# ======================

sub read_first_line {
    my ($path) = @_;

    open(my $fh, '<', $path) or return undef;
    my $line = <$fh>;
    close $fh;

    return undef unless defined $line;
    chomp $line;
    return $line =~ /^-?\d+$/ ? $line + 0 : undef;
}

sub discover_rapl_domains {
    my $base = '/sys/class/powercap';
    return () unless -d $base;

    opendir(my $dh, $base) or return ();
    my @all = sort grep { /^\w+-rapl:\d+$/ && -r "$base/$_/energy_uj" } readdir($dh);
    closedir($dh);

    return map { "$base/$_/energy_uj" } @all;
}

sub read_rapl_energy {
    my (@paths) = @_;

    my $total = 0;
    my $any;
    for my $path (@paths) {
        my $v = read_first_line($path);
        next unless defined $v;
        $total += $v;
        $any = 1;
    }

    return $any ? $total : undef;
}

sub sample_power_linux_battery {
    for my $bat (glob('/sys/class/power_supply/BAT*')) {
        my $power_uw = read_first_line("$bat/power_now");

        if (!defined $power_uw) {
            my $i = read_first_line("$bat/current_now");
            my $v = read_first_line("$bat/voltage_now");
            $power_uw = $i * $v / 1_000_000 if defined $i && defined $v;
        }

        return $power_uw / 1_000_000 if defined $power_uw && $power_uw > 0;
    }

    return undef;
}

sub sample_power_linux {
    my @domains = discover_rapl_domains();

    if (@domains) {
        my $now_uj = read_rapl_energy(@domains);
        my $now_t  = time();

        my $watts;
        if (defined $now_uj && defined $last_rapl_uj && $now_t > $last_rapl_time) {
            my $delta_uj = $now_uj - $last_rapl_uj;
            $watts = ($delta_uj / 1_000_000) / ($now_t - $last_rapl_time) if $delta_uj > 0;
        }

        $last_rapl_uj   = $now_uj if defined $now_uj;
        $last_rapl_time = $now_t;

        return ($watts, 'RAPL');
    }

    my $batt_watts = sample_power_linux_battery();
    return ($batt_watts, 'battery') if defined $batt_watts;

    return (undef, undef);
}

sub sample_power_darwin {
    my $out = `ioreg -rn AppleSmartBattery -w0 2>/dev/null`;
    return (undef, undef) unless defined $out && length $out;

    my ($amperage) = $out =~ /"(?:InstantAmperage|Amperage)"\s*=\s*(-?\d+)/;
    my ($voltage)  = $out =~ /"Voltage"\s*=\s*(-?\d+)/;
    return (undef, undef) unless defined $amperage && defined $voltage && $voltage > 0;

    $amperage -= 2**64 if $amperage > 2**63;

    my $watts = abs($amperage) * $voltage / 1_000_000;
    return ($watts, 'battery');
}

sub sample_power_windows {
    my $ps = 'Get-CimInstance -Namespace root/wmi -ClassName BatteryStatus -ErrorAction SilentlyContinue '
           . '| Select-Object -First 1 '
           . '| ForEach-Object { if ($_.DischargeRate -gt 0) { $_.DischargeRate } elseif ($_.ChargeRate -gt 0) { $_.ChargeRate } else { 0 } }';

    my $out = `powershell -NoProfile -NonInteractive -Command "$ps" 2>NUL`;
    return (undef, undef) unless defined $out && $out =~ /(\d+)/;

    my $mw = $1;
    return (undef, undef) if $mw == 0;
    return ($mw / 1000, 'WMI');
}

sub sample_power {
    unless ($power_monitor_enabled) {
        $power_watts  = undef;
        $power_source = undef;
        return;
    }

    my $now = time();
    return if $now - $last_power_sample_at < $POWER_SAMPLE_INTERVAL;
    $last_power_sample_at = $now;

    my ($watts, $source) =
        $^O eq 'linux'   ? sample_power_linux()
      : $^O eq 'darwin'  ? sample_power_darwin()
      : $^O eq 'MSWin32' ? sample_power_windows()
      :                    (undef, undef);

    if (defined $source) {
        $power_source = $source;
        if (defined $watts) {
            $power_watts   = $watts;
            $power_ever_ok = 1;
        }
    }
    else {
        $power_source = undef;
        $power_watts  = undef;
    }
}

sub format_cost {
    my ($amount) = @_;
    return sprintf('%.2f', $amount) if $amount >= 0.01;
    return sprintf('%.4f', $amount) if $amount >= 0.0001;
    return sprintf('%.6f', $amount);
}

# ======================
# Stress testing
# ======================

sub collect_web_root_files {
    my @files;

    find({
        no_chdir => 1,
        wanted   => sub {
            return unless -f $_;
            my $rel = substr($File::Find::name, length($REAL_WEB_ROOT));
            $rel = "/$rel" unless $rel =~ m{^/};
            push @files, $rel;
        },
    }, $REAL_WEB_ROOT);

    return @files;
}

sub http_get_ok {
    my ($host, $port, $path) = @_;

    my $ok = eval {
        local $SIG{ALRM} = sub { die "timeout\n" };
        alarm(5);

        socket(my $sock, PF_INET, SOCK_STREAM, getprotobyname('tcp')) or die "socket\n";
        binmode($sock);
        connect($sock, sockaddr_in($port, inet_aton($host))) or die "connect\n";

        my $req = "GET $path HTTP/1.1\r\nHost: $host:$port\r\nConnection: close\r\n\r\n";
        syswrite($sock, $req) or die "write\n";

        my $response = '';
        while (my $bytes = sysread($sock, my $chunk, 65536)) {
            $response .= $chunk;
        }
        close $sock;

        die "bad status\n" unless $response =~ m{^HTTP/1\.[01]\s+(\d\d\d)};
        my $status = $1;
        die "bad status\n" unless $status >= 200 && $status < 300;

        if ($response =~ /\r\n\r\n/) {
            my ($headers, $body) = split(/\r\n\r\n/, $response, 2);
            if ($headers =~ /Content-Length:\s*(\d+)/i) {
                die "truncated\n" unless length($body) == $1;
            }
        }

        1;
    };

    alarm(0);
    return $ok ? 1 : 0;
}

sub run_stress_test {
    return if $stress_test_running;

    my @files = collect_web_root_files();
    unless (@files) {
        show_notice('No files found in the web root to stress test.');
        return;
    }

    pipe(my $read_fh, my $write_fh) or return;

    my $pid = fork();
    return unless defined $pid;

    if ($pid == 0) {
        close $read_fh;

        my $rate     = $stress_test_rate;
        my $duration = $stress_test_duration;
        my $interval = $rate > 0 ? 1 / $rate : 1;

        my $sent     = 0;
        my $ok_count = 0;
        my $deadline = time() + $duration;

        while (time() < $deadline) {
            my $file = $files[int(rand(@files))];
            $sent++;
            $ok_count++ if http_get_ok($HOST, $PORT, $file);
            select(undef, undef, undef, $interval);
        }

        print $write_fh "$sent $ok_count\n";
        close $write_fh;
        POSIX::_exit(0);
    }

    close $write_fh;
    $stress_test_running   = 1;
    $stress_test_read_fh   = $read_fh;
    $stress_test_child_pid = $pid;

    push_log_records(
        make_line(''),
        make_line("${LABEL}Stress test started$RESET ${MUTED}-$RESET $VALUE$stress_test_rate req/s for ${stress_test_duration}s$RESET against $VALUE" . scalar(@files) . " file(s)$RESET", 'center'),
        make_line(''),
    );
}

sub finish_stress_test {
    my $line = <$stress_test_read_fh>;
    close $stress_test_read_fh;
    waitpid($stress_test_child_pid, 0);

    $stress_test_running   = 0;
    $stress_test_read_fh   = undef;
    $stress_test_child_pid = undef;

    my ($sent, $ok_count) = (0, 0);
    ($sent, $ok_count) = ($1, $2) if defined $line && $line =~ /^(\d+)\s+(\d+)/;

    my $passed = $sent > 0 && $ok_count == $sent;
    my $pct    = $sent > 0 ? sprintf('%.1f%%', ($ok_count / $sent) * 100) : '0%';

    push_log_records(
        make_line(''),
        make_line(($passed ? "${GOOD}STRESS TEST PASSED" : "${BAD}STRESS TEST FAILED") . "$RESET", 'center'),
        make_line("${MUTED}$ok_count / $sent requests succeeded ($pct)$RESET", 'center'),
        make_line(''),
    );

    show_notice(
        $passed ? 'Stress test PASSED' : 'Stress test FAILED',
        "$ok_count / $sent requests succeeded ($pct)",
    );
}

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

init_history();
load_settings();
rebuild_tone_wav();
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

while (1) {
    my $rin = '';
    vec($rin, fileno($server), 1) = 1;
    vec($rin, fileno(STDIN), 1) = 1 if $IS_TTY;
    vec($rin, fileno($stress_test_read_fh), 1) = 1 if $stress_test_running && $stress_test_read_fh;
    for my $c (@ws_clients) {
        my $fn = fileno($c->{fh});
        vec($rin, $fn, 1) = 1 if defined $fn;
    }

    my $timeout = $redraw_pending ? redraw_interval() : 1;
    my $rout = $rin;
    my $ready = select($rout, undef, undef, $timeout);
    next if !defined $ready || $ready < 0;

    ws_check_filesystem();

    if ($ready == 0) {
        cleanup_old_logs();
        request_redraw();
        next;
    }

    handle_keys() if $IS_TTY && vec($rout, fileno(STDIN), 1);

    if ($stress_test_running && $stress_test_read_fh && vec($rout, fileno($stress_test_read_fh), 1)) {
        finish_stress_test();
    }

    if (@ws_clients) {
        my @readable = @ws_clients;   # snapshot: ws_handle_readable may prune @ws_clients
        for my $c (@readable) {
            my $fn = fileno($c->{fh});
            next unless defined $fn && vec($rout, $fn, 1);
            ws_handle_readable($c);
        }
    }

    if (vec($rout, fileno($server), 1)) {
        my $client;
        my $client_addr = accept($client, $server) or next;

        my $keep = handle_client($client, $client_addr);

        close $client if $client && !$keep;
    }

    request_redraw() if $redraw_pending;
}

sub handle_client {
    my ($client, $client_addr) = @_;

    my $client_ip = 'unknown';
    my $keep_open = 0;

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
            my $headers = parse_headers($request);

            # WebSocket upgrade (push mode): keep the socket open and register it.
            if (   lc($headers->{connection} // '') =~ /\bupgrade\b/
                && lc($headers->{upgrade}    // '') eq 'websocket'
                && defined $headers->{'sec-websocket-key'}) {

                if (ws_handshake($client, $headers->{'sec-websocket-key'})) {
                    push @ws_clients, { fh => $client, ip => $client_ip, buf => '' };
                    $last_ws_signature = web_root_signature() unless defined $last_ws_signature;
                    $keep_open = 1;
                    log_ws_connect($client_ip);
                }
                return;
            }

            # Poll mode: report the current web-root signature.
            $last_hot_reload = strftime("%Y-%m-%d %H:%M:%S", localtime);
            $last_poll_epoch = time();
            $poll_count++;
            send_response($client, 200, "OK", "text/plain", web_root_signature(), $client_ip, $path, quiet => 1);
            request_redraw();
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

    return $keep_open unless $error;

    if ($error =~ /timeout/) {
        log_output("${WARN}Request timeout from client$RESET\n");
        send_response($client, 408, "Request Timeout", "text/plain", "Timeout", 'unknown', undef);
    }
    else {
        send_response($client, 500, "Internal Server Error", "text/plain", "Internal error", $client_ip, undef);
    }

    return 0;
}

# ======================
# History persistence
# ======================

sub history_file {
    return File::Spec->catfile($HISTORY_DIR, md5_hex($REAL_WEB_ROOT) . '.hist');
}

sub init_history {
    make_path($HISTORY_DIR) unless -d $HISTORY_DIR;
    load_history();
    $history_ready = 1;
}

sub load_history {
    my $file = history_file();
    return unless -f $file;

    my $data = eval { retrieve($file) };
    return unless $data && ref $data eq 'HASH';

    @log_lines       = @{ $data->{log_lines} // [] };
    $stream_counter  = $data->{stream_counter}  // 0;
    $last_time       = $data->{last_time}       // (time() - 5);
    $last_hot_reload = $data->{last_hot_reload};
    $last_poll_epoch = $data->{last_poll_epoch};
    $poll_count       = $data->{poll_count}       // 0;
    $request_count    = $data->{request_count}    // 0;
    $total_bytes_sent = $data->{total_bytes_sent} // 0;
    $star_seed        = $data->{star_seed} if defined $data->{star_seed};

    if (@log_lines > $MAX_LOG_LINES) {
        splice(@log_lines, 0, @log_lines - $MAX_LOG_LINES);
    }
}

sub save_history {
    return unless $history_ready && defined $REAL_WEB_ROOT;

    make_path($HISTORY_DIR) unless -d $HISTORY_DIR;

    eval {
        nstore({
            log_lines       => [@log_lines],
            stream_counter  => $stream_counter,
            last_time       => $last_time,
            last_hot_reload => $last_hot_reload,
            last_poll_epoch => $last_poll_epoch,
            poll_count       => $poll_count,
            request_count    => $request_count,
            total_bytes_sent => $total_bytes_sent,
            star_seed        => $star_seed,
        }, history_file());
    };
}

sub clear_history {
    @log_lines       = ();
    $scroll_offset   = 0;
    $stream_counter  = 0;
    $last_time       = time() - 5;
    $last_hot_reload = undef;
    $last_poll_epoch = undef;
    $poll_count       = 0;
    $request_count    = 0;
    $total_bytes_sent = 0;
    @xfer_window      = ();
    $star_seed        = int(rand(0x7FFFFFFF));

    unlink history_file();

    push_log_records(make_line("${WARN}History cleared. Stream numbering restarts at #0.$RESET", 'center'));
}

# ======================
# Settings persistence
# ======================

sub load_settings {
    return unless -f $SETTINGS_FILE;

    my $data = eval { retrieve($SETTINGS_FILE) };
    return unless $data && ref $data eq 'HASH';

    $HOT_RELOAD             = $data->{hot_reload}            if defined $data->{hot_reload};
    $HOT_RELOAD_MODE        = ($data->{hot_reload_mode} eq 'push' ? 'push' : 'poll') if defined $data->{hot_reload_mode};
    $power_monitor_enabled  = $data->{power_monitor_enabled} if defined $data->{power_monitor_enabled};
    $POWER_SAMPLE_INTERVAL  = $data->{power_sample_interval} if defined $data->{power_sample_interval};
    $XFER_WINDOW_SECS       = $data->{xfer_window_secs}      if defined $data->{xfer_window_secs};
    $muted                  = $data->{muted}                 if defined $data->{muted};
    $kwh_cost               = $data->{kwh_cost}               if exists $data->{kwh_cost};
    $tone_volume            = $data->{tone_volume}            if defined $data->{tone_volume};
    $stars_enabled          = $data->{stars_enabled}          if defined $data->{stars_enabled};
    $star_density_scale     = $data->{star_density_scale}     if defined $data->{star_density_scale};
    $star_colors_enabled    = $data->{star_colors_enabled}    if defined $data->{star_colors_enabled};
    $stress_test_rate       = $data->{stress_test_rate}       if defined $data->{stress_test_rate};
    $stress_test_duration   = $data->{stress_test_duration}   if defined $data->{stress_test_duration};
    $log_cleanup_enabled    = $data->{log_cleanup_enabled}    if defined $data->{log_cleanup_enabled};
    $log_max_age            = $data->{log_max_age}            if defined $data->{log_max_age};
    $target_fps             = $data->{target_fps}             if defined $data->{target_fps};
}

sub save_settings {
    make_path($HISTORY_DIR) unless -d $HISTORY_DIR;

    eval {
        nstore({
            hot_reload             => $HOT_RELOAD,
            hot_reload_mode        => $HOT_RELOAD_MODE,
            power_monitor_enabled  => $power_monitor_enabled,
            power_sample_interval  => $POWER_SAMPLE_INTERVAL,
            xfer_window_secs       => $XFER_WINDOW_SECS,
            muted                  => $muted,
            kwh_cost                => $kwh_cost,
            tone_volume             => $tone_volume,
            stars_enabled           => $stars_enabled,
            star_density_scale      => $star_density_scale,
            star_colors_enabled     => $star_colors_enabled,
            stress_test_rate        => $stress_test_rate,
            stress_test_duration    => $stress_test_duration,
            log_cleanup_enabled     => $log_cleanup_enabled,
            log_max_age             => $log_max_age,
            target_fps              => $target_fps,
        }, $SETTINGS_FILE);
    };
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

    play_tone('stream');
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

    $tui_active = 1;
    print "\e[?1049h\e[?25l\e[?7l\e[2J";
    request_redraw();
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
    return '' unless $stars_enabled;

    my $out = '';
    for my $layer (0 .. $#STAR_LAYERS) {
        my $l = $STAR_LAYERS[$layer];
        my $world = $row - int($scroll_offset * $l->{speed});
        my $hash = md5_hex("stars:$star_seed:$layer:$world");

        for my $i (0 .. 2) {
            my $v = hex(substr($hash, $i * 8, 8));
            next unless ($v % 100) < ($l->{density} * $star_density_scale);
            my $col = int($v / 100) % $TERM_COLS + 1;

            my $color = $star_colors_enabled
                ? $l->{colors}[hex(substr($hash, 28 + $i, 1)) % @{$l->{colors}}]
                : $MUTED;

            my $phase  = $v % 7;
            my $bucket = int((time() + $phase) / 3);
            my $flare  = hex(substr(md5_hex("twinkle:$star_seed:$layer:$world:$i:$bucket"), 0, 8)) % 100;
            $color = $star_colors_enabled ? $l->{twinkle} : $VALUE if $flare < 6;

            $out .= "\e[${row};${col}H$color$l->{char}$RESET";
        }
    }
    return $out;
}

sub redraw_screen {
    return unless $IS_TTY;

    my $modal_open = $confirm_open || $notice_open || $settings_open;

    my $height = log_height();
    my $end    = $#log_lines - $scroll_offset;
    my $start  = $end - $height + 1;

    my $out = '';
    for my $row (1 .. $height) {
        $out .= "\e[${row};1H\e[0m\e[2K";

        next if $modal_open;

        my $idx = $start + $row - 1;
        my $rec = ($idx >= 0 && $idx <= $end) ? $log_lines[$idx] : undef;

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

    $out .= draw_status_bar();
    $out .= draw_confirm_box();
    $out .= draw_notice_box();
    $out .= draw_settings_box();

    atomic_print($out);

    $last_redraw_at = Time::HiRes::time();
    $redraw_pending  = 0;
}

sub atomic_print {
    my ($content) = @_;
    print "\e[?2026h${content}\e[?2026l";
}

sub redraw_interval {
    my $fps = $target_fps > 0 ? $target_fps : 1;
    return 1 / $fps;
}

sub request_redraw {
    return unless $IS_TTY;

    if (Time::HiRes::time() - $last_redraw_at >= redraw_interval()) {
        redraw_screen();
    }
    else {
        $redraw_pending = 1;
    }
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

sub relative_age {
    my ($age) = @_;
    return $age < 2  ? 'just now'
         : $age < 60 ? "${age}s ago"
         :             sprintf('%dm %ds ago', $age / 60, $age % 60);
}

sub draw_status_bar {
    return '' unless $IS_TTY;

    sample_power();

    my $inner = $TERM_COLS - 2;

    my $poll;
    if ($HOT_RELOAD_MODE eq 'push') {
        my $n       = scalar @ws_clients;
        my $dot     = $n > 0 ? "$GOOD*$RESET" : "${MUTED}o$RESET";
        my $clients = "$VALUE$n$RESET ${MUTED}client" . ($n == 1 ? '' : 's') . "$RESET";
        if (defined $last_ws_reload_epoch) {
            my $age_str = relative_age(time() - $last_ws_reload_epoch);
            $poll = "$dot ${LABEL}Hot reload$RESET ${MUTED}(WS)$RESET $clients "
                  . "${MUTED}- last push$RESET $VALUE$last_ws_reload$RESET "
                  . "$MUTED($age_str)$RESET";
        }
        else {
            $poll = "$dot ${LABEL}Hot reload$RESET ${MUTED}(WS)$RESET $clients "
                  . "${MUTED}- watching for changes$RESET";
        }
    }
    elsif (defined $last_poll_epoch) {
        my $age = time() - $last_poll_epoch;
        my $dot_color = $age <= 3 ? $GOOD : $age <= 10 ? $WARN : $BAD;
        $poll = "$dot_color*$RESET ${LABEL}Hot reload$RESET "
              . "${MUTED}- last poll$RESET $VALUE$last_hot_reload$RESET "
              . "$MUTED(" . relative_age($age) . ")$RESET";
    }
    else {
        $poll = "${MUTED}o$RESET ${LABEL}Hot reload$RESET "
              . "${MUTED}- waiting for first poll...$RESET";
    }

    my $title  = "${LABEL}OVERPORT DEV SERVER$RESET";
    my $url    = "\e[4m${VALUE}http://$HOST:$PORT/$RESET";
    my $counts = $HOT_RELOAD_MODE eq 'push'
        ? "${MUTED}pushes $ws_reload_count | reqs $request_count$RESET"
        : "${MUTED}polls $poll_count | reqs $request_count$RESET";

    my $xfer_rate  = "${LABEL}Transfer$RESET ${MUTED}-$RESET $VALUE" . format_data_size(bytes_per_window()) . "/min$RESET";
    my $xfer_total = "${LABEL}Total sent$RESET ${MUTED}-$RESET $VALUE" . format_data_size($total_bytes_sent) . "$RESET";

    my $power_value;
    if (!$power_monitor_enabled) {
        $power_value = "${MUTED}Disabled$RESET";
    }
    elsif (defined $power_watts) {
        $power_value = "$VALUE" . sprintf('%.1f W', $power_watts) . "$RESET";
    }
    else {
        my $stuck = !$power_ever_ok && (time() - $SERVER_START_TIME) >= $POWER_ROOT_HINT_AFTER;
        $power_value = "${MUTED}N/A$RESET" . ($stuck ? " ${WARN}(try running as root)$RESET" : '');
    }
    my $power = "${LABEL}Power draw$RESET ${MUTED}-$RESET $power_value";
    my $power_meta = defined $power_source ? "${MUTED}via $power_source$RESET" : '';
    if (defined $power_watts && defined $kwh_cost) {
        my $cost_per_hr = ($power_watts / 1000) * $kwh_cost;
        $power_meta .= ($power_meta ne '' ? '  ' : '') . "${MUTED}~\$" . format_cost($cost_per_hr) . "/hr$RESET";
    }

    my $keys = "${MUTED}Scroll: Up/Dn PgUp/PgDn Home End | o open | c clear | m mute | s settings | t stress | q quit$RESET";
    my $mode = $scroll_offset > 0
        ? "$WARN^ SCROLLED +$scroll_offset$RESET"
        : "$GOOD>> FOLLOWING$RESET";
    $mode .= '  ' . (($muted || $tone_volume == 0) ? "$MUTED- muted$RESET" : "$GOOD- sound$RESET");

    my @rows = (
        $FRAME . '+' . ('-' x $inner) . '+' . $RESET,
        bar_content($title, $url),
        bar_content($poll,  $counts),
        bar_content($xfer_rate, $xfer_total),
        bar_content($power, $power_meta),
        bar_content($keys,  $mode),
        $FRAME . '+' . ('-' x $inner) . '+' . $RESET,
    );

    my $top = $TERM_ROWS - $BAR_HEIGHT + 1;
    my $out = '';
    for my $i (0 .. $#rows) {
        my $row = $top + $i;
        $out .= "\e[${row};1H\e[0m\e[2K" . $rows[$i];
    }
    return $out;
}

sub box_row {
    my ($content, $inner) = @_;

    my $vis  = strip_len($content);
    my $padl = int(($inner - $vis) / 2);
    $padl = 0 if $padl < 0;
    my $padr = $inner - $vis - $padl;
    $padr = 0 if $padr < 0;

    return "$WARN|$RESET" . (' ' x $padl) . $content . (' ' x $padr) . "$WARN|$RESET";
}

sub draw_confirm_box {
    return '' unless $IS_TTY && $confirm_open;

    my $w = 50;
    $w = $TERM_COLS if $w > $TERM_COLS;
    my $inner = $w - 2;

    my $left = int(($TERM_COLS - $w) / 2) + 1;
    $left = 1 if $left < 1;

    my $yes = $confirm_choice == 1 ? "$WARN\e[7m [ Yes ] $RESET" : "$MUTED [ Yes ] $RESET";
    my $no  = $confirm_choice == 0 ? "$GOOD\e[7m [ No ] $RESET"  : "$MUTED [ No ] $RESET";

    my $border = $WARN . '+' . ('-' x $inner) . '+' . $RESET;
    my @lines = (
        $border,
        box_row('', $inner),
        box_row("${VALUE}Clear saved history for this web root?$RESET", $inner),
        box_row("${MUTED}Stream numbering will restart at #0.$RESET", $inner),
        box_row('', $inner),
        box_row($yes . '    ' . $no, $inner),
        box_row('', $inner),
        $border,
    );

    my $top = int((log_height() - scalar @lines) / 2) + 1;
    $top = 1 if $top < 1;

    my $out = '';
    for my $i (0 .. $#lines) {
        my $row = $top + $i;
        $out .= "\e[${row};${left}H\e[0m" . $lines[$i];
    }
    return $out;
}

sub draw_notice_box {
    return '' unless $IS_TTY && $notice_open;

    my $w = 60;
    $w = $TERM_COLS if $w > $TERM_COLS;
    my $inner = $w - 2;

    my $left = int(($TERM_COLS - $w) / 2) + 1;
    $left = 1 if $left < 1;

    my $border = $WARN . '+' . ('-' x $inner) . '+' . $RESET;
    my @lines = ($border, box_row('', $inner));
    push @lines, box_row("${VALUE}$_$RESET", $inner) for @notice_text;
    push @lines, box_row('', $inner);
    push @lines, box_row("${MUTED}Press any key to dismiss$RESET", $inner);
    push @lines, box_row('', $inner);
    push @lines, $border;

    my $top = int((log_height() - scalar @lines) / 2) + 1;
    $top = 1 if $top < 1;

    my $out = '';
    for my $i (0 .. $#lines) {
        my $row = $top + $i;
        $out .= "\e[${row};${left}H\e[0m" . $lines[$i];
    }
    return $out;
}

sub show_notice {
    my (@lines) = @_;
    @notice_text = @lines;
    $notice_open = 1;
    request_redraw();
}

sub handle_notice_keys {
    $notice_open = 0;
    request_redraw();
}

sub handle_confirm_keys {
    my ($buf) = @_;

    while (length $buf) {
        if ($buf =~ s/^(?:\e\[[ABCD]|\eO[ABCD])//) {
            $confirm_choice = 1 - $confirm_choice;
            request_redraw();
        }
        elsif ($buf =~ s/^[\r\n]//) {
            my $confirmed = $confirm_choice == 1;
            $confirm_open = 0;
            if ($confirmed) {
                clear_history();
            }
            else {
                request_redraw();
            }
            return;
        }
        elsif ($buf =~ s/^\e//) {
            $confirm_open = 0;
            request_redraw();
            return;
        }
        else {
            substr($buf, 0, 1, '');
        }
    }
}

sub cycle_value {
    my ($current, $direction, @steps) = @_;
    for my $i (0 .. $#steps) {
        if ($steps[$i] == $current) {
            return $steps[($i + $direction + @steps) % @steps];
        }
    }
    return $steps[0];
}

sub humanize_duration {
    my ($secs) = @_;
    my $YEAR = 365 * 86400;

    return "${secs}s" if $secs < 60;

    my $mins = $secs / 60;
    return sprintf('%dm', $mins) if $secs < 3600;

    my $hours = $secs / 3600;
    return sprintf('%dh', $hours) if $secs < 86400;

    my $days = $secs / 86400;
    return sprintf('%dd', $days) if $secs < $YEAR;

    my $years = $secs / $YEAR;
    return sprintf('%dy', $years) if $secs < 10 * $YEAR;

    my $decades = $secs / (10 * $YEAR);
    return sprintf('%d decade%s', $decades, $decades == 1 ? '' : 's') if $secs < 100 * $YEAR;

    my $centuries = $secs / (100 * $YEAR);
    return sprintf('%d centur%s', $centuries, $centuries == 1 ? 'y' : 'ies') if $secs < 1000 * $YEAR;

    my $millennia = $secs / (1000 * $YEAR);
    return sprintf('%d millenni%s', $millennia, $millennia == 1 ? 'um' : 'a');
}

sub settings_list {
    return (
        {
            category => 'Development',
            label    => 'Hot reload',
            render   => sub { $HOT_RELOAD ? 'Enabled' : 'Disabled' },
            toggle   => sub { $HOT_RELOAD = $HOT_RELOAD ? 0 : 1; },
        },
        {
            category => 'Development',
            label    => 'Hot reload mode',
            render   => sub { $HOT_RELOAD_MODE eq 'push' ? 'WebSocket (push)' : 'Poll (fetch)' },
            toggle   => sub {
                $HOT_RELOAD_MODE = $HOT_RELOAD_MODE eq 'push' ? 'poll' : 'push';
                $settings_flash  = 'Refresh open pages to apply the new mode.';
            },
        },
        {
            category => 'Development',
            label    => 'Stress test rate',
            render   => sub { "$stress_test_rate req/s" },
            toggle   => sub {
                my ($dir) = @_;
                $stress_test_rate = cycle_value($stress_test_rate, $dir, 1, 5, 10, 25, 50, 100, 200);
            },
        },
        {
            category => 'Development',
            label    => 'Stress test duration',
            render   => sub { humanize_duration($stress_test_duration) },
            toggle   => sub {
                my ($dir) = @_;
                $stress_test_duration = cycle_value($stress_test_duration, $dir, 5, 10, 30, 60, 120, 300);
            },
        },
        {
            category => 'Development',
            label    => 'Auto log cleanup',
            render   => sub { $log_cleanup_enabled ? 'Enabled' : 'Disabled' },
            toggle   => sub { $log_cleanup_enabled = $log_cleanup_enabled ? 0 : 1; },
        },
        {
            category => 'Development',
            label    => 'Log max age',
            render   => sub { humanize_duration($log_max_age) },
            toggle   => sub {
                my ($dir) = @_;
                $log_max_age = cycle_value(
                    $log_max_age, $dir,
                    300, 900, 1800, 3600, 21600, 43200,
                    86400, 259200, 604800, 2592000, 7776000, 31536000,
                    63072000, 126144000, 157680000,
                    315360000, 3153600000, 31536000000,
                );
            },
        },

        {
            category => 'Estimations',
            label    => 'Power monitor',
            render   => sub { $power_monitor_enabled ? 'Enabled' : 'Disabled' },
            toggle   => sub {
                $power_monitor_enabled = $power_monitor_enabled ? 0 : 1;
                unless ($power_monitor_enabled) {
                    $power_watts  = undef;
                    $power_source = undef;
                }
            },
        },
        {
            category => 'Estimations',
            label    => 'Power sample rate',
            render   => sub { "every ${POWER_SAMPLE_INTERVAL}s" },
            toggle   => sub {
                my ($dir) = @_;
                $POWER_SAMPLE_INTERVAL = cycle_value($POWER_SAMPLE_INTERVAL, $dir, 2, 5, 10, 30, 60);
            },
        },
        {
            category => 'Estimations',
            label    => 'Bandwidth window',
            render   => sub { "${XFER_WINDOW_SECS}s" },
            toggle   => sub {
                my ($dir) = @_;
                $XFER_WINDOW_SECS = cycle_value($XFER_WINDOW_SECS, $dir, 15, 30, 60, 120, 300);
            },
        },
        {
            category  => 'Estimations',
            label     => 'Cost per kWh',
            type      => 'text',
            render    => sub { defined $kwh_cost ? sprintf('$%.4f', $kwh_cost) : 'not set' },
            edit_init => sub { defined $kwh_cost ? sprintf('%.4f', $kwh_cost) : '' },
            commit    => sub {
                my ($text) = @_;
                if ($text eq '') {
                    $kwh_cost = undef;
                }
                elsif ($text =~ /^\d*\.?\d+$/) {
                    $kwh_cost = $text + 0;
                }
            },
        },

        {
            category => 'Cosmetics',
            label    => 'Sound',
            render   => sub { $muted ? 'Muted' : 'Enabled' },
            toggle   => sub { $muted = $muted ? 0 : 1; },
        },
        {
            category => 'Cosmetics',
            label    => 'Tone volume',
            render   => sub { sprintf('%d%%', int($tone_volume * 100 + 0.5)) },
            toggle   => sub {
                my ($dir) = @_;
                $tone_volume = cycle_value($tone_volume, $dir, 0, 0.25, 0.5, 0.75, 1, 1.25, 1.5);
                rebuild_tone_wav();
            },
        },
        {
            category => 'Cosmetics',
            label    => 'Stars',
            render   => sub { $stars_enabled ? 'Enabled' : 'Disabled' },
            toggle   => sub { $stars_enabled = $stars_enabled ? 0 : 1; },
        },
        {
            category => 'Cosmetics',
            label    => 'Star frequency',
            render   => sub { sprintf('%d%%', int($star_density_scale * 100 + 0.5)) },
            toggle   => sub {
                my ($dir) = @_;
                $star_density_scale = cycle_value($star_density_scale, $dir, 0.25, 0.5, 1, 1.5, 2);
            },
        },
        {
            category => 'Cosmetics',
            label    => 'Star colors',
            render   => sub { $star_colors_enabled ? 'Colored' : 'Monochrome' },
            toggle   => sub { $star_colors_enabled = $star_colors_enabled ? 0 : 1; },
        },
        {
            category => 'Cosmetics',
            label    => 'Frame rate',
            render   => sub { "$target_fps fps" },
            toggle   => sub {
                my ($dir) = @_;
                $target_fps = cycle_value($target_fps, $dir, 1, 2, 5, 10, 15, 20, 30, 60);
            },
        },
    );
}

sub draw_settings_box {
    return '' unless $IS_TTY && $settings_open;

    my @settings = settings_list();

    my $w = 56;
    $w = $TERM_COLS if $w > $TERM_COLS;
    my $inner = $w - 2;

    my $left = int(($TERM_COLS - $w) / 2) + 1;
    $left = 1 if $left < 1;

    my $border = $WARN . '+' . ('-' x $inner) . '+' . $RESET;
    my @lines = (
        $border,
        box_row("${LABEL}SETTINGS$RESET", $inner),
        $border,
    );

    my @values;
    my $label_width = 0;
    my $value_width = 0;
    for my $i (0 .. $#settings) {
        my $value = $settings[$i]{render}->();
        if ($settings_editing && $i == $settings_index) {
            $value = "$settings_edit_buffer" . '_';
        }
        $values[$i] = $value;

        $label_width = length($settings[$i]{label}) if length($settings[$i]{label}) > $label_width;
        $value_width = length($value) if length($value) > $value_width;
    }

    my $category = '';
    for my $i (0 .. $#settings) {
        my $s = $settings[$i];

        if ($s->{category} ne $category) {
            $category = $s->{category};
            push @lines, box_row('', $inner) if $i > 0;
            push @lines, box_row("${MUTED}-- $category --$RESET", $inner);
        }

        my $label = sprintf('%-*s', $label_width, $s->{label});
        my $value = sprintf('%*s', $value_width, $values[$i]);

        my $row_content = $i == $settings_index
            ? "$WARN\e[7m $label  $value $RESET"
            : " ${LABEL}$label$RESET  ${VALUE}$value$RESET ";

        push @lines, box_row($row_content, $inner);
    }

    if (length $settings_flash) {
        push @lines, box_row('', $inner);
        push @lines, box_row("$WARN! $settings_flash$RESET", $inner);
    }

    push @lines, $border;
    if ($settings_editing) {
        push @lines, box_row("${MUTED}Type digits and '.' | Backspace delete$RESET", $inner);
        push @lines, box_row("${MUTED}Enter confirm | Esc cancel$RESET", $inner);
    }
    else {
        push @lines, box_row("${MUTED}Up/Dn select | Left back | Right/Space forward$RESET", $inner);
        push @lines, box_row("${MUTED}s or Esc to close$RESET", $inner);
    }
    push @lines, $border;

    my $top = int((log_height() - scalar @lines) / 2) + 1;
    $top = 1 if $top < 1;

    my $out = '';
    for my $i (0 .. $#lines) {
        my $row = $top + $i;
        $out .= "\e[${row};${left}H\e[0m" . $lines[$i];
    }
    return $out;
}

sub handle_settings_keys {
    my ($buf) = @_;

    return handle_settings_edit_keys($buf) if $settings_editing;

    my @settings = settings_list();

    while (length $buf) {
        if ($buf =~ s/^(?:\e\[A|\eOA)//) {
            $settings_index = ($settings_index - 1 + @settings) % @settings;
            request_redraw();
        }
        elsif ($buf =~ s/^(?:\e\[B|\eOB)//) {
            $settings_index = ($settings_index + 1) % @settings;
            request_redraw();
        }
        elsif ($buf =~ s/^(?:\e\[D|\eOD)//) {
            my $s = $settings[$settings_index];
            if (($s->{type} // '') ne 'text') {
                $s->{toggle}->(-1);
                save_settings();
                request_redraw();
            }
        }
        elsif ($buf =~ s/^(?:\e\[C|\eOC| )//) {
            my $s = $settings[$settings_index];
            if (($s->{type} // '') eq 'text') {
                $settings_edit_buffer = $s->{edit_init}->();
                $settings_editing     = 1;
                request_redraw();
            }
            else {
                $s->{toggle}->(1);
                save_settings();
                request_redraw();
            }
        }
        elsif ($buf =~ s/^[\r\n]//) {
            my $s = $settings[$settings_index];
            if (($s->{type} // '') eq 'text') {
                $settings_edit_buffer = $s->{edit_init}->();
                $settings_editing     = 1;
                request_redraw();
            }
        }
        elsif ($buf =~ s/^[sS\e]//) {
            $settings_open  = 0;
            $settings_flash = '';
            request_redraw();
            return;
        }
        else {
            substr($buf, 0, 1, '');
        }
    }
}

sub handle_settings_edit_keys {
    my ($buf) = @_;
    my @settings = settings_list();
    my $s        = $settings[$settings_index];

    while (length $buf) {
        if ($buf =~ s/^([0-9.])//) {
            $settings_edit_buffer .= $1 unless $1 eq '.' && index($settings_edit_buffer, '.') >= 0;
            request_redraw();
        }
        elsif ($buf =~ s/^(?:\x7f|\x08)//) {
            substr($settings_edit_buffer, -1, 1, '') if length $settings_edit_buffer;
            request_redraw();
        }
        elsif ($buf =~ s/^[\r\n]//) {
            $s->{commit}->($settings_edit_buffer);
            $settings_editing = 0;
            save_settings();
            request_redraw();
        }
        elsif ($buf =~ s/^\e//) {
            $settings_editing = 0;
            request_redraw();
        }
        else {
            substr($buf, 0, 1, '');
        }
    }
}

sub browser_launch_command {
    my ($url) = @_;

    return ($ENV{BROWSER}, $url) if $ENV{BROWSER};

    if ($^O eq 'darwin') {
        return ('open', $url);
    }
    elsif ($^O eq 'MSWin32') {
        return ('cmd', '/c', 'start', '""', $url);
    }
    elsif ($^O eq 'linux') {
        return ('xdg-open', $url);
    }

    return ();
}

sub open_browser {
    my $url = "http://$HOST:$PORT/";
    my @launcher = browser_launch_command($url);

    unless (@launcher) {
        my @message = (
            "Automatic browser launch isn't supported on this OS ($^O).",
            "Open $url manually in your browser.",
        );
        if ($IS_TTY) {
            show_notice(@message);
        }
        else {
            push_log_records(make_line("$WARN$_$RESET", 'center')) for @message;
        }
        return;
    }

    my $pid = fork();
    return unless defined $pid;

    if ($pid == 0) {
        my $grandchild = fork();
        POSIX::_exit(0) if !defined $grandchild || $grandchild;

        drop_root_privileges();

        my $devnull = File::Spec->devnull;
        open(STDIN,  '<', $devnull);
        open(STDOUT, '>', $devnull);
        open(STDERR, '>', $devnull);

        { no warnings 'exec'; exec(@launcher); }
        POSIX::_exit(1);
    }

    waitpid($pid, 0);

    log_output(browser_opened_banner($url), 'center');
    play_tone('browser');
}

sub handle_keys {
    my $buf = '';
    sysread(STDIN, $buf, 256);
    return unless length $buf;

    return handle_notice_keys() if $notice_open;
    return handle_confirm_keys($buf) if $confirm_open;
    return handle_settings_keys($buf) if $settings_open;

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
        elsif ($buf =~ s/^o//) {
            open_browser();
        }
        elsif ($buf =~ s/^c//) {
            $confirm_open   = 1;
            $confirm_choice = 0;
            request_redraw();
            return;
        }
        elsif ($buf =~ s/^[mM]//) {
            $muted = !$muted;
            save_settings();
            request_redraw();
        }
        elsif ($buf =~ s/^[sS]//) {
            $settings_open  = 1;
            $settings_index = 0;
            $settings_flash = '';
            request_redraw();
            return;
        }
        elsif ($buf =~ s/^[tT]//) {
            run_stress_test();
        }
        elsif ($buf =~ s/^q//)                   { exit 0; }
        else                                     { substr($buf, 0, 1, ''); }
    }

    clamp_scroll();
    request_redraw() if $scroll_offset != $before;
}

sub cleanup_old_logs {
    return unless $log_cleanup_enabled;

    my $cutoff  = time() - $log_max_age;
    my $removed = 0;

    while (@log_lines && ($log_lines[0]{time} // 0) < $cutoff) {
        shift @log_lines;
        $removed++;
    }

    clamp_scroll() if $removed;
}

sub push_log_records {
    my (@records) = @_;

    my $now = time();
    $_->{time} = $now for @records;

    push @log_lines, @records;
    $scroll_offset += @records if $scroll_offset > 0;

    if (@log_lines > $MAX_LOG_LINES) {
        splice(@log_lines, 0, @log_lines - $MAX_LOG_LINES);
    }

    cleanup_old_logs();

    unless ($IS_TTY) {
        for my $rec (@records) {
            print $rec->{rule}
                ? $FRAME . ($rec->{rule} x $LOG_WIDTH) . $RESET . "\n"
                : $rec->{text} . "\n";
        }
        return;
    }

    clamp_scroll();
    request_redraw();
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

# The snippet injected before </body>. In poll mode the browser drives the
# check by fetching the signature; in push mode it opens a WebSocket and waits
# for the server to tell it when to reload.
sub hot_reload_script {
    if ($HOT_RELOAD_MODE eq 'push') {
        return <<"END_WS";
<script>
(function () {
    var proto = location.protocol === 'https:' ? 'wss://' : 'ws://';
    var url = proto + location.host + '$HOT_RELOAD_PATH';
    function connect() {
        var ws;
        try { ws = new WebSocket(url); }
        catch (e) { setTimeout(connect, $HOT_RELOAD_POLL_MS); return; }
        ws.onmessage = function (ev) {
            if (ev.data === 'reload') location.reload();
        };
        ws.onclose = function () { setTimeout(connect, $HOT_RELOAD_POLL_MS); };
        ws.onerror = function () { try { ws.close(); } catch (e) {} };
    }
    connect();
})();
</script>
END_WS
    }

    return <<"END_POLL";
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
END_POLL
}

# ======================
# WebSocket push transport (RFC 6455, subset)
# ======================

# Split a raw HTTP request into a lowercased-name => value header hash.
sub parse_headers {
    my ($request) = @_;

    my %h;
    my @lines = split(/\r?\n/, $request);
    shift @lines;   # drop the request line

    for my $line (@lines) {
        last if $line eq '';
        if ($line =~ /^([^:]+):\s*(.*?)\s*$/) {
            $h{lc $1} = $2;
        }
    }

    return \%h;
}

# Complete the opening handshake. Returns 1 on success.
sub ws_handshake {
    my ($client, $key) = @_;

    my $accept = encode_base64(sha1($key . $WS_GUID), '');

    my $response =
        "HTTP/1.1 101 Switching Protocols\r\n" .
        "Upgrade: websocket\r\n" .
        "Connection: Upgrade\r\n" .
        "Sec-WebSocket-Accept: $accept\r\n\r\n";

    my $sent = syswrite($client, $response);
    return 0 unless defined $sent;

    record_transfer($sent);
    return 1;
}

# Encode a server->client text frame (unmasked, per spec).
sub ws_encode_text {
    my ($payload) = @_;

    my $len = length($payload);
    my $header;
    if ($len < 126) {
        $header = pack('CC', 0x81, $len);
    }
    elsif ($len < 65536) {
        $header = pack('CCn', 0x81, 126, $len);
    }
    else {
        $header = pack('CCNN', 0x81, 127, 0, $len);
    }

    return $header . $payload;
}

# Drop a connection and re-baseline the monitor once the last client leaves.
sub ws_remove_client {
    my ($c) = @_;

    @ws_clients = grep { $_ != $c } @ws_clients;
    close $c->{fh} if $c->{fh};

    $last_ws_signature = undef unless @ws_clients;
    request_redraw();
}

# Consume whatever the client sent: honor close frames, answer pings, and
# treat a dead socket as a disconnect. Everything else is ignored.
sub ws_handle_readable {
    my ($c) = @_;

    my $chunk = '';
    my $n = sysread($c->{fh}, $chunk, 4096);

    unless (defined $n) {
        return if $! == EINTR;
        ws_remove_client($c);
        return;
    }

    if ($n == 0) {
        ws_remove_client($c);
        return;
    }

    $c->{buf} .= $chunk;

    while (1) {
        my $buf = $c->{buf};
        last if length($buf) < 2;

        my $b0     = ord(substr($buf, 0, 1));
        my $b1     = ord(substr($buf, 1, 1));
        my $opcode = $b0 & 0x0f;
        my $masked = ($b1 & 0x80) ? 1 : 0;
        my $len    = $b1 & 0x7f;
        my $offset = 2;

        if ($len == 126) {
            last if length($buf) < 4;
            $len    = unpack('n', substr($buf, 2, 2));
            $offset = 4;
        }
        elsif ($len == 127) {
            last if length($buf) < 10;
            my ($hi, $lo) = unpack('NN', substr($buf, 2, 8));
            $len    = $lo;   # dev payloads never approach 4 GiB
            $offset = 10;
        }

        my $mask_len = $masked ? 4 : 0;
        last if length($buf) < $offset + $mask_len + $len;

        my $mask    = $masked ? substr($buf, $offset, 4) : '';
        my $payload = substr($buf, $offset + $mask_len, $len);

        if ($masked) {
            my @m = map { ord } split //, $mask;
            my $out = '';
            for my $i (0 .. length($payload) - 1) {
                $out .= chr(ord(substr($payload, $i, 1)) ^ $m[$i % 4]);
            }
            $payload = $out;
        }

        substr($c->{buf}, 0, $offset + $mask_len + $len, '');

        if ($opcode == 0x8) {          # close
            syswrite($c->{fh}, pack('CC', 0x88, 0));
            ws_remove_client($c);
            return;
        }
        elsif ($opcode == 0x9) {       # ping -> pong (control payloads are < 126 bytes)
            syswrite($c->{fh}, pack('CC', 0x8A, length($payload)) . $payload);
        }
        # text / binary / pong: nothing to do
    }
}

# Tell every connected client to reload, pruning any that have gone away.
sub ws_broadcast_reload {
    my $frame = ws_encode_text('reload');

    my @survivors;
    for my $c (@ws_clients) {
        if (defined syswrite($c->{fh}, $frame)) {
            push @survivors, $c;
        }
        else {
            close $c->{fh} if $c->{fh};
        }
    }
    @ws_clients = @survivors;

    $ws_reload_count++;
    $last_ws_reload       = strftime("%Y-%m-%d %H:%M:%S", localtime);
    $last_ws_reload_epoch = time();

    my $n = scalar @ws_clients;
    push_log_records(
        make_line("${GOOD}>> Hot reload pushed$RESET ${MUTED}- $n client" . ($n == 1 ? '' : 's') . " notified$RESET", 'center'),
    );
    play_tone('browser');
}

# While clients are connected, watch the web root and push a reload on change.
sub ws_check_filesystem {
    return unless @ws_clients;

    my $now = Time::HiRes::time();
    return if $now - $last_ws_scan_at < $WS_SCAN_INTERVAL;
    $last_ws_scan_at = $now;

    my $sig = web_root_signature();

    if (!defined $last_ws_signature) {
        $last_ws_signature = $sig;
        return;
    }

    return if $sig eq $last_ws_signature;

    $last_ws_signature = $sig;
    ws_broadcast_reload();
}

sub log_ws_connect {
    my ($ip) = @_;
    my $n = scalar @ws_clients;
    push_log_records(
        make_line("${GOOD}o$RESET ${LABEL}Hot reload client connected$RESET ${MUTED}($ip) - $n active$RESET", 'center'),
    );
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
        record_transfer($written);
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

        my $script = hot_reload_script();
        unless ($body =~ s{</body>}{$script</body>}i) {
            $body .= $script;
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

    my $sent = syswrite($client, $response);
    record_transfer($sent) if defined $sent;
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
    my ($content, $width) = @_;
    $width //= $LOG_WIDTH;
    my $pad = $width - 4 - strip_len($content);
    $pad = 0 if $pad < 0;
    return "$FRAME|$RESET " . $content . (' ' x $pad) . " $FRAME|$RESET\n";
}

sub field_row {
    my ($label, $value, $color, $width) = @_;
    $color //= $VALUE;
    $width //= $LOG_WIDTH;

    my $value_max = $width - 4 - 12;
    $value = truncate_text("$value", $value_max);

    return log_row($LABEL . sprintf('%-12s', $label) . $RESET . $color . $value . $RESET, $width);
}

sub browser_opened_banner {
    my ($url) = @_;

    my $width = $LOG_WIDTH + 20;
    $width = $TERM_COLS if $width > $TERM_COLS;
    my $sep = '=' x $width;

    return "\n$FRAME$sep$RESET\n"
         . field_row('Opening:', $url, $VALUE, $width)
         . "$FRAME$sep$RESET\n\n";
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

    my $tone = 'packet';
    if (exists $params{code}) {
        $tone = $params{code} >= 500 ? 'error'
              : $params{code} >= 400 ? 'warn'
              : 'packet';
    }
    play_tone($tone);
}

END {
    return unless $$ == $MAIN_PID;

    save_history();
    save_settings();
    if ($IS_TTY && $tui_active) {
        print "\e[?7h\e[?25h\e[0m\e[?1049l";
        $termios_orig->setattr(fileno(STDIN), TCSANOW) if $termios_orig;
    }
    close $server if $server;
}