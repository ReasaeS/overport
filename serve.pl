#!/usr/bin/perl
use strict;
use warnings;
use Socket;
use File::Basename;
use File::Spec;
use POSIX qw(strftime);
use Time::HiRes qw(sleep);

# ======================
# Configuration
# ======================
my $PORT        = 9001;
my $HOST        = '0.0.0.0';
my $WEB_ROOT    = $ARGV[0] // File::Spec->catdir(dirname(__FILE__), '.' ); "The path of your WEB_ROOT here.";

my $INDEX_FILE  = File::Spec->catfile($WEB_ROOT, 'index.html');

my $PAGE_404    = File::Spec->catfile(dirname(__FILE__), 'status', '404.html');
my $BUFFER_SIZE = 8192;

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

my $reset  = "\e[0m";
my $bright = "\e[1m";
my $cyan   = "\e[96m";
my $magenta = "\e[95m";
my $yellow = "\e[93m";

# ======================
# Socket setup
# ======================
socket(my $server, PF_INET, SOCK_STREAM, getprotobyname('tcp')) or die "socket: $!";
setsockopt($server, SOL_SOCKET, SO_REUSEADDR, 1) or die "setsockopt: $!";
bind($server, sockaddr_in($PORT, inet_aton($HOST))) or die "bind: $!";
listen($server, SOMAXCONN) or die "listen: $!";

print "#" x 80 . "\n";
print "Server running at http://$HOST:$PORT/\n";
print "Web root: $WEB_ROOT\n";
print "Listening for input...\n";
print "#" x 80 . "\n" x 2;

# ======================
# Main loop
# ======================

my $stream_counter = 0;
my $last_time = time() - 5;

my $power_saving_time = 1/1028;

while (1) {

    if ($power_saving_time > 0) {
        sleep($power_saving_time);
    }

    my $client;
    my $client_addr = accept($client, $server) or next;
    
    my $now_time = time();
    my $delta_time = $now_time - $last_time;

    if ($delta_time >= 5) {
        my $stream_message = "STREAM ID: #$stream_counter" ;
        $stream_counter++;

        start_stream_banner($stream_message);
    }

    binmode($client);

    my $client_ip = inet_ntoa((sockaddr_in($client_addr))[1]) // 'unknown';

    my $request = '';
    my $bytes_read = sysread($client, $request, $BUFFER_SIZE);
    if (!$bytes_read) {
        close $client;
        next;
    }

    my ($method, $path) = parse_request($request);

    if (!$method || !$path) {
        send_response($client, 400, "Bad Request", "text/plain", "Invalid request", $client_ip, $path);
        close $client;
        next;
    }

    if ($method ne 'GET') {
        send_response($client, 405, "Method Not Allowed", "text/plain", "Method not allowed", $client_ip, $path);
        close $client;
        next;
    }

    my $file_path = sanitize_path($path);
    if (!$file_path) {
        send_response($client, 400, "Bad Request", "text/plain", "Invalid path", $client_ip, $path);
        close $client;
        next;
    }

    serve_file($client, $file_path, $client_ip);
    close $client;

    $last_time = $now_time;
}

# ======================
# Terminal utility
# ======================

sub start_stream_banner {
    my ($stream_message) = @_;
    
    my $line = '=' x 80;
    my $space = ' ' x 80;

    print "\n";
    print $cyan . $space . $reset . "\n";
    print $bright . $magenta . $line . $reset . "\n";
    print $bright . $yellow . "STARTING STREAM..." . $reset . "\n";
    print $bright . $cyan . "$stream_message" . $reset . "\n";
    print $bright . $magenta . $line . $reset . "\n";
    print $cyan . $space . $reset . "\n";
    print "\n";
}


# ======================
# Request parsing
# ======================
sub parse_request {
    my ($request) = @_;
    if ($request =~ /^([A-Z]+)\s+([^\s]+)\s+HTTP\/1\.[01]/) {
        return ($1, $2);
    }
    return;
}

# ======================
# Path sanitization
# ======================
sub sanitize_path {
    my ($path) = @_;

    $path = '/' if !defined $path || $path eq '';
    $path =~ s/[?#].*$//;
    $path =~ s{\\}{/}g;
    $path =~ s{/+}{/}g;

    return undef if $path =~ /\.\./ || $path =~ /\0/;

    $path =~ s{^/}{};

    if ($path eq '') {
        return $INDEX_FILE;
    }

    return File::Spec->catfile($WEB_ROOT, $path);
}

# ======================
# File serving
# ======================
sub serve_file {
    my ($client, $file_path, $client_ip) = @_;

    if (-d $file_path) {
        $file_path = $INDEX_FILE;
    }

    my ($ext) = $file_path =~ /\.([^.]+)$/;
    my $mime_type = $MIME_TYPES{lc($ext // '')} || 'application/octet-stream';

    unless (-f $file_path && -r $file_path) {
        serve_404($client, $client_ip, $file_path);
        return;
    }

    open(my $fh, '<', $file_path) or do {
        send_response($client, 500, "Internal Server Error", "text/plain", "Cannot open file", $client_ip, $file_path);
        return;
    };
    binmode($fh);

    my $file_size = -s $file_path;

    my $headers =
        "HTTP/1.1 200 OK\r\n" .
        "Content-Type: $mime_type\r\n" .
        "Content-Length: $file_size\r\n" .
        "Cache-Control: public, max-age=3600\r\n" .
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

    print $client $headers;

    my $sent = 0;
    my $packet_num = 1;

    while (my $read = sysread($fh, my $buffer, $BUFFER_SIZE)) {
        print $client $buffer;
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
# 404 handling
# ======================
sub serve_404 {
    my ($client, $client_ip, $requested_path) = @_;

    if ($requested_path =~ /\.html?$/i && -f $PAGE_404 && -r $PAGE_404) {
        serve_file($client, $PAGE_404, $client_ip);
    }

    send_response($client, 404, "Not Found", "text/plain", "File not found", $client_ip, $requested_path);
}


# ======================
# Generic responses
# ======================
sub send_response {
    my ($client, $code, $status, $type, $body, $client_ip, $file_path) = @_;

    my $response =
        "HTTP/1.1 $code $status\r\n" .
        "Content-Type: $type\r\n" .
        "Content-Length: " . length($body) . "\r\n" .
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
    );

    print $client $response;
}

# ======================
# Packet logger
# ======================
sub log_packet {
    my %params = @_;
    my $timestamp = strftime("%Y-%m-%d %H:%M:%S", localtime);

    my $separator    = '=' x 80;
    my $subseparator = '-' x 80;

    print "\n\033[1;36m$separator\033[0m\n";
    print "\033[1;33m| PACKET DETAILS (\033[1;37m$params{type}\033[1;33m) at \033[1;35m$timestamp\033[0m\n";
    print "\033[1;36m$subseparator\033[0m\n";

    print "\033[1;32m| Client:\033[0m     \033[1;37m$params{client_ip}\033[0m\n";

    print "\033[1;32m| File:\033[0m       \033[1;37m$params{file_path}\033[0m\n"
        if exists $params{file_path};

    print "\033[1;32m| Status:\033[0m     \033[1;37m$params{code} $params{status}\033[0m\n"
        if exists $params{code};

    print "\033[1;32m| MIME Type:\033[0m  \033[1;37m$params{mime_type}\033[0m\n"
        if exists $params{mime_type};

    print "\033[1;32m| Size:\033[0m       \033[1;37m$params{size} bytes\033[0m\n";

    print "\033[1;32m| File Size:\033[0m  \033[1;37m$params{file_size} bytes\033[0m\n"
        if exists $params{file_size};

    print "\033[1;32m| Packet #:\033[0m   \033[1;37m$params{packet_num}\033[0m\n"
        if exists $params{packet_num};

    print "\033[1;32m| Progress:\033[0m   \033[1;37m$params{progress}%\033[0m\n"
        if exists $params{progress};

    print "\033[1;36m$separator\033[0m\n\n";
}

END {
    close $server if $server;
}
