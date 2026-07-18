# Overport

The port is over 9000! This is a tiny Perl web-server that is HTTP/0.9 compliant.

## Dependencies

- A Perl interpreter

## Install

```bash
./install.sh
```

Symlinks `serve.pl` to `~/.local/bin/overport`, making `overport` a permanent
terminal command (make sure `~/.local/bin` is on your `PATH`).

## Usage

```bash
overport (optional webroot)
```

With no webroot argument, it looks for a `src` subdirectory in whatever
directory you ran the command from.

* Please note: the webroot must have a file name `index.html` and the entry.