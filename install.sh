#!/usr/bin/env bash
#
# Installs `overport` as a permanent terminal command by symlinking it
# into a directory on your PATH. Run this once from anywhere; it locates
# serve.pl relative to this script, not the current directory.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SERVE_PL="$SCRIPT_DIR/serve.pl"
COMMAND_NAME="overport"

if [ ! -f "$SERVE_PL" ]; then
    echo "error: $SERVE_PL not found" >&2
    exit 1
fi

chmod +x "$SERVE_PL"

# Prefer ~/.local/bin (no sudo, standard user bin dir) over /usr/local/bin.
INSTALL_DIR="$HOME/.local/bin"
mkdir -p "$INSTALL_DIR"

LINK_PATH="$INSTALL_DIR/$COMMAND_NAME"
ln -sf "$SERVE_PL" "$LINK_PATH"

echo "Installed: $LINK_PATH -> $SERVE_PL"

case ":$PATH:" in
    *":$INSTALL_DIR:"*)
        echo "Done. Run '$COMMAND_NAME' from any directory."
        ;;
    *)
        echo
        echo "warning: $INSTALL_DIR is not on your PATH."
        echo "Add this to your shell rc file (e.g. ~/.bashrc or ~/.zshrc):"
        echo
        echo "    export PATH=\"\$HOME/.local/bin:\$PATH\""
        echo
        ;;
esac
