#!/bin/sh
# Install renamer, its tab completion and its man page for the current user.
# Run it as yourself, not with sudo:  sh install.sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
bin_dir="$HOME/.local/bin"

if [ "$(id -u)" = 0 ]; then
    echo "Run this as your normal user, not root, so the files end up in your home folder." >&2
    exit 1
fi

# The version being replaced, for the changelog at the end. Copies from before the 2026-10-30
# renumbering still carry the old number: 10.0.0 is 1.0.0, 8.1 is 0.8.1.
old_version=""
[ -f "$bin_dir/renamer" ] && old_version=$(sed -n 's/^VERSION = "\(.*\)"$/\1/p' "$bin_dir/renamer")
case "$old_version" in
    10.*) old_version="1.${old_version#10.}" ;;
    [0-9].[0-9]) old_version="0.$old_version" ;;
esac

# 1. The command itself, without the .py, so it runs as plain "renamer".
mkdir -p "$bin_dir"
install -m 755 "$here/renamer.py" "$bin_dir/renamer"
echo "Installed $bin_dir/renamer"

# 2. zsh completion. oh-my-zsh already searches custom/completions; plain zsh needs an fpath line.
if [ -d "$HOME/.oh-my-zsh" ]; then
    zsh_dir="${ZSH_CUSTOM:-$HOME/.oh-my-zsh/custom}/completions"
    zsh_note=""
else
    zsh_dir="$HOME/.local/share/zsh/site-functions"
    zsh_note="Add this line to ~/.zshrc, before compinit runs:  fpath=(\"$zsh_dir\" \$fpath)"
fi
mkdir -p "$zsh_dir"
install -m 644 "$here/_renamer" "$zsh_dir/_renamer"
echo "Installed $zsh_dir/_renamer"

# 3. bash completion, loaded on demand by the bash-completion package.
bash_dir="${XDG_DATA_HOME:-$HOME/.local/share}/bash-completion/completions"
mkdir -p "$bash_dir"
install -m 644 "$here/renamer.bash" "$bash_dir/renamer"
echo "Installed $bash_dir/renamer"

# 4. The man page, for "man renamer". man-db searches ~/.local/share/man because ~/.local/bin is
#    on PATH, once the folder exists.
man_dir="${XDG_DATA_HOME:-$HOME/.local/share}/man/man1"
mkdir -p "$man_dir"
install -m 644 "$here/renamer.1" "$man_dir/renamer.1"
echo "Installed $man_dir/renamer.1"
man_note=""
if command -v man >/dev/null 2>&1 && ! man -w renamer >/dev/null 2>&1; then
    man_note="man doesn't find it yet. Add this line to ~/.zshrc or ~/.bashrc:  export MANPATH=\"\$HOME/.local/share/man:\""
fi

# 5. Tags (renamer meta, --meta) need ffmpeg and mkvtoolnix.
missing=""
for tool in ffprobe ffmpeg mkvmerge mkvpropedit mkvextract; do
    command -v "$tool" >/dev/null 2>&1 || missing="$missing $tool"
done
if [ -n "$missing" ]; then
    echo
    echo "Not installed:$missing. renamer meta and --meta need them; renaming works without."
    echo "    Debian/Ubuntu: sudo apt install ffmpeg mkvtoolnix"
    echo "    Arch:          sudo pacman -S ffmpeg mkvtoolnix-cli"
fi

echo
case ":$PATH:" in
    *":$bin_dir:"*) ;;
    *) echo "$bin_dir isn't in your PATH yet. Add this line to ~/.zshrc or ~/.bashrc:"
       echo "    export PATH=\"\$HOME/.local/bin:\$PATH\""
       echo ;;
esac
[ -n "$zsh_note" ] && { echo "$zsh_note"; echo; }
[ -n "$man_note" ] && { echo "$man_note"; echo; }
# What's new: every entry above the version being replaced. A reinstall, a first install or a
# version the changelog doesn't list shows the newest entry alone.
grep -qxF "## $old_version" "$here/CHANGELOG.md" || old_version=""
awk -v old="$old_version" '
    /^## / {
        n++
        if (n == 1) newest = $2
        else if (old == "" || old == newest || old == $2) exit
        else print ""
        print "What'\''s new in renamer " $2 ":"
        next
    }
    n && NF { print "  " $0 }
' "$here/CHANGELOG.md"
echo
# Each command on a line of its own, so the whole line can be copied and pasted.
echo "To load the completion in this terminal, run:"
echo
case "${SHELL##*/}" in
    zsh)  echo "    rm -f ~/.zcompdump*; exec zsh" ;;
    bash) echo "    exec bash" ;;
    *)    echo "In zsh:"
          echo "    rm -f ~/.zcompdump*; exec zsh"
          echo "In bash:"
          echo "    exec bash" ;;
esac
