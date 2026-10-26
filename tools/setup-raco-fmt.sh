#!/bin/sh
# 固定した raco fmt と依存を user scope に揃え、user layer で compile する。
set -eu
pe=https://github.com/sorawee/pretty-expressive.git
pe_commit=ce4e0e178bf8d492ded88c62a796e44e7f059e70
fmt_commit=4e1ed68e596e656960b44a8244bb33eb4e65ec64

# $1 は package 名、$2 は URL#commit。
# 照会失敗は未導入と扱わず、名前の行が無い場合だけ install する。
setup_pkg() {
  listing=$(raco pkg show --user --full-checksum "$1") || return
  installed=$(printf '%s\n' "$listing" | grep -E "^ *$1\\*? " || :)
  case "$installed" in
    *"${2##*#}"*) echo "$1: ${2##*#} は導入済み" ;;
    "") raco pkg install --user --auto --no-setup --no-docs --batch "$2" ;;
    *) raco pkg update --user --deps search-auto --no-setup --no-docs --batch "$2" ;;
  esac
}

setup_pkg pretty-expressive-lib "$pe?path=pretty-expressive-lib#$pe_commit"
setup_pkg pretty-expressive "$pe?path=pretty-expressive#$pe_commit"
setup_pkg fmt "https://github.com/sorawee/fmt.git#$fmt_commit"
raco setup --avoid-main --no-docs --pkgs pretty-expressive-lib pretty-expressive fmt
