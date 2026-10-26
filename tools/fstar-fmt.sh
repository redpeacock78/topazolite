#!/bin/sh
# 標準入力の F* ソースを fstar.exe --print で整形し、標準出力へ書く。
# fstar.exe はファイル引数だけを受け付けるため、同じ拡張子の一時ファイルを経由する。
set -eu
case "${1:-}" in
  fst|fsti) ext=$1 ;;
  *) echo "usage: fstar-fmt.sh fst|fsti" >&2; exit 2 ;;
esac

fstar=${FSTAR_EXE:-fstar.exe}
ci_version=2026.09.13
version=$("$fstar" --version) || exit $?
printf '%s\n' "$version" >&2
case "$version" in
  *"$ci_version"*) ;;
  *) echo "警告: F* の版が CI（v$ci_version）と異なる。整形結果が CI と食い違いうる。" >&2 ;;
esac

dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cat > "$dir/Input.$ext"
status=0
"$fstar" --print "$dir/Input.$ext" > "$dir/out" || status=$?
if [ "$status" -ne 0 ]; then
  exit "$status"
fi
cat "$dir/out"
