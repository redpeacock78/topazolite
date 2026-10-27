#!/bin/sh
# lint-text.sh が空の許可リストで通り、違反を含む文書を拒否することを確かめる。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

: > "$work/empty"
LINT_TEXT_ALLOWLIST="$work/empty" sh tools/lint-text.sh || {
  echo "空の許可リストで失敗した" >&2
  exit 1
}

printf '# 見出し\n\nこれはテストのの文です。。\n' > "$work/bad.md"
printf '%s\n' "$work/bad.md" > "$work/list"
if LINT_TEXT_ALLOWLIST="$work/list" sh tools/lint-text.sh > /dev/null 2>&1; then
  echo "違反を含む文書を通した" >&2
  exit 1
fi
echo "lint-text OK"
