#!/bin/sh
# 許可リストに載った文書だけに textlint をかける。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
list=${LINT_TEXT_ALLOWLIST:-tools/textlint-allowlist.txt}
files=$(grep -v -E '^(#|$)' "$list" || :)
if [ -z "$files" ]; then
  echo "lint:text: 許可リストは空"
  exit 0
fi
# 一行一ファイルを位置引数へ積む（xargs -0 は POSIX に無いので使わない）。
set --
while IFS= read -r f; do
  set -- "$@" "$f"
done <<EOF
$files
EOF
textlint --config .textlintrc.json "$@"
