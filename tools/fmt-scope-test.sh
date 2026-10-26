#!/bin/sh
# dprint の整形対象が許可リストの三ファイルだけであることを確かめる。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
PATH="$root/node_modules/.bin:$PATH"
export PATH
tmp=$(mktemp -d)
pr=; pf=; pd=
# この起動が mktemp -d で作ったディレクトリだけを消す。既存のファイルには触れない。
trap 'rm -rf "$tmp" ${pr:+"$pr"} ${pf:+"$pf"} ${pd:+"$pd"}' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# 未整形の新規ファイルを各拡張子一つずつ、対象ディレクトリ内の専用ディレクトリに置く。
pr=$(mktemp -d model/redex/fmt-scope-probe.XXXXXX)
pf=$(mktemp -d model/fstar/fmt-scope-probe.XXXXXX)
pd=$(mktemp -d docs/specification/fmt-scope-probe.XXXXXX)
printf '(define   x\n1)\n' > "$pr/probe.rkt"
printf 'module Probe\nlet   x  =  1\n' > "$pf/Probe.fst"
printf '#  見出し\n\n*  項目\n' > "$pd/probe.md"

dprint file-paths | sed "s|^$root/||" | sort > "$tmp/paths"
printf '%s\n' .textlintrc.json dprint.json package.json | sort > "$tmp/expected"
if ! cmp -s "$tmp/paths" "$tmp/expected"; then
  echo "整形対象が許可リストと異なる" >&2
  diff "$tmp/expected" "$tmp/paths" >&2 || :
  exit 1
fi
dprint check

# 許可リストのファイルが未整形なら check が落ちることを、写しの設定で確かめる。
mkdir "$tmp/dirty"
cp dprint.json "$tmp/dirty/"
printf '{"name":   "x"}\n' > "$tmp/dirty/package.json"
printf '{}\n' > "$tmp/dirty/.textlintrc.json"
if (cd "$tmp/dirty" && dprint check >/dev/null 2>&1); then
  echo "未整形の package.json を dprint check が検出しない" >&2
  exit 1
fi
echo "fmt-scope OK"
