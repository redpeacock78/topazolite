#!/bin/sh
# CI の fstar job と同じ検査を手元で実行する。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
fstar=${FSTAR_EXE:-fstar.exe}
ci_version=2026.09.13
version=$("$fstar" --version)
printf '%s\n' "$version"
case "$version" in
  *"$ci_version"*) ;;
  *) echo "警告: F* の版が CI（v$ci_version）と異なる。結果が CI と食い違いうる。CI の結果を最終の基準とする。" >&2 ;;
esac
"$fstar" --include model/fstar model/fstar/Topazolite.Surface.fst
"$fstar" --include model/fstar model/fstar/Topazolite.Parity.fst
racket tools/fstar-parity.rkt
sh tools/check-fstar-no-admit.sh model/fstar
