#!/bin/sh
# CI の test job の三段（raco make、raco test、requirement coverage）を同じ順で実行する。
# requirement coverage は CI の if: always() に合わせ、前段が失敗しても実行する。
set -u
status=0
raco make -j 4 model/redex/tests/*.rkt && raco test -j 4 model/redex/tests/ || status=$?
cov=0
racket tools/req-coverage.rkt || cov=$?
if [ "$status" -eq 0 ]; then
  status=$cov
fi
exit "$status"
