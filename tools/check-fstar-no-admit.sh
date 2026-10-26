#!/bin/sh
# model/fstar に admit と assume、let の無い val、置き場所だけの注釈が無いことを確かめる。
# .github/workflows/test.yml の no admit or assume 段と同じ検査である（T5 で CI を切り替える）。
set -eu
dir=${1:-model/fstar}

if grep -rn -E '\b(admit|assume)\b' "$dir"; then
  echo "$dir に admit か assume がある" >&2
  exit 1
fi

for f in "$dir"/*.fst; do
  for n in $(grep -oE '^val [A-Za-z_][A-Za-z0-9_]*' "$f" | awk '{print $2}'); do
    if ! grep -qE "^let (rec )?$n[ (:]" "$f"; then
      echo "$f: val $n に対応する let が無い" >&2
      exit 1
    fi
  done
done

if grep -rnF '(*' "$dir" | grep -F '…'; then
  echo "$dir に置き場所だけの注釈がある" >&2
  exit 1
fi
