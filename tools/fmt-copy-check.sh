#!/bin/sh
# 既存コードの写しだけを整形し、冪等性と意味の保存を確かめる。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
fstar=${FSTAR_EXE:-fstar.exe}
mode=${1:-}
work=
retain=1

find_work() {
  set --
  for candidate in "$root"/.codex/t1-fmt-copy-check.*; do
    [ -d "$candidate" ] && set -- "$@" "$candidate"
  done
  [ "$#" -eq 1 ] || {
    echo "fmt-copy-check の作業ディレクトリが一意でない" >&2
    exit 1
  }
  work=$1
}

report_retained_work() {
  rc=$?
  if [ "$retain" -eq 1 ] && [ -n "$work" ]; then
    printf 'workspace retained: %s; cleanup: sh tools/fmt-copy-check.sh cleanup\n' "$work" >&2
  fi
  return "$rc"
}

record_time() {
  ended=$(date +%s)
  line="$stage seconds=$((ended - started))"
  printf '%s\n' "$line" | tee -a "$work/timings.txt"
}

case "$mode" in
  prepare)
    [ -d "$root/.codex" ] || { echo ".codex/ が無い" >&2; exit 1; }
    for candidate in "$root"/.codex/t1-fmt-copy-check.*; do
      [ ! -d "$candidate" ] || { echo "既存の fmt-copy-check 作業ディレクトリ: $candidate" >&2; exit 1; }
    done
    work=$(mktemp -d "$root/.codex/t1-fmt-copy-check.XXXXXX")
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    started=$(date +%s)
    before="$work/before"
    after="$work/after"
    first="$work/first"
    mkdir "$before" "$after" "$first"
    git -C "$root" archive HEAD model/redex model/fstar tools docs/specification | tar -x -C "$before"
    cp -R "$before/." "$after/"
    jq '.includes = ["**/*.rkt", "**/*.fst", "**/*.fsti"]' "$root/dprint.json" > "$after/dprint.json"
    cp "$root/tools/fstar-fmt.sh" "$after/tools/fstar-fmt.sh"
    jq -er '.lineWidth | numbers' "$root/dprint.json" > "$work/line-width"
    find "$after/model/redex" -type f -name '*.rkt' -print | LC_ALL=C sort > "$work/rkt-list"
    split -l 60 "$work/rkt-list" "$work/rkt-batch-"
    : > "$work/timings.txt"
    stage=prepare
    record_time
    printf 'workspace=%s\n' "$work"
    printf 'rkt files=%s batches=' "$(wc -l < "$work/rkt-list" | tr -d ' ')"
    for batch in "$work"/rkt-batch-*; do printf '%s ' "${batch##*-}"; done
    printf '\n'
    ;;
  cleanup)
    find_work
    find "$work" -depth -delete
    retain=0
    echo "fmt-copy-check workspace cleaned"
    ;;
  dprint-rkt)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    suffix=${2:-}
    batch="$work/rkt-batch-$suffix"
    [ -n "$suffix" ] && [ -f "$batch" ] || { echo "batch が無い: $suffix" >&2; exit 1; }
    before="$work/before"
    after="$work/after"
    started=$(date +%s)
    stage="dprint-rkt-$suffix"
    (cd "$after" && DPRINT_CACHE_DIR="$work/dprint-cache" \
      xargs -n 60 timeout 600 dprint fmt --config "$after/dprint.json" < "$batch")
    record_time
    : > "$work/$stage.done"
    ;;
  dprint-fstar)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    after="$work/after"
    started=$(date +%s)
    stage=dprint-fstar
    (cd "$after" && DPRINT_CACHE_DIR="$work/dprint-cache" \
      timeout 600 dprint fmt --config "$after/dprint.json" model/fstar)
    record_time
    : > "$work/dprint-fstar.done"
    ;;
  snapshot)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    for batch in "$work"/rkt-batch-*; do
      suffix=${batch##*-}
      [ -f "$work/dprint-rkt-$suffix.done" ] || { echo "未処理の Racket batch: $suffix" >&2; exit 1; }
    done
    [ -f "$work/dprint-fstar.done" ] || { echo "F* の dprint が未実行" >&2; exit 1; }
    started=$(date +%s)
    stage=snapshot
    cp -R "$work/after/." "$work/first/"
    : > "$work/snapshot.done"
    record_time
    ;;
  verify-format)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    before="$work/before"
    after="$work/after"
    first="$work/first"
    [ -f "$work/snapshot.done" ] || { echo "一巡目の snapshot が無い" >&2; exit 1; }
    width=$(cat "$work/line-width")

    started=$(date +%s)
    stage=second-raco-fmt
    (cd "$after" && find model/redex -type f -name '*.rkt' -print | LC_ALL=C sort | \
      xargs -n 9999 timeout 600 raco fmt --width "$width" -i)
    record_time

    started=$(date +%s)
    stage=second-dprint-fstar
    (cd "$after" && DPRINT_CACHE_DIR="$work/dprint-cache" \
      timeout 600 dprint fmt --config "$after/dprint.json" model/fstar)
    record_time

    if ! diff -qr "$first/model" "$after/model" > "$work/idempotence.diff"; then
      cat "$work/idempotence.diff" >&2
      echo "二回目の整形で差分が出た" >&2
      exit 1
    fi
    echo "idempotence OK"
    ;;

  fstar)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    side=${2:-}
    file=${3:-}
    case "$side:$file" in
      before:Topazolite.Surface.fst|after:Topazolite.Surface.fst|before:Topazolite.Parity.fst|after:Topazolite.Parity.fst) ;;
      *) echo "usage: fmt-copy-check.sh fstar before|after Topazolite.Surface.fst|Topazolite.Parity.fst" >&2; exit 2 ;;
    esac
    tree="$work/$side"
    label="$side-${file%.fst}"
    started=$(date +%s)
    stage="fstar-$label"
    if timeout 600 "$fstar" --include "$tree/model/fstar" "$tree/model/fstar/$file" > "$work/$label.log" 2>&1; then
      printf '0\n' > "$work/$label.status"
    else
      rc=$?
      printf '%s\n' "$rc" > "$work/$label.status"
    fi
    printf '%s=%s\n' "$label" "$(cat "$work/$label.status")"
    record_time
    ;;

  compare-fstar)
    find_work
    file=${2:-}
    case "$file" in
      Topazolite.Surface.fst|Topazolite.Parity.fst) ;;
      *) echo "usage: fmt-copy-check.sh compare-fstar Topazolite.Surface.fst|Topazolite.Parity.fst" >&2; exit 2 ;;
    esac
    base_name=${file%.fst}
    for side in before after; do
      [ -f "$work/$side-$base_name.status" ] || { echo "$side の F* 結果が無い: $file" >&2; exit 1; }
    done
    if [ "$(cat "$work/before-$base_name.status")" -ne 0 ] || \
      [ "$(cat "$work/after-$base_name.status")" -ne 0 ] || \
      ! cmp -s "$work/before-$base_name.status" "$work/after-$base_name.status"; then
      printf 'before-%s=%s after-%s=%s\n' \
        "$base_name" "$(cat "$work/before-$base_name.status")" \
        "$base_name" "$(cat "$work/after-$base_name.status")" >&2
      echo "$file: 整形前後で F* の終了コードが異なる" >&2
      exit 1
    fi
    printf '%s=0\n' "$base_name"
    ;;

  focused)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    side=${2:-}
    case "$side" in before|after) ;; *) echo "usage: fmt-copy-check.sh focused before|after" >&2; exit 2 ;; esac
    tree="$work/$side"
    label="focused-$side"
    log="$work/$label.raco.log"
    started=$(date +%s)
    stage=$label
    (cd "$tree" && \
      timeout 600 raco make -j 4 model/redex/tests/req-coverage-test.rkt model/redex/tests/handoff-table-test.rkt model/redex/tests/lowering-test.rkt && \
      timeout 600 raco test -j 4 model/redex/tests/req-coverage-test.rkt model/redex/tests/handoff-table-test.rkt model/redex/tests/lowering-test.rkt) > "$log" 2>&1
    count=$(awk '$2 == "tests" && $3 == "passed" {n=$1} END {if (!n) exit 1; print n}' "$log") || {
      tail -40 "$log" >&2
      echo "$label: raco test の通過件数を取得できない" >&2
      exit 1
    }
    printf '%s\n' "$count" > "$work/$label.count"
    printf '%s tests=%s\n' "$label" "$count"
    record_time
    ;;

  finish)
    find_work
    trap report_retained_work EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    before="$work/before"
    after="$work/after"
    [ -f "$work/snapshot.done" ] || { echo "一巡目の snapshot が無い" >&2; exit 1; }
    [ -f "$work/idempotence.diff" ] || { echo "二巡目の固定点検査が無い" >&2; exit 1; }
    for base_name in Topazolite.Surface Topazolite.Parity; do
      for side in before after; do
        [ -f "$work/$side-$base_name.status" ] || { echo "F* 結果が無い: $side-$base_name" >&2; exit 1; }
      done
      [ "$(cat "$work/before-$base_name.status")" -eq 0 ] && \
        [ "$(cat "$work/after-$base_name.status")" -eq 0 ] && \
        cmp -s "$work/before-$base_name.status" "$work/after-$base_name.status" || {
          echo "F* status mismatch: $base_name" >&2
          exit 1
        }
    done
    for side in before after; do [ -f "$work/focused-$side.count" ] || { echo "focused 結果が無い: $side" >&2; exit 1; }; done
    if ! cmp -s "$work/focused-before.count" "$work/focused-after.count"; then
      printf 'before=%s after=%s\n' "$(cat "$work/focused-before.count")" "$(cat "$work/focused-after.count")" >&2
      echo "focused の試験件数が整形前後で異なる" >&2
      exit 1
    fi

    if grep -rn -E '\b(admit|assume)\b' "$after/model/fstar/"; then
      echo "model/fstar/ に admit か assume がある" >&2
      exit 1
    fi
    for file in "$after"/model/fstar/*.fst; do
      for name in $(grep -oE '^val [A-Za-z_][A-Za-z0-9_]*' "$file" | awk '{print $2}'); do
        if ! grep -qE "^let (rec )?$name[ (:]" "$file"; then
          echo "$file: val $name に対応する let が無い" >&2
          exit 1
        fi
      done
    done
    if grep -rnF '(*' "$after/model/fstar/" | grep -F '…'; then
      echo "model/fstar/ に置き場所だけの注釈がある" >&2
      exit 1
    fi
    echo "no-admit OK"

    find "$after/model/fstar" -type f -name '*.fst' -print | \
      while IFS= read -r file; do awk 'length($0) > 100 {n++} END {print n+0}' "$file"; done | \
      awk '{n += $1} END {print n+0}' > "$work/long-lines"

    count_diff() {
      tree=$1
      suffix=$2
      find "$before/model" -type f -name "*.$suffix" -print | while IFS= read -r path; do
        rel=${path#"$before/"}
        git diff --no-index --numstat "$before/$rel" "$tree/$rel" || :
      done | awk -F '\t' '$1 ~ /^[0-9]+$/ {added += $1; removed += $2} END {printf "%d added, %d removed\n", added, removed}'
    }
    printf 'F* lines over 100=%s\n' "$(cat "$work/long-lines")"
    printf 'Racket line changes: %s\n' "$(count_diff "$after" rkt)"
    printf 'F* line changes: %s\n' "$(count_diff "$after" fst)"
    echo 'stage timings:'
    cat "$work/timings.txt"
    printf 'total recorded stage seconds=%s\n' "$(awk -F= '{sum += $NF} END {print sum+0}' "$work/timings.txt")"
    find "$work" -depth -delete
    retain=0
    echo "fmt-copy-check OK; workspace cleaned"
    ;;
  *)
    echo "usage: fmt-copy-check.sh prepare|dprint-rkt <batch>|dprint-fstar|snapshot|verify-format|fstar <side> <file>|compare-fstar <file>|focused <side>|finish|cleanup" >&2
    exit 2
    ;;
esac
