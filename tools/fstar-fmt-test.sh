#!/bin/sh
# tools/fstar-fmt.sh の契約を確かめる。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
w="$root/tools/fstar-fmt.sh"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
mkdir "$work/tmp"

# 一時ディレクトリが残らないことを見るため、TMPDIR を専用にする。
run() { TMPDIR="$work/tmp" sh "$w" "$@"; }
assert_tmp_empty() {
  if [ -n "$(ls -A "$work/tmp")" ]; then echo "一時ディレクトリが残った: $1" >&2; exit 1; fi
}

# 終了コード、版の表示、シグナルを確かめるための F* の代役。
cat > "$work/stub" <<'STUB'
#!/bin/sh
if [ "$1" = --version ]; then printf 'F* %s\n' "${STUB_VERSION:-2026.09.13}"; exit 0; fi
case "${STUB_MODE:-}" in
  fail) echo "途中の出力"; exit 37 ;;
  slow) : > "$STUB_MARK"; sleep 2; cat "$2" ;;
  *) cat "$2" ;;
esac
STUB
chmod +x "$work/stub"

# 正常系（実 F*）：.fst と .fsti を整形し、二回目で変わらない。
printf 'module A\nlet   x  =  1\n' | run fst > "$work/a1" 2> "$work/a1.err"
run fst < "$work/a1" > "$work/a2" 2> /dev/null
cmp -s "$work/a1" "$work/a2" || { echo ".fst が冪等でない" >&2; exit 1; }
grep -q 'F[*]' "$work/a1.err" || { echo "版を標準エラーに表示しない" >&2; exit 1; }
if grep -q 'F[*] ' "$work/a1" && ! grep -q '^module' "$work/a1"; then echo "版が標準出力に混じった" >&2; exit 1; fi
assert_tmp_empty fst
printf 'module A\nval x : int\n' | run fsti > "$work/i1" 2> /dev/null
grep -q '^val x' "$work/i1" || { echo ".fsti を interface として整形しない" >&2; exit 1; }
assert_tmp_empty fsti

# 版の警告：CI と同じ版では警告なし、異なる版では警告あり。どちらも標準出力は本文だけ。
printf 'x\n' | FSTAR_EXE="$work/stub" run fst > "$work/v1" 2> "$work/v1.err"
! grep -q '警告' "$work/v1.err" || { echo "CI と同じ版で警告した" >&2; exit 1; }
[ "$(cat "$work/v1")" = x ] || { echo "版の表示が標準出力に混じった" >&2; exit 1; }
printf 'x\n' | STUB_VERSION='2026.08.09~dev' FSTAR_EXE="$work/stub" run fst > "$work/v2" 2> "$work/v2.err"
grep -q '警告' "$work/v2.err" || { echo "異なる版で警告しない" >&2; exit 1; }
[ "$(cat "$work/v2")" = x ] || { echo "警告が標準出力に混じった" >&2; exit 1; }
assert_tmp_empty version

# F* の終了コードをそのまま返し、標準出力は空。
status=0
printf 'x\n' | STUB_MODE=fail FSTAR_EXE="$work/stub" run fst > "$work/f" 2> /dev/null || status=$?
[ "$status" -eq 37 ] || { echo "終了コード 37 を返さない: $status" >&2; exit 1; }
[ ! -s "$work/f" ] || { echo "失敗時に標準出力に書いた" >&2; exit 1; }
assert_tmp_empty fail

# 構文誤り（実 F*）：非 0 で終わり、標準出力は空。
if printf 'module A\nlet = = =\n' | run fst > "$work/bad" 2> /dev/null; then
  echo "構文誤りで exit 0" >&2; exit 1
fi
[ ! -s "$work/bad" ] || { echo "構文誤りで標準出力に書いた" >&2; exit 1; }
assert_tmp_empty bad

# fstar.exe が無い：非 0 で終わり、標準出力は空。
if printf 'module A\nlet x = 1\n' | FSTAR_EXE="$work/no-such-fstar" run fst > "$work/missing" 2> /dev/null; then
  echo "fstar.exe 不在で exit 0" >&2; exit 1
fi
[ ! -s "$work/missing" ] || { echo "fstar.exe 不在で標準出力に書いた" >&2; exit 1; }
assert_tmp_empty missing

# TERM：F* の実行中に止めても一時ディレクトリが残らない。
printf 'x\n' > "$work/in"
STUB_MODE=slow STUB_MARK="$work/mark" FSTAR_EXE="$work/stub" TMPDIR="$work/tmp" sh "$w" fst < "$work/in" > /dev/null 2>&1 &
pid=$!
i=0
while [ ! -e "$work/mark" ] && [ "$i" -lt 50 ]; do sleep 0.1; i=$((i + 1)); done
kill -TERM "$pid"
status=0
wait "$pid" || status=$?
[ "$status" -ne 0 ] || { echo "TERM 後に exit 0" >&2; exit 1; }
assert_tmp_empty term

# 拡張子の引数が誤り：非 0。
if printf 'x\n' | run txt > /dev/null 2>&1; then echo "誤った拡張子で exit 0" >&2; exit 1; fi
echo "fstar-fmt OK"
