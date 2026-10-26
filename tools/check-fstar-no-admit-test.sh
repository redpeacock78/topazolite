#!/bin/sh
# check-fstar-no-admit.sh が違反を拒否し、違反の無い写しを通すことを確かめる。
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
chk="$root/tools/check-fstar-no-admit.sh"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

fresh() {
  rm -rf "$work/c"
  cp -R "$root/model/fstar" "$work/c"
  rm -rf "$work/c/compiled"
}

expect_reject() {
  if sh "$chk" "$work/c" > /dev/null 2>&1; then
    echo "違反を検出しない: $1" >&2
    exit 1
  fi
}

fresh
sh "$chk" "$work/c" || { echo "違反の無い写しを拒否した" >&2; exit 1; }

fresh
printf '\nlet zz_probe_admit () : unit = admit ()\n' >> "$work/c/Topazolite.Surface.fst"
expect_reject admit

fresh
printf '\nlet zz_probe_assume () : unit = assume False\n' >> "$work/c/Topazolite.Surface.fst"
expect_reject assume

fresh
printf '\nval zz_probe_val : int\n' >> "$work/c/Topazolite.Surface.fst"
expect_reject val-without-let

fresh
printf '\n(* 証明は後で書く … *)\n' >> "$work/c/Topazolite.Surface.fst"
expect_reject placeholder

echo "check-fstar-no-admit OK"
