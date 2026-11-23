#!/usr/bin/env bash
# reproduce.sh: check the rank barrier in Lean and the (r, Q, R) = (2, 3, 2) table by script. See README.md.
#
#   ./reproduce.sh          fetch the pinned Lean toolchain, Mathlib and Mathlib's compiled cache (network);
#                           build lean/RankBarrier.lean; print its axioms; run both controls; run both scripts
#                           and compare their output with results/out.txt
#
# Needs: Linux on x86-64 (tested) or arm64 (untested), bash, curl, git, python3 >= 3.9, zstd, tar.
# Work files go to $ERB_WORK (default ./work); Mathlib and its cache go to lean/.lake: about 6 GB in all.
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$PWD
WORK=${ERB_WORK:-$ROOT/work}
export XDG_CACHE_HOME=$WORK/cache

# ---------------------------------------------------------------- pins
LEAN_VERSION=4.33.1
case "$(uname -s)/$(uname -m)" in
  Linux/x86_64) LEAN_ASSET=lean-4.33.1-linux.tar.zst
                LEAN_SHA=890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235 ;;
  Linux/aarch64|Linux/arm64) LEAN_ASSET=lean-4.33.1-linux_aarch64.tar.zst
                LEAN_SHA=f7353a8b2a8741c84558523e450556f9a1c45e3cafcf54399ce68c6a24c55f07 ;;
  *) echo "unsupported platform $(uname -s)/$(uname -m): use Linux x86-64 or arm64 (on a Mac, Docker; see README.md)" >&2; exit 2 ;;
esac
# Mathlib and its dependencies: the commits in lean/lake-manifest.json (Mathlib v4.33.1 = 0df444a3).
LEAN_DIR=$WORK/tools/lean-$LEAN_VERSION
export PATH=$LEAN_DIR/bin:$PATH

T0=$(date +%s)
step() { printf '\n== [+%ds] %s\n' "$(( $(date +%s) - T0 ))" "$*"; }
die() { echo "FAILED: $*" >&2; exit 1; }

# ---------------------------------------------------------------- fetch (network)
step "fetch: Lean $LEAN_VERSION ($LEAN_ASSET)"
mkdir -p "$WORK/dl"
if [ ! -x "$LEAN_DIR/bin/lake" ]; then
  [ -f "$WORK/dl/$LEAN_ASSET" ] && [ "$(sha256sum "$WORK/dl/$LEAN_ASSET" | cut -d' ' -f1)" = "$LEAN_SHA" ] ||
    curl -fsSL --retry 3 -o "$WORK/dl/$LEAN_ASSET" \
      "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/$LEAN_ASSET"
  echo "$LEAN_SHA  $WORK/dl/$LEAN_ASSET" | sha256sum -c --quiet - || die "Lean toolchain sha256"
  mkdir -p "$LEAN_DIR"
  tar -C "$LEAN_DIR" --strip-components=1 --use-compress-program=unzstd -xf "$WORK/dl/$LEAN_ASSET"
fi
echo "sha256 $LEAN_SHA ok"

step "fetch: Mathlib and its dependencies at lean/lake-manifest.json's commits"
python3 - lean/lake-manifest.json > "$WORK/dl/packages.tsv" <<'PY'
import json, sys
for p in json.load(open(sys.argv[1]))['packages']:
    print('%s\t%s\t%s' % (p['name'], p['url'], p['rev']))
PY
while IFS=$'\t' read -r name url rev; do
  d=$ROOT/lean/.lake/packages/$name
  if [ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" != "$rev" ]; then
    rm -rf "$d"; mkdir -p "$d"
    git -C "$d" init -q
    git -C "$d" remote add origin "$url"
    git -C "$d" fetch -q --depth 1 origin "$rev"
    git -C "$d" -c advice.detachedHead=false checkout -q FETCH_HEAD
  fi
  [ "$(git -C "$d" rev-parse HEAD)" = "$rev" ] || die "$name is not at $rev"
  printf '%-18s %s\n' "$name" "$rev"
done < "$WORK/dl/packages.tsv"

step "fetch: Mathlib's compiled .olean files (lake exe cache get)"
(cd lean && lake exe cache get) 2>&1 | tr '\r' '\n' | { grep -v '^Downloaded:' || true; } | tail -3

# ---------------------------------------------------------------- Lean (offline from here)
step "Lean: build RankBarrier.lean"
(cd lean && lake build 2>&1 | tail -2)

step "Lean: must-pass control (controls/must-pass.lean), with #print axioms"
(cd lean && lake env lean controls/must-pass.lean) | tee "$WORK/must-pass.out" || die "must-pass control did not build"
python3 - "$WORK/must-pass.out" <<'PY' || die "axioms"
import re, sys
text = open(sys.argv[1]).read()
items = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text.replace('\n', ' '))
ok = {'propext', 'Classical.choice', 'Quot.sound'}
bad = [n for n, a in items if not {x.strip() for x in a.split(',') if x.strip()} <= ok]
if len(items) != 5 or bad or 'error' in text:
    sys.exit('unexpected output: %d theorems listed, outside the standard axioms: %s' % (len(items), bad))
print('AXIOMS OK: all 5 theorems use only propext, Classical.choice, Quot.sound (no sorryAx, no native_decide)')
PY

step "Lean: must-fail control (controls/must-fail.lean): both statements must be rejected"
if (cd lean && lake env lean controls/must-fail.lean) > "$WORK/must-fail.out" 2>&1; then
  cat "$WORK/must-fail.out"; die "must-fail control was accepted"
fi
cat "$WORK/must-fail.out"
[ "$(grep -c ': error: ' "$WORK/must-fail.out")" = 2 ] || die "must-fail: expected exactly 2 errors"
grep -q '^controls/must-fail.lean:8:.*Application type mismatch' "$WORK/must-fail.out" || die "must-fail: F1 not rejected by type mismatch"
grep -q '^controls/must-fail.lean:10:.*Tactic `decide` proved that the proposition' "$WORK/must-fail.out" || die "must-fail: F2 not refuted by decide"
echo "MUST-FAIL OK: F1 (support weakened to <= R) and F2 (count 8) are both rejected"

# ---------------------------------------------------------------- scripts
step "scripts: tiny.py and mais.py, compared with results/out.txt"
(cd scripts && {
  echo '$ python3 -I tiny.py'; python3 -I tiny.py
  for a in "2 2 2" "2 3 3" "2 3 2"; do echo "\$ python3 -I mais.py $a"; python3 -I mais.py $a; done
}) > "$WORK/out.txt"
diff "$WORK/out.txt" results/out.txt || die "script output differs from results/out.txt"
echo "SCRIPTS OK: output identical to results/out.txt"

step "ALL CHECKS PASSED"
