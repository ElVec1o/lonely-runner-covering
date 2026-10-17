#!/bin/bash
# Re-derive the exact quantities in Table "tab:O4" and in Section "The Goddyn-Wong mechanism" of
# paper/obstructions/main.tex with the Rust program code/reduction/mdr (exact i128 integer arithmetic,
# standard library only).  Run from the bundle root:  bash code/obstructions/repro_O4.sh [BUILD_DIR]
# Output: one line per family.  Expected values are in the comments.
set -e
OUT=${1:-build/obstructions}; mkdir -p "$OUT"
rustc --edition 2021 -O -o "$OUT/mdr" code/reduction/mdr/src/main.rs
M="$OUT/mdr"
rustc --edition 2021 -O -o "$OUT/levelfit" code/reduction/levelfit/src/main.rs
LF="$OUT/levelfit"
rustc --edition 2021 -O -o "$OUT/mlcheck" code/obstructions/mlcheck.rs
MC="$OUT/mlcheck"

echo "--- row 1 (m=12): WC certificate level (WX) must exceed m+1 = 13; U1 = 1.003918"
$M certv 60 1,4,5,6,7,9,11,13,40,60,238,2731
$M u1 1,4,5,6,7,9,11,13,40,60,238,2731
echo "--- row 2 (m=12): ML = 11/84, least witness (4,31); U1 = 1.002573; WX level 13 (the WC at q=13)"
$M ml 1,3,4,5,7,9,11,13,40,48,100,1079
$M certv 60 1,3,4,5,7,9,11,13,40,48,100,1079
$M u1 1,3,4,5,7,9,11,13,40,48,100,1079
echo "--- row 3 (m=16): first window level 35; run with MDR_QMIN=18"
MDR_QMIN=18 $M certv 60 1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680
$M ml 1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680
echo "--- row 4 (m=18): ML = 28/191; first point at q = 38; U1 = 1.007002"
$M ml 1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943
$M certv 60 1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943
$M u1 1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943
echo "--- row 5 (m=18): ML = 30/203; U1 = 1.024583"
$M ml 1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422
$M certv 60 1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422
$M u1 1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422
echo "--- shifted lonely runner, speeds (1,2,3,4,6,9), phases (0,1/2,1/2,1/2,1/2,0): sup gap 3/22 at t = 7/22; ML = 1/5"
$M shift 1,2,3,4,6,9 0,1,1,1,1,0 2
$M ml 1,2,3,4,6,9

echo "--- invariants U1, U2 of the five table rows (Riesz-product ratios, f64 with an a posteriori error bound; column order: src m v class residU U1 U2 ML ...)"
# expected U1/U2: 1.003918/1.001345, 1.002573/1.000429, 1.483163/1.715019, 1.007002/1.003326, 1.024583/1.014631
$LF fitv 80 1,4,5,6,7,9,11,13,40,60,238,2731 1,3,4,5,7,9,11,13,40,48,100,1079 1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680 1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943 1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422 | cut -f2-8
echo "--- control for U_D: tight families [1..m] have U1, U2 >= 1 (Corollary of the barrier); families with ML far above 1/(m+1) have U1 < 1"
$LF fitv 80 1,2,3,4,5,6,7,8 1,2,3,4,5,6,7,8,9,10,11,12 1,3,7 1,5,17,60 | cut -f2-8
echo "--- last row of the table: exact multiple scan, hunt (time-limited, result UNRESOLVED whatever it prints)"
echo "    run: MDR_WX=1 mdr hunt2 M 6000 SECONDS SEED 2M+2 data/obstructions/seeds/seed_mM.txt OUT   (M = 18,20,22,24)"
echo "    optional here: set HUNT_SECONDS (default 0 = skipped) to run M = 18 for that many seconds"
if [ "${HUNT_SECONDS:-0}" -gt 0 ]; then
  MDR_WX=1 $M hunt2 18 6000 "$HUNT_SECONDS" 1 38 data/obstructions/seeds/seed_m18.txt "$OUT/hunt_m18.txt"
fi

echo "--- ML by the independent program mlcheck (all numerators): selftest, then the five table rows (expected 14/121, 11/84, 168/1697, 28/191, 30/203)"
$MC selftest | tail -1
$MC 1,4,5,6,7,9,11,13,40,60,238,2731 1,3,4,5,7,9,11,13,40,48,100,1079 1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680 1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943 1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422 | cut -c1-200
