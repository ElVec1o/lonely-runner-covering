#!/bin/bash
# assemble_real.sh : compile lean/LRSpectrumFull/EightRunnersReal.lean with raw lean (one process)
# against the kept E8Stage oleans and print axioms of eight_runners_unconditional_real and
# hchk_all_real, in the SAME lean run (a copy of the file with the #print lines appended; importing the
# built olean by module name does not work because LRSpectrumFull.* resolves to lean/.lake).
# Requires all 27 work/records/P<p>/KEPT markers and Asm.olean. Does not use lake build.
# Refuses (exit 3) when 2 or more lean processes run machine-wide. Log: build/logs/assemble_real.log
# Expected last lines: both declarations depend on [propext, Classical.choice, Quot.sound] only.
. "$(dirname "$0")/env.sh"
PR="31 37 43 47 53 59 61 67 71 73 79 83 89 97 101 103 107 109 113 127 131 137 139 149 151 157 163"
for p in $PR; do [ -f "$W/records/P$p/KEPT" ] && [ -f "$W/olean/E8Stage/P$p/Asm.olean" ] || { echo "MISSING P$p (no KEPT/Asm.olean)"; exit 1; }; done
n=$(ps -axo comm | grep -c 'lean$'); [ "$n" -ge 2 ] && { echo "refuse: $n lean processes running"; exit 3; }
LP=$(cd "$LM" && lake env printenv LEAN_PATH); LEAN=$(cd "$LM" && lake env which lean)
OUT=$W/olean_final; mkdir -p "$OUT" "$ROOT/build/logs"
{ cat "$LM/LRSpectrumFull/EightRunnersReal.lean"; echo
  echo "#print axioms LRSpectrumFull.EightRunnersReal.eight_runners_unconditional_real"
  echo "#print axioms LRSpectrumFull.EightRunnersReal.hchk_all_real"; } > "$OUT/RealAx.lean"
cd "$LM"
LEAN_PATH="$LP:$W/olean" /usr/bin/time -l "$LEAN" -R "$LM" "$OUT/RealAx.lean" > "$ROOT/build/logs/assemble_real.log" 2>&1; rc=$?
grep -E "depends on axioms|error|sorry|warning" "$ROOT/build/logs/assemble_real.log" -A3 | grep -vE "^--$" | head -20
grep -E "maximum resident|real" "$ROOT/build/logs/assemble_real.log" | head -2
echo "lean exit code: $rc"
if [ $rc -eq 0 ] && [ "$(tr '\n' ' ' < "$ROOT/build/logs/assemble_real.log" | sed 's/  */ /g' | grep -o 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' | wc -l | tr -d ' ')" -eq 2 ]; then
  echo "ASSEMBLY OK: standard axioms only for both declarations"; exit 0
else echo "ASSEMBLY CHECK FAILED"; exit 2; fi
