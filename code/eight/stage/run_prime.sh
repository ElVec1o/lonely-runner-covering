#!/bin/bash
# run_prime.sh P [SLOTS] : full kernel re-check of prime P (resumable).
#   generate -> compile Base, then {Tab, Top, S*} on up to SLOTS concurrent lean processes -> Asm
#   -> check (EXIT 0 everywhere, no error/sorry, axioms standard) -> write work/records/P<P>/record.txt
#   -> delete the staged sources and oleans (KEEP=1: keep oleans, marker KEPT, record.real.txt;
#      MINMB=<MB> overrides the 1640 MB free-disk floor).
# At most 2 lean processes machine-wide; each peaks near 1 GB. The largest prime stages ~150 MB.
# Exit: 0 verified, 1 build failure, 2 check failure, 3 refused (low disk / STOP file).
. "$(dirname "$0")/env.sh"
P=$1; SLOTS=${2:-2}; MAXF=${MAXF:-400000}; TABB=${TABB:-16}
D=$W/src/E8Stage/P$P; O=$W/olean/E8Stage/P$P; R=$W/records/P$P
log() { echo "$(date '+%F %T') P$P $*" >> "$W/logs/campaign.log"; }
KEEP=${KEEP:-0}   # KEEP=1: keep the oleans (delete only the .lean sources); done-marker is $R/KEPT
if [ "$KEEP" = 1 ]; then [ -f "$R/KEPT" ] && { log "already kept"; exit 0; }
else [ -f "$R/VERIFIED" ] && { log "already verified"; exit 0; }; fi
[ -f "$W/STOP" ] && { log "STOP file present"; exit 3; }
mkdir -p "$R"
RECF=$R/record.txt; [ "$KEEP" = 1 ] && RECF=$R/record.real.txt   # KEEP mode never overwrites record.txt
MINMB=${MINMB:-1640}; export MINMB
free_mb=$(df -m "$W" | awk 'NR==2{print $4}'); [ "$free_mb" -lt "$MINMB" ] && { log "REFUSE low disk ${free_mb}MB"; exit 3; }
if [ ! -f "$D/manifest.txt" ]; then
  rm -rf "$D" "$O"
  "$GEN" "$P" stage "$D" "$MAXF" "$TABB" bitkey 2> "$R/gen.err" || { log "generator failed"; exit 1; }
  log "generated $(head -1 "$D/manifest.txt")"
fi
done_ok() { [ -f "$O/$1.olean" ] && grep -q '^EXIT:0 ' "$W/logs/E8Stage_P${P}_$1.log" 2>/dev/null; }
wait_slot() {
  while :; do
    [ -f "$W/STOP" ] && return 1
    n=$(ps -axo comm | grep -c 'lean$'); ours=$(jobs -rp | wc -l | tr -d ' ')
    [ "$n" -lt 2 ] && [ "$ours" -lt "$SLOTS" ] && return 0
    sleep 5
  done
}
run_mod() {
  done_ok "$1" && return 0
  wait_slot || return 3
  "$S/compile1.sh" "$P" "$1"; rc=$?
  log "$1 rc=$rc $(grep -E '^EXIT' "$W/logs/E8Stage_P${P}_$1.log")"
  return $rc
}
t0=$(date +%s)
run_mod Base || { log "Base failed"; exit 1; }
MODS="Tab Top $(ls "$D" | sed -n 's/^\(S[0-9]*\)\.lean$/\1/p' | sort -t S -k2 -n | tr '\n' ' ')"
for m in $MODS; do
  done_ok $m && continue
  wait_slot || { wait; log "stopped"; exit 3; }
  ( run_mod $m ) &
  sleep 3
done
wait
for m in $MODS; do done_ok $m || { log "module $m failed"; exit 1; }; done
run_mod Asm || { log "Asm failed"; exit 1; }
bad=$(grep -lE "error|sorry" "$W"/logs/E8Stage_P${P}_*.log)
ax=$(grep "depends on axioms" "$W/logs/E8Stage_P${P}_Asm.log")
if [ -n "$bad" ] || [ "$ax" != "'LRSpectrumFull.EightV4.Cert$P.lemma7Check_seven_p$P' depends on axioms: [propext, Classical.choice, Quot.sound]" ]; then
  log "CHECK FAILED bad=[$bad] ax=[$ax]"; exit 2; fi
{
  echo "theorem LRSpectrumFull.EightV4.Cert$P.lemma7Check_seven_p$P : lemma7Check 7 $P = true"
  echo "$ax"
  echo "verified_at: $(date '+%F %T')  total_wall_s: $(( $(date +%s) - t0 ))"
  echo "generator: code/eight/generator/l7v4.rs sha256 $(shasum -a 256 "$E/generator/l7v4.rs" | cut -d' ' -f1)"
  echo "checker: lean/LRSpectrumFull/EightCheckV4.lean sha256 $(shasum -a 256 "$LM/LRSpectrumFull/EightCheckV4.lean" | cut -d' ' -f1)"
  echo "soundness: lean/LRSpectrumFull/EightCheckSound.lean sha256 $(shasum -a 256 "$LM/LRSpectrumFull/EightCheckSound.lean" | cut -d' ' -f1)"
  echo "toolchain: $(cat "$LM/lean-toolchain")"
  echo "combined_sha256 $(cd "$D" && cat $(ls *.lean | sort) | shasum -a 256 | cut -d' ' -f1)"
} > "$RECF"
if [ "$KEEP" = 1 ]; then
  touch "$R/KEPT"
  { echo "olean_bytes $(du -sk "$O" | cut -f1) KiB"; ls -l "$O" | awk 'NR>1{print $5, $9}'; } > "$R/olean_sizes.txt"
  rm -rf "$D"; rm -f "$W"/logs/E8Stage_P${P}_*.log
  log "VERIFIED+KEPT (oleans kept, sources deleted); wall=$(( $(date +%s) - t0 ))s"
  exit 0
fi
touch "$R/VERIFIED"
rm -rf "$D" "$O"; rm -f "$W"/logs/E8Stage_P${P}_*.log
log "VERIFIED; staging deleted; wall=$(( $(date +%s) - t0 ))s"
exit 0
