#!/bin/bash
# compile1.sh P MOD : compile one staged module E8Stage.P<P>.<MOD> with a single `lean` process
# (no lake), olean into work/olean, log with /usr/bin/time -l. A lean process is started only while
# fewer than 2 run machine-wide (mkdir lock). Exit: lean's code; 3 = refused (low disk or STOP file).
. "$(dirname "$0")/env.sh"
P=$1; M=$2; K=E8Stage
LOGF=$W/logs/${K}_P${P}_$M.log
LP=$(cd "$LM" && lake env printenv LEAN_PATH)
LEAN=$(cd "$LM" && lake env which lean)
mkdir -p "$W/olean/$K/P$P"
while :; do
  [ -f "$W/STOP" ] && { echo "REFUSE STOP file" > "$LOGF"; exit 3; }
  if mkdir "$W/.slotlock" 2>/dev/null; then
    n=$(ps -axo comm | grep -c 'lean$')
    [ "$n" -lt 2 ] && break
    rmdir "$W/.slotlock"
  fi
  sleep 4
done
free_mb=$(df -m "$W" | awk 'NR==2{print $4}')
if [ "$free_mb" -lt "${MINMB:-1640}" ]; then rmdir "$W/.slotlock"; echo "REFUSE low disk ${free_mb}MB" > "$LOGF"; touch "$W/STOP"; exit 3; fi
s=$(date +%s)
cd "$W/src"
LEAN_PATH="$LP:$W/olean" /usr/bin/time -l "$LEAN" -R "$W/src" \
  -o "$W/olean/$K/P$P/$M.olean" "$W/src/$K/P$P/$M.lean" > "$LOGF" 2>&1 &
cpid=$!
for i in 1 2 3 4 5 6 7 8 9 10; do pgrep -P $cpid >/dev/null && break; sleep 0.5; done
sleep 1
rmdir "$W/.slotlock"
wait $cpid; rc=$?
echo "EXIT:$rc wall=$(( $(date +%s) - s ))s" >> "$LOGF"
exit $rc
