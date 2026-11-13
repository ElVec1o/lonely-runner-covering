#!/bin/bash
# usage: launch_watchdog.sh CEILING_MB LOGDIR NAME cmd args...   (declare the ceiling; nice -n 10; own process group; memory + disk watchdog; RSS is summed over the process tree)
# Used for the builds of 2026-11 with CEILING_MB = 12000 (the watchdog kills the tree at 90% of the ceiling, i.e. 10800 MB). No memory or load gate is applied before the start; only a disk floor of 3 GB.
# Written for macOS (ps, df -g on /System/Volumes/Data). The only edit made for the archive: the preflight comment and an unused variable were removed.
CEIL=${1:?}; LOGDIR=${2:?}; NAME=${3:?}; shift 3
mkdir -p "$LOGDIR"
DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "$DG" -ge 3 ] || { echo "ONEOFF FAIL: disk ${DG}GB"; exit 3; }
set -m
nice -n 10 "$@" > "$LOGDIR/$NAME.out" 2> "$LOGDIR/$NAME.err" &
PID=$!; PG=$PID
echo "launched $NAME pid=$PID ceiling=${CEIL}MB $(date +%T)" >> "$LOGDIR/$NAME.watch"
( while kill -0 $PID 2>/dev/null; do
    # 2026-11-12: sum RSS over the whole process tree (lake's lean child was invisible before) and kill the tree
    TREE=$(ps -axo pid=,ppid=,rss= | awk -v r=$PID '{pp[$1]=$2; rs[$1]=$3} END{t[r]=1; do{c=0; for(p in pp) if(!(p in t) && (pp[p] in t)){t[p]=1;c=1}}while(c); s=0; l=""; for(p in t){s+=rs[p]; l=l" "p}; print s, l}')
    RSS=${TREE%% *}; PIDS=${TREE#* }; [ -z "$RSS" ] || [ "$RSS" = 0 ] && break
    MB=$((RSS/1024)); echo "$(date +%T) rss=${MB}MB" >> "$LOGDIR/$NAME.watch"
    if [ "$MB" -gt $((CEIL*90/100)) ]; then echo "WATCHDOG KILL rss=${MB}MB > 90% of ${CEIL}MB" >> "$LOGDIR/$NAME.watch"; kill $PIDS 2>/dev/null; kill -- -$PG 2>/dev/null; break; fi
    DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "$DG" -lt 2 ] && { echo "WATCHDOG KILL disk ${DG}GB" >> "$LOGDIR/$NAME.watch"; kill $PIDS 2>/dev/null; kill -- -$PG 2>/dev/null; break; }
    sleep 2
  done ) &
wait $PID; echo "exit=$? $(date +%T)" >> "$LOGDIR/$NAME.watch"
