#!/bin/bash
# status.sh : primes re-verified in work/records, lean processes, disk, last log lines.
. "$(dirname "$0")/env.sh"
echo "re-verified: $(for d in "$W"/records/P*; do [ -f "$d/VERIFIED" ] && echo -n "${d##*P} "; done)"
echo "lean processes: $(ps -axo comm | grep -c 'lean$')   disk free: $(df -h "$W" | awk 'NR==2{print $4}')"
tail -5 "$W/logs/campaign.log" 2>/dev/null
