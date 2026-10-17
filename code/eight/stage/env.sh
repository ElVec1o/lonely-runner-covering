# Sourced by the stage scripts. All paths are relative to this repository.
S=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)          # code/eight/stage
E=$(cd "$S/.." && pwd)                                   # code/eight
ROOT=$(cd "$E/../.." && pwd)                             # repository root
LM=$ROOT/lean
GEN=$E/bin/l7v4s                                         # built by build_generator.sh
W=$S/work                                                # staging: sources, oleans, logs, new records
REC=$E/records                                           # committed records (read only here)
mkdir -p "$W/logs" "$W/records"
