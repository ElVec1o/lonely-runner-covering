#!/bin/bash
# run_glp.sh M TMAX TMLIM MINPROFIT : master MIP of the block family (profit >= MINPROFIT) written by
# `xc lp` and solved by glpsol, then read back by `xc fromglp`.
# Run from the directory data/dense (the tools take that directory as their working root).
# Environment: BIN = directory holding the built binary `xc` (default ../../build/dense).
BIN=${BIN:-../../build/dense}
[ -n "$IRR" ] && export XC_IRRED=1
m=$1; t=$2; lim=$3; mp=${4:--99}
tag=m${m}_t${t}_p${mp}${IRR:+_irr}
mkdir -p logs/xc
XC_MINPROFIT=$mp XC_BIN=1 $BIN/xc lp $m $t 99 logs/xc/glp_$tag.lp | tail -1
glpsol --lp logs/xc/glp_$tag.lp -o logs/xc/glp_$tag.sol --tmlim $lim --mipgap 0 > logs/xc/glp_$tag.log 2>&1
tail -4 logs/xc/glp_$tag.log
rm -f logs/xc/glp_$tag.lp
XC_MINPROFIT=$mp $BIN/xc fromglp $m $t 99 logs/xc/glp_$tag.sol | grep -v "^chunk"
