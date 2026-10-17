# Independent cross-check (different code path from dense_check.rs): Fraction arithmetic, itertools,
# witness search over ALL rationals a/b with 2 <= b <= 6m. Soundness only needs a witness; no
# completeness claim is used. Run: python3 -I cross_check.py
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def gap(v, t):
    return min(min(F(x) * t - (F(x) * t).__floor__(), 1 - (F(x) * t - (F(x) * t).__floor__())) for x in v)

def ml_grid(v, bmax):
    best = F(0)
    for b in range(1, bmax + 1):
        for a in range(1, b):
            if gcd(a, b) == 1:
                g = gap(v, F(a, b))
                if g > best: best = g
    return best

print("controls (grid b<=40):", ml_grid([1,2,3,4,5], 40), ml_grid([1,3,4,7], 40))
assert ml_grid([1,2,3,4,5], 40) == F(1,6) and ml_grid([1,3,4,7], 40) == F(1,5)

def has_witness(v, m):
    thr = F(1, m + 1)
    for b in range(2, 6 * m + 1):
        for a in range(1, b):
            if gcd(a, b) == 1:
                if all(min((x * a) % b, b - (x * a) % b) * (m + 1) >= b for x in v): return True
    return False

for m in range(2, 9):
    H = 2 * m; tot = bad = 0
    for d in range(1, m + 1):          # multisets of size m == sets of size <= m (ML depends on the support)
        for v in combinations(range(1, H + 1), d):
            tot += 1
            if not has_witness(v, m): bad += 1
    print(f"m={m} 2m+1={2*m+1} sets(size<=m) in [1,{H}]: {tot} no-witness: {bad}")
