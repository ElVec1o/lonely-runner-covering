#!/usr/bin/env python3 -I
"""Exact check of Proposition 'Tight corner' (paper/obstructions). Python glue: small boxes, exact Fractions.
Usage: python3 -I code/obstructions/cornercheck.py
For ML(v)=a/b<1/2 and every maximiser t=k/L (lowest terms): some speeds sit at +a/b and -a/b, and for EVERY such pair
(i,j): b | L, L | b*gcd(v_i,v_j), L | v_i+v_j.  Negative control: the broken predicate 'L == b' must fail somewhere."""
import itertools, sys
from fractions import Fraction as F
from math import gcd

def frac(x): return x - (x.numerator // x.denominator)

def ml_exact(v):
    D = set()
    for i in range(len(v)):
        D.add(2*v[i])
        for j in range(i+1, len(v)):
            D.add(v[i]+v[j])
            if v[i] != v[j]: D.add(abs(v[i]-v[j]))
    best, maxs = F(0), set()
    for d in D:
        for k in range(d):
            t = F(k, d)
            g = min(min(frac(x*t), 1-frac(x*t)) for x in v)
            if g > best: best, maxs = g, {t}
            elif g == best: maxs.add(t)
    return best, sorted(maxs)

def check(v, ml, t):
    a, b = ml.numerator, ml.denominator; L = t.denominator
    plus = [x for x in v if frac(x*t) == ml]; minus = [x for x in v if frac(x*t) == 1-ml]
    if not plus or not minus or L % b: return False, None
    for x in plus:
        for y in minus:
            if (b*gcd(x, y)) % L or (x+y) % L: return False, None
    return True, L//b

def main():
    for v, w in [((1,2,3,4,5), F(1,6)), ((1,3,4,7), F(1,5)), ((1,2,4,6), F(1,4)), ((1,2,3), F(1,4))]:
        got, mx = ml_exact(v); assert got == w, (v, got, w)
        print("control ML%s = %s, maximisers %s" % (v, got, [str(t) for t in mx]))
    # worked example
    v = (1,2,4,6); ml, mx = ml_exact(v)
    print("worked example", v, "ML", ml, "maximisers", [str(t) for t in mx])
    for t in mx:
        ok, d = check(v, ml, t); print("   t=%s L=%d b=%d d=%s lemma=%s" % (t, t.denominator, ml.denominator, d, ok))
        assert ok
    stats = dict(vectors=0, half=0, maximisers=0, fails=0, d_gt1=0, broken=0, tight=0, tight_d_gt1=0, tight_div=0)
    for m, H in [(2,30), (3,20), (4,12), (5,9)]:
        for v in itertools.combinations_with_replacement(range(1, H+1), m):
            ml, mx = ml_exact(v); stats['vectors'] += 1
            if ml >= F(1,2): stats['half'] += 1; continue
            tight = (ml == F(1, m+1))
            if ml < F(1, m+1): print("COUNTEREXAMPLE TO LRC??", v); sys.exit(1)
            if tight:
                stats['tight'] += 1
                if any(x % (m+1) == 0 for x in v) and gcd(*v) == 1: stats['tight_div'] += 1
            for t in mx:
                ok, d = check(v, ml, t); stats['maximisers'] += 1
                if not ok: stats['fails'] += 1; print("FAIL", v, t)
                else:
                    if d > 1: stats['d_gt1'] += 1
                    if tight and d > 1: stats['tight_d_gt1'] += 1
                if t.denominator != ml.denominator: stats['broken'] += 1
        print("box m=%d H<=%d done" % (m, H), stats)
    print("FINAL", stats)
    assert stats['fails'] == 0 and stats['broken'] > 0
main()
