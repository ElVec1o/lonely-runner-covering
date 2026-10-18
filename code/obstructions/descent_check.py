#!/usr/bin/env python3 -I
"""Exact checks for Section 'Descent and topological obstructions' (paper/obstructions). Python glue: exact Fractions,
bounded memory, each mode runs in under 5 minutes.

Usage (from the archive root):
  python3 -I code/obstructions/descent_check.py controls            # control battery of the ML routine (must print SELFTEST PASS)
  python3 -I code/obstructions/descent_check.py d0                  # monotonicity and dilation on random vectors
  python3 -I code/obstructions/descent_check.py instances           # m = 7 witnesses, second-level witnesses, near-tight examples
  python3 -I code/obstructions/descent_check.py table [MFULL]       # the 70 tight vectors; full recomputation for m <= MFULL (default 73)
  python3 -I code/obstructions/descent_check.py gw                  # regenerates the single-acceleration Goddyn-Wong triples for n <= 260 from the GCD condition
  python3 -I code/obstructions/descent_check.py strict [MMAX]       # the eleven strict values of m; V recomputed for m <= MMAX (default 151)

Convention: m = number of speeds, ML(v) = max_t min_i ||v_i t||, tight means ML = 1/(m+1), loo(V) = min_i ML(V minus v_i),
a tight leave-one-out is ML(V minus v_i) = 1/m exactly.
The function ml and the control battery below are copied unchanged from the standard exact routine (every numerator k of
k/L, L = v_i + v_j; no coprime filter), whose earlier variants skipped numerators not coprime to L.
"""
import sys, random
from fractions import Fraction as F

def ml(v):
    """Return (ML as Fraction, one maximiser t as Fraction)."""
    v = [int(x) for x in v]
    assert v and all(x > 0 for x in v), "speeds must be positive integers"
    best, arg = F(0), F(0)
    for L in sorted({a + b for i, a in enumerate(v) for b in v[i:]}):
        for k in range(L):                      # every numerator
            m = min(min((a * k) % L, L - (a * k) % L) for a in v)
            if m * best.denominator > best.numerator * L:
                best, arg = F(m, L), F(k, L)
    return best, arg

def grid(v, qmax=200):
    """Independent lower bound: max over t = p/q, q <= qmax, all p in 0..q (numpy, exact int64)."""
    best = F(0)
    try:
        import numpy as np
        va = np.array(v, dtype=np.int64)
        for q in range(1, qmax + 1):
            p = np.arange(0, q + 1, dtype=np.int64)
            r = (p[:, None] * va[None, :]) % q
            mx = int(np.minimum(r, q - r).min(axis=1).max())
            if mx * best.denominator > best.numerator * q: best = F(mx, q)
    except ImportError:                          # pure-Python fallback (slower; p <= q/2 by the symmetry t -> 1-t)
        for q in range(1, qmax + 1):
            for p in range(0, q // 2 + 1):
                mx = min(min((a * p) % q, q - (a * p) % q) for a in v)
                if mx * best.denominator > best.numerator * q: best = F(mx, q)
    return best

CONTROLS = [((1,2,3,4,5), F(1,6)), ((1,3,4,7), F(1,5)), ((7,19), F(1,2)), ((3,4,7,11), F(2,9)),
            ((1,4,6,7,10,11,12,13,16,17,19,23), F(1,9)), ((1,5,6,11,16,17), F(5,33)),
            ((1,2,3,4,5,7,12), F(1,8)), ((2,3,6), F(1,3)), ((5,), F(1,2))]

def selftest(n_random=None, seed=20261018):
    try:
        import numpy  # noqa
        n_random = n_random or 2000
    except ImportError:
        n_random = n_random or 300      # pure-Python grid is slow; Rust twin runs 2000
    ok = True
    for v, e in CONTROLS:
        r, _ = ml(v); g = grid(v); good = (r == e == g); ok &= good
        print(f"{list(v)} ML={r} expected {e} grid(q<=200)={g} {'OK' if good else 'FAIL'}")
    rng = random.Random(seed); bad = 0
    for _ in range(n_random):          # m = 2..6, distinct speeds <= 40: maximiser denominators <= 80 < 200
        v = sorted(rng.sample(range(1, 41), rng.randint(2, 6)))
        r, _ = ml(v)
        if r != grid(v):
            bad += 1; print("RANDOM MISMATCH", v, r, grid(v))
    print(f"random battery (seed {seed}): {bad} mismatches of {n_random}")
    return ok and bad == 0

# ---------------------------------------------------------------- end of the copied standard routine

import os, itertools, time
from math import gcd

def loo(v):
    """(loo value, set of removed speeds attaining it, list of all removal values)."""
    vals = []
    for i in range(len(v)):
        w = v[:i] + v[i+1:]
        vals.append(ml(w)[0])
    lo = min(vals)
    return lo, sorted({v[i] for i in range(len(v)) if vals[i] == lo}), vals

def build_gw(tag):
    """Vector from a tag of data/obstructions/descent_gw_loo.tsv: [n-1] with r replaced by mu*r (one entry),
    or with r in acc replaced by 2r (tag 'GWmulti')."""
    p = tag.split()
    n = int(p[1].split("=")[1])
    v = list(range(1, n))
    if p[0] == "GW1":
        r = int(p[2].split("=")[1]); mu = int(p[3].split("=")[1])
        v[r-1] = mu * r
    else:
        acc = [int(x) for x in tag.split("acc=[")[1].rstrip("]").split(",")]
        for r in acc: v[r-1] = 2 * r
    assert len(set(v)) == len(v)
    return sorted(v)

def parse_fr(s):
    a, b = s.split("/"); return F(int(a), int(b))

def read_table(path):
    rows = []
    with open(path) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for line in f:
            x = line.rstrip("\n").split("\t")
            rows.append(dict(tag=x[0], n=int(x[1]), m=int(x[2]), loo=parse_fr(x[3]), rem=int(x[4])))
    return rows

def d0(seed=20261018, n=1500):
    rng = random.Random(seed); bad = 0
    for _ in range(n):
        v = rng.sample(range(1, 61), rng.randint(2, 7)); r = ml(v)[0]
        c = rng.randint(2, 9)
        if ml([c * x for x in v])[0] != r: bad += 1; print("DILATION FAIL", v, c)
        for i in range(len(v)):
            if ml(v[:i] + v[i+1:])[0] < r: bad += 1; print("MONOTONE FAIL", v, i)
    print(f"d0: {n} random vectors (seed {seed}, 2 to 7 speeds in [1,60], dilation factors 2 to 9): {bad} failures")
    # negative control: a false monotonicity claim must fail, 'deleting a speed lowers ML'
    ctrl = sum(1 for _ in range(200) if (lambda v: ml(v[:-1])[0] < ml(v)[0])(rng.sample(range(1, 61), 4)))
    print(f"d0 control (deletion lowers ML, false): fires {ctrl} times of 200 (must be 0)")
    return bad == 0 and ctrl == 0

def instances():
    ok = True
    print("-- m = 7")
    for v in ([1,4,5,6,7,11,13], [1,2,3,4,5,7,12]):
        r = ml(v)[0]; lo, arg, vals = loo(v)
        print(f"V={v} ML={r} tight={r==F(1,8)} loo={lo} removed={arg} removal values={[str(x) for x in vals]}")
        ok &= (r == F(1,8) and lo == F(2,13))
    W = [1,5,6,11,16,17]; rw = ml(W)[0]
    print(f"W={W} (6 speeds) ML={rw}; 1/7 < ML(W) < 2/13: {F(1,7) < rw < F(2,13)}")
    ok &= (rw == F(5,33) and F(1,7) < rw < F(2,13))
    print("-- sporadic tight vectors")
    for v in ([1,3,4,7], [1,3,4,5,9]):
        m = len(v); r = ml(v)[0]; lo, arg, vals = loo(v)
        print(f"V={v} m={m} ML={r} (1/(m+1)={F(1,m+1)}) loo={lo} removed={arg} 2/(2m-1)={F(2,2*m-1)}")
        ok &= (r == F(1,m+1) and lo == F(2,2*m-1))
    print("-- second-level witnesses [m-2] u {2(m-1)}: ML = 2/(2m-1) > 1/m, m-1 speeds")
    bad = []
    for m in list(range(3, 101)):
        v = list(range(1, m-1)) + [2*(m-1)]
        if len(v) != m-1 or ml(v)[0] != F(2, 2*m-1) or not F(2, 2*m-1) > F(1, m): bad.append(m)
    print(f"m = 3..100: failures at {bad}")
    ok &= not bad
    print("-- near-tight examples (1/(m+1) < ML < 1/m)")
    for v in ([1,2,3,5,8], [1,2,3,4,5,7,18,40], [1,5,6,7,8,11,13,19,20,27]):
        m = len(v); r = ml(v)[0]; lo, arg, vals = loo(v)
        tight_sub = []
        for k in range(2, m):
            for s in itertools.combinations(v, k):
                if ml(list(s))[0] == F(1, k+1): tight_sub.append(s)
        nsub = sum(1 for k in range(2, m) for _ in itertools.combinations(v, k))
        print(f"V={v} m={m} ML={r} in (1/{m+1},1/{m}): {F(1,m+1) < r < F(1,m)}; loo={lo} removed={arg}; "
              f"removal values={[str(x) for x in vals]}; tight leave-one-out: {any(x==F(1,m) for x in vals)}; "
              f"tight proper subfamilies of size 2..{m-1}: {len(tight_sub)} of {nsub}"
              + (f": {tight_sub}" if tight_sub else ""))
        ok &= (F(1,m+1) < r < F(1,m)) and not any(x == F(1,m) for x in vals)
    print("instances:", "OK" if ok else "FAIL")
    return ok

STRICT_M = [7, 31, 61, 73, 91, 121, 143, 151, 181, 211, 241]

def table(path, mfull):
    rows = read_table(path)
    t0 = time.time(); ok = True; recomputed = 0
    recs = []     # (m, loo, tight_loo, source)
    for r in rows:
        v = build_gw(r["tag"]); m = len(v); assert m == r["m"] and r["n"] == m + 1
        if m <= mfull:
            ml_v = ml(v)[0]
            lo, arg, vals = loo(v)
            good = (ml_v == F(1, m+1) and lo == r["loo"] and r["rem"] in arg)
            ok &= good; recomputed += 1
            src = "recomputed"
            print(f"{r['tag']:36s} m={m:3d} ML={ml_v} loo={lo} removed={arg} table={r['loo']}@{r['rem']} {'OK' if good else 'MISMATCH'}", flush=True)
        else:
            lo = r["loo"]; src = "table"
        recs.append((m, lo, lo == F(1, m), src, r["tag"]))
    for v in ([1,3,4,7], [1,3,4,5,9], [1,4,5,6,7,11,13]):
        m = len(v); assert ml(v)[0] == F(1, m+1)
        lo = loo(v)[0]; recs.append((m, lo, lo == F(1, m), "recomputed", "sporadic " + str(v)))
        recomputed += 1
    n_all = len(recs)
    with_tight = [x for x in recs if x[2]]; without = [x for x in recs if not x[2]]
    eq = [x for x in without if x[1] == F(2, 2*x[0]-1)]
    gt = [x for x in without if x[1] > F(2, 2*x[0]-1)]
    lt = [x for x in without if x[1] < F(2, 2*x[0]-1)]
    gw_without = [x for x in without if not x[4].startswith("sporadic")]
    gw_eq = [x for x in gw_without if x[1] == F(2, 2*x[0]-1)]
    print(f"vectors: {n_all} (67 Goddyn-Wong type + 3 sporadic); rows recomputed here: {recomputed} (m <= {mfull} and the sporadics), taken from the table: {n_all - recomputed}")
    print(f"tight leave-one-out: {len(with_tight)}; none: {len(without)}")
    print(f"among the {len(without)} without: loo = 2/(2m-1): {len(eq)}; loo > 2/(2m-1): {len(gt)}; loo < 2/(2m-1): {len(lt)}")
    print(f"among the {len(gw_without)} Goddyn-Wong type without: equal {len(gw_eq)}, above {len(gt)}; sporadic: {len(without)-len(gw_without)} (all equal: {all(x[1]==F(2,2*x[0]-1) for x in without if x[4].startswith('sporadic'))})")
    print("strictly above, by m:", sorted((x[0], str(x[1])) for x in gt))
    print("m with tight leave-one-out:", sorted(x[0] for x in with_tight))
    ok &= (n_all, len(with_tight), len(without), len(eq), len(gt), len(lt), len(gw_without), len(gw_eq)) == (70, 11, 59, 46, 13, 0, 56, 43)
    print(f"table: {'OK' if ok else 'FAIL'} ({time.time()-t0:.1f} s)")
    return ok

def gw_single(nmax=260, wrong=False):
    """All (n, r, mu), 3 <= n <= nmax, mu >= 2, with the GCD condition: gcd(r, b) > 1 for every b in [n-r, mu(n-r)-1].
    wrong=True tests gcd(n, b) > 1 instead (a deliberately wrong condition, used as negative control)."""
    out = []
    for n in range(3, nmax + 1):
        for r in range(1, n):
            mu = 2
            while all(gcd(n if wrong else r, b) > 1 for b in range(n - r, mu * (n - r))):
                out.append((n, r, mu)); mu += 1
                if mu > 3 * n: break
    return out

def gw(path):
    gen = set(gw_single())
    tab = set()
    for r in read_table(path):
        if r["tag"].startswith("GW1"):
            p = r["tag"].split(); tab.add((int(p[1].split("=")[1]), int(p[2].split("=")[1]), int(p[3].split("=")[1])))
    print(f"GCD-condition triples (n, r, mu), 3 <= n <= 260, mu >= 2: {len(gen)}; single-acceleration rows of the table: {len(tab)}")
    print(f"in generator, not in table: {sorted(gen - tab)}; in table, not in generator: {sorted(tab - gen)}")
    # negative control: the wrong condition gcd(n, b) > 1 must give a different set
    weak = set(gw_single(wrong=True))
    print(f"control (gcd(n, b) > 1 instead of gcd(r, b) > 1): {len(weak)} triples, differs from the table: {weak != tab}")
    ok = gen == tab and weak != tab
    print(f"gw: {'OK' if ok else 'FAIL'}")
    return ok

def strict(path, mmax):
    rows = {(r["m"], r["loo"]): r for r in read_table(path)}
    ok = True; t0 = time.time()
    print("m, witness V (loo above sigma bound), sigma bound = ML of the (m-1)-speed vector, jump lower bound")
    for m in STRICT_M:
        if m == 7:
            V = [1,4,5,6,7,11,13]; W = [1,5,6,11,16,17]
            lo = loo(V)[0]; sig = ml(W)[0]; assert ml(V)[0] == F(1, 8)
            print(f"m=7: V={V} loo={lo}, W={W} ML={sig}, loo - ML(W) = {lo - sig}  [recomputed]")
            ok &= lo > sig > F(1, 7); continue
        cand = [r for r in rows.values() if r["m"] == m and r["loo"] > F(2, 2*m-1) and r["loo"] > F(1, m)]
        wv = [1 + i for i in range(m-2)] + [2*(m-1)]
        sig = ml(wv)[0]; assert sig == F(2, 2*m-1) > F(1, m)
        for r in cand:
            if m > mmax:
                print(f"m={m}: {r['tag']} loo={r['loo']} (table), sigma bound 2/(2m-1)={sig} (recomputed), loo > bound: {r['loo']>sig}  [ML(V) and loo taken from the table]", flush=True)
                ok &= r["loo"] > sig; continue
            v = build_gw(r["tag"]); mlv = ml(v)[0]
            vm = [x for x in v if x != r["rem"]]; mlrem = ml(vm)[0]
            full = ""
            if m <= 73:
                lo = loo(v)[0]; full = f" loo recomputed over all {m} removals = {lo}"; ok &= lo == r["loo"]
            print(f"m={m}: {r['tag']} ML={mlv} (tight: {mlv==F(1,m+1)}), ML(V minus {r['rem']}) = {mlrem} (table loo {r['loo']}), "
                  f"sigma bound 2/(2m-1)={sig}, loo > bound: {r['loo']>sig}{full}", flush=True)
            ok &= (mlv == F(1, m+1) and mlrem == r["loo"] and r["loo"] > sig)
        ok &= bool(cand)
    print(f"strict: {'OK' if ok else 'FAIL'} ({time.time()-t0:.1f} s)")
    return ok

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    tsv = os.path.join(here, "..", "..", "data", "obstructions", "descent_gw_loo.tsv")
    mode = sys.argv[1] if len(sys.argv) > 1 else ""
    if mode == "controls": good = selftest(); print("SELFTEST PASS" if good else "SELFTEST FAIL")
    elif mode == "d0": good = d0()
    elif mode == "instances": good = instances()
    elif mode == "table": good = table(tsv, int(sys.argv[2]) if len(sys.argv) > 2 else 73)
    elif mode == "gw": good = gw(tsv)
    elif mode == "strict": good = strict(tsv, int(sys.argv[2]) if len(sys.argv) > 2 else 151)
    else: print(__doc__); sys.exit(2)
    sys.exit(0 if good else 1)
