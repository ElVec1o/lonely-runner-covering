# Exact check of the worked examples of paper/goddyn-wong-loo (integer and Fraction arithmetic only).
# Part 1: n=8, r=6, mu=2, V={1,2,3,4,5,7,12}.  Part 2: n=74, r=70, mu=2, deletion of n-1 (witness t = a/Q).
# Runs in well under one second; no large data structures.  Usage: python3 example_check.py
from fractions import Fraction as F
from math import gcd

def dist(x):                      # distance to the nearest integer, exact
    x = x - (x.numerator // x.denominator)
    return min(x, 1 - x)

def ml(v):
    """ML(v) = max_t min_i ||v_i t||; a maximiser can be taken of the form k/(v_i+v_j)."""
    best = F(0)
    for L in sorted({a + b for a in v for b in v}):
        for k in range(L):
            m = min(dist(F(x * k, L)) for x in v)
            if m > best: best = m
    return best

def ml_grid(v, qmax=400):         # independent cross-check: all t = p/q with q <= qmax
    best = F(0)
    for q in range(1, qmax + 1):
        for p in range(q):
            m = min(dist(F(x * p, q)) for x in v)
            if m > best: best = m
    return best

n, r, mu = 8, 6, 2
V = [x for x in range(1, n) if x != r] + [mu * r]
s = n - r
assert all(gcd(r, b) > 1 for b in range(s, mu * s)), "criterion (1) fails"
print("V =", V, "; criterion (1): gcd(6,b) > 1 for b in [2,3]")
print("ML(V) =", ml(V), "(grid:", ml_grid(V), ")")
vals = {}
for j in V:
    W = [x for x in V if x != j]
    vals[j] = ml(W)
    assert vals[j] == ml_grid(W)
    print("delete %2d: ML = %s" % (j, vals[j]))
c = F(mu, mu * r + 1)
print("loo =", min(vals.values()), "; mu/(mu r+1) =", c, "; minimisers:", [j for j in V if vals[j] == c])
assert min(vals.values()) == c and [j for j in V if vals[j] == c] == [n - 1]

def mind(W, t): return min(dist(x * t) for x in W)
Q = mu * r + 1
t = F(mu, Q)                       # witness of Corollary 3 for the deletion of n-1 = 7
print("deleting 7: t* = 2/13, min over W =", mind([x for x in V if x != 7], t))
assert mind([x for x in V if x != 7], t) == c
t = F(1, 6);  print("deleting 12: t = 1/6, min =", mind([x for x in V if x != 12], t)); assert mind([x for x in V if x != 12], t) >= F(1, 6)
t = F(1, 5);  print("deleting  5: t = 1/5, min =", mind([x for x in V if x != 5], t));  assert mind([x for x in V if x != 5], t) >= F(1, 5)
delta = F(1, r * Q); t = F(1, 4) + delta
print("deleting  4: t = 1/4 + 1/78 = %s, min =" % t, mind([x for x in V if x != 4], t)); assert mind([x for x in V if x != 4], t) == c
for x in [1, 2, 3, 5, 7, 12]: print("   x=%2d  ||x t|| = %s" % (x, dist(x * t)))

# Part 2: Lemma 10 at n=74, r=70, mu=2 (s=4, gcd(r,n-1)=gcd(70,73)=1)
n, r, mu = 74, 70, 2; s = n - r
assert all(gcd(r, b) > 1 for b in range(s, mu * s)) and gcd(r, n - 1) == 1
V = [x for x in range(1, n) if x != r] + [mu * r]
Q = 2 * r + s - 1; a = pow(r, -1, Q); t = F(a, Q)
W = [x for x in V if x != n - 1]
m = mind(W, t)
print("n=74: Q = %d, a = %d, min over V minus {73} of ||x a/Q|| = %s; 2/Q = %s; 1/(n-2) = %s" % (Q, a, m, F(2, Q), F(1, n - 2)))
assert m == F(2, Q) and m > F(1, n - 2)
print("OK")
