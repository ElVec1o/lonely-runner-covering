# Lists the triples (n, r, mu), mu >= 2, satisfying criterion (1) with s = n - r >= 4 and gcd(r, n-1) = 1, for n <= NMAX.
# Pure integer arithmetic (about 10^7 gcd tests for NMAX = 1100).  Usage: python3 enum_coprime_case.py [NMAX]
import sys
from math import gcd
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 1100
out = []
for n in range(6, NMAX + 1):
    for r in range(2, n - 3):
        s = n - r
        if gcd(r, n - 1) != 1: continue
        mu = 2
        while all(gcd(r, b) > 1 for b in range(s, mu * s)):
            out.append((n, r, mu, s)); mu += 1
for t in out: print(*t)
print("count", len(out), "; distinct n:", sorted({t[0] for t in out}))
