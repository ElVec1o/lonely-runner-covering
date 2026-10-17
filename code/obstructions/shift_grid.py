# Exact rational grid scan for the shifted gap of Proposition "phase" (paper/obstructions/main.tex).
# gap_ph(t) = min_i dist(v_i t - ph_i, Z), t = p/q for all q <= QMAX, 0 <= p < q; exact Fraction arithmetic.
# Glue only: bounded loops (QMAX = 400, about 80,000 rational points), no large structures. Run: python3 -I shift_grid.py
from fractions import Fraction as F
def dist(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)
def scan(v, ph, qmax=400):
    best, arg = F(0), None
    for q in range(1, qmax + 1):
        for p in range(q):
            t = F(p, q)
            g = min(dist(vi * t - pi) for vi, pi in zip(v, ph))
            if g > best: best, arg = g, t
    return best, arg
v = [1, 2, 3, 4, 6, 9]
ph = [F(0), F(1, 2), F(1, 2), F(1, 2), F(1, 2), F(0)]
b, t = scan(v, ph); print("shifted phases (0,1/2,1/2,1/2,1/2,0): sup gap over q<=400 =", b, "at t =", t, "; expected 3/22 at 7/22")
b0, t0 = scan(v, [F(0)] * 6); print("control, zero phases: sup gap =", b0, "at t =", t0, "; expected 1/5")
assert b == F(3, 22) and t == F(7, 22) and b0 == F(1, 5)
print("OK")
