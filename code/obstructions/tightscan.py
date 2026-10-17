# Exhaustive scan: primitive speed vectors in [1,H] with m speeds, tight (ML = 1/(m+1)), exact integer/Fraction arithmetic.
# Candidate times k/D, D in {2 v_i, v_i+v_j, |v_i-v_j|}, ALL numerators k in [0,D): superset of the local maxima of gap_v.
import itertools, math, sys
from fractions import Fraction as F
def ml_all(v):
    Ds=set()
    for a in v:
        Ds.add(2*a)
        for b in v:
            Ds.add(a+b)
            if a!=b: Ds.add(abs(a-b))
    best=F(0); mx=set()
    for D in sorted(Ds):
        for k in range(D):
            g=min(min((a*k)%D, D-(a*k)%D) for a in v)
            val=F(g,D)
            if val>best: best=val; mx={F(k,D)%1}
            elif val==best: mx.add(F(k,D)%1)
    return best,mx
def need(v,m): return all(any(a%j==0 for a in v) for j in range(2,m+1))
def main(m,H):
    tight=[];n=0
    for v in itertools.combinations(range(1,H+1),m):
        if math.gcd(*v)!=1 or not need(v,m): continue
        n+=1

        b,mx=ml_all(v)
        if b==F(1,m+1): tight.append((v,mx))
    bad=[v for v,mx in tight if any(a%(m+1)==0 for a in v)]
    badmax=[v for v,mx in tight if any((x*(m+1)).denominator!=1 for x in mx)]
    print(f"m={m} H={H} primitive vectors passing j<=m divisor filter: {n}; tight: {len(tight)}; with (m+1)|v_i: {len(bad)}; with a maximiser not in (1/(m+1))Z: {len(badmax)}")
    for v,mx in tight: print("  ",v)
    sys.stdout.flush()
if __name__=="__main__":
    for m,H in [(3,60),(4,40),(5,30),(6,24),(7,20),(8,16)]: main(m,H)
