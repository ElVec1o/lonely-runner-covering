# Exact check of Goddyn-Wong type vectors: ML = 1/n and n divides no speed (n = m+1).
from tightscan import ml_all
from fractions import Fraction as F
def acc(n, mu): return sorted(r*mu.get(r,1) for r in range(1,n))
cases={
 "T1 (1,3,4,7)":[1,3,4,7],
 "T2 (1,3,4,5,9)":[1,3,4,5,9],
 "Wills (1,4,5,6,7,11,13)":[1,4,5,6,7,11,13],
 "(1,2,3,4,5,7,12)":[1,2,3,4,5,7,12],
 "[1..11]+{13,24}":list(range(1,12))+[13,24],
 "[1..17]+{19,36}":list(range(1,18))+[19,36],
 "n=74 doubling 70,72":[r for r in range(1,74) if r not in (70,72)]+[140,144],
}
for name,v in cases.items():
    m=len(v); n=m+1
    b,mx=ml_all(v)
    print(name,"n=%d"%n,"ML=",b,"tight=",b==F(1,n),"n|speed:",any(a%n==0 for a in v),"maximisers in (1/n)Z:",all((x*n).denominator==1 for x in mx))
