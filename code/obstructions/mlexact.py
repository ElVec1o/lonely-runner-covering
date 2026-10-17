# Independent exact computation of ML(v) (does not use mdr or mlcheck).
# ML is attained at a time k/D with D in {2 v_i, v_i+v_j, |v_i-v_j|}; ALL numerators k in [0,D) are scanned.
# Integer arithmetic for the gap, Fraction only for comparing maxima.  Memory bounded, runtime seconds.
import sys
from fractions import Fraction as F
def ml(v):
    Ds=set()
    for a in v:
        Ds.add(2*a)
        for b in v:
            Ds.add(a+b)
            if a!=b: Ds.add(abs(a-b))
    best=F(0); arg=None
    for D in sorted(Ds):
        for k in range(D//2+1):
            g=min(min((a*k)%D, D-(a*k)%D) for a in v)
            if F(g,D)>best: best=F(g,D); arg=(k,D)
    return best,arg
TESTS={
 "row1 m=12":[1,4,5,6,7,9,11,13,40,60,238,2731],
 "row2 m=12":[1,3,4,5,7,9,11,13,40,48,100,1079],
 "row3 m=16":[1,5,6,7,8,9,11,13,17,19,23,25,29,31,366,1680],
 "row4 m=18":[1,3,4,5,7,11,13,17,19,23,31,70,74,116,180,272,3986,4943],
 "row5 m=18":[1,3,4,5,7,11,13,17,19,23,31,38,70,74,116,180,272,4422],
 "(1,2,3,4,6,9)":[1,2,3,4,6,9],
 "(1,3,4)":[1,3,4],
 "E_14":list(range(1,14))+[14*15],
 "(1..11,13,24,210)":list(range(1,12))+[13,24,210],
 "(1,5,6,11,16,17)":[1,5,6,11,16,17],
 "(3,4,7,11)":[3,4,7,11],
}
if __name__=="__main__":
    for n,v in TESTS.items():
        b,a=ml(v); print(n,"m=%d"%len(v),"ML=",b,"at",a,flush=True)
