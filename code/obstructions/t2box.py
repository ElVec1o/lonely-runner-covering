# Minimum of ML over primitive divisor-complete vectors (every j in [2,m+1] divides a speed) in boxes [1,H]^m.
import itertools, math
from fractions import Fraction as F
from mlexact import ml
def dc(v,m): return all(any(a%j==0 for a in v) for j in range(2,m+2))
for m,H in [(3,60),(4,40),(5,30),(6,24),(7,20)]:
    best=None;cnt=0;arg=[]
    for v in itertools.combinations(range(1,H+1),m):
        if math.gcd(*v)!=1 or not dc(v,m): continue
        cnt+=1
        b,_=ml(list(v))
        if best is None or b<best: best=b;arg=[v]
        elif b==best and len(arg)<3: arg.append(v)
    Em=list(range(1,m))+[m*(m+1)]
    print(m,H,"DC primitive count",cnt,"min ML",best,"2/(2m+1)=",F(2,2*m+1),"ML(E_m)",ml(Em)[0],arg,flush=True)
