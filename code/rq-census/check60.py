# independent cross-check, sum <= 60 only (bounded: ~ 40k sets). Different structure: permutations, direct definitions.
import itertools, math, sys
from math import gcd
MAXS=60
def nonres(s,a,b): return s!=a+b and a!=b+s and b!=a+s
hist={}; extra={'Q4':0,'QG5':0,'QG5bad':0,'T7':0,'T7n':0}
tot=0
for v in itertools.combinations(range(1,MAXS+1),4):
    if sum(v)>MAXS or math.gcd(math.gcd(v[0],v[1]),math.gcd(v[2],v[3]))!=1: continue
    tot+=1
    mss29=any(all(x%q==0 for x in t) for q in range(2,MAXS+1) for t in itertools.combinations(v,3))
    mss65=any((gcd(x,y)%2==1 and gcd(x,y)>=5) or (gcd(x,y)%2==0 and gcd(x,y)>=10) for x,y in itertools.combinations(v,2))
    r5=any(x%5==0 for x in v) and any(x%5!=0 for x in v)
    p3=any(sum(1 for x in v if x%q==0)==3 for q in range(2,MAXS+1))
    qg=False;t=False;q4=False;qg5=False;t7=False
    for p in itertools.permutations(v):
        s1,s2,a,b=p
        for q in range(4,MAXS+1):
            if s1%q==0 and s2%q==0 and gcd(a,q)==1 and gcd(b,q)==1:
                if q>=6: t=True
                if q>=7 and q!=8: t7=True
                if ((a-b)%q==0 or (a+b)%q==0) and nonres(s1,a,b) and nonres(s2,a,b):
                    qg=True
                    if q==4: q4=True
                    if q>=5: qg5=True
    g24=any(a%2==1 and b%2==1 and e%4==2 and s%4==0 and nonres(s,a,b) for (a,b,e,s) in itertools.permutations(v))
    m=(mss29)|(mss65<<1)|(r5<<2)|(p3<<3)|(qg<<4)|(t<<5)|(g24<<6)
    hist[m]=hist.get(m,0)+1
    extra['Q4']+=q4; extra['QG5']+=qg5; extra['T7']+=t7
    if qg5 and not (mss29 or mss65 or r5 or t): extra['QG5bad']+=1
    if t7 and not mss65: extra['T7n']+=1
print("TOTAL",tot)
for m in sorted(hist): print("H",m,hist[m])
print("Q4",extra['Q4']);print("QG5",extra['QG5']);print("QG5_NOT_R5_MSS_T",extra['QG5bad']);print("T7",extra['T7']);print("T7_NOT_MSS65",extra['T7n'])
