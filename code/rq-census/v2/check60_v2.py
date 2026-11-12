# independent cross-check, sum <= 60 (separate from main.rs): direct definitions over permutations; R7/Q3 written from the Lean hypotheses
import itertools, math, sys
from math import gcd
MAXS=60
def nonres(s,a,b): return s!=a+b and a!=b+s and b!=a+s
names=['R5','P3','QGEN','T','G24','R7','Q3']
tot=0; cls={n:0 for n in names}; mss=0; lean=0; lean2=0; res2=0; r7add=0; q3add=0; rqadd=0; only={n:0 for n in names}
split={}
for v in itertools.combinations(range(1,MAXS+1),4):
    if sum(v)>MAXS or math.gcd(math.gcd(v[0],v[1]),math.gcd(v[2],v[3]))!=1: continue
    tot+=1
    mss29=any(all(x%q==0 for x in t) for q in range(2,MAXS+1) for t in itertools.combinations(v,3))
    mss65=any((gcd(x,y)%2==1 and gcd(x,y)>=5) or (gcd(x,y)%2==0 and gcd(x,y)>=10) for x,y in itertools.combinations(v,2))
    f={}
    f['R5']=any(x%5==0 for x in v) and any(x%5!=0 for x in v)
    f['P3']=any(sum(1 for x in v if x%q==0)==3 for q in range(2,MAXS+1))
    qg=False;t=False
    for p in itertools.permutations(v):
        s1,s2,a,b=p
        for q in range(4,MAXS+1):
            if s1%q==0 and s2%q==0 and gcd(a,q)==1 and gcd(b,q)==1:
                if q>=6: t=True
                if ((a-b)%q==0 or (a+b)%q==0) and nonres(s1,a,b) and nonres(s2,a,b): qg=True
    f['QGEN']=qg; f['T']=t
    f['G24']=any(a%2==1 and b%2==1 and e%4==2 and s%4==0 and nonres(s,a,b) for (a,b,e,s) in itertools.permutations(v))
    # R7_partial from the Lean statement (abs form of resonance, integer divisibility form of ~)
    r7=False
    for s,a,b,c in itertools.permutations(range(4)):
        if v[s]%7==0 and all(v[i]%7!=0 for i in (a,b,c)):
            sim=lambda x,y:(x-y)%7==0 or (x+y)%7==0
            A=sim(v[a],v[b]) and sim(v[a],v[c])
            reson=(v[s]==v[b]+v[c] or v[s]==abs(v[b]-v[c]))
            B=sim(v[b],v[c]) and (not sim(v[a],v[b])) and not (reson and sim(v[b],3*v[a]))
            if A or B: r7=True
    f['R7']=r7
    q3=False
    for s1,s2,a,b in itertools.permutations(range(4)):
        if v[s1]%3==0 and v[s2]%3==0 and v[a]%3!=0 and v[b]%3!=0:
            ok=all(v[s]!=v[a]+v[b] and v[s]!=abs(v[a]-v[b]) for s in (s1,s2))
            if ok: q3=True
    f['Q3']=q3
    for n in names: cls[n]+=f[n]
    old=f['R5'] or f['P3'] or f['QGEN'] or f['T'] or f['G24']
    m=mss29 or mss65
    lean+=old; mss+=m
    new= old or f['R7'] or f['Q3']; lean2+=new
    if not new and not m:
        res2+=1
        reson=any(v[i]+v[j]==v[k] for i in range(4) for j in range(i+1,4) for k in range(4) if k not in (i,j)) or v[0]+v[1]==v[2]+v[3] or v[0]+v[2]==v[1]+v[3] or v[0]+v[3]==v[1]+v[2]
        ne=sum(1 for x in v if x%2==0); split[(reson,ne)]=split.get((reson,ne),0)+1
    if f['R7'] and not old: r7add+=1
    if f['Q3'] and not old: q3add+=1
    if (f['R7'] or f['Q3']) and not old: rqadd+=1
    for n in names:
        if f[n] and sum(f.values())==1: only[n]+=1
print("TOTAL",tot)
for n in names: print("CLASS",n,cls[n],"only_among_7_lean",only[n])
print("LEAN",lean,"MSS",mss,"LEAN2",lean2,"RESIDUAL2",res2)
print("R7_ADDED",r7add,"Q3_ADDED",q3add,"R7_OR_Q3_ADDED",rqadd)
print("RESID2 split (resonant,evens):",sorted(split.items()))
