import re,glob,os,sys
D=sys.argv[1].rstrip('/')+'/'   # usage: python3 -I check_layers.py <path to lean/LRSpectrumFull>
# theorem statements
thm={}
pat=re.compile(r'theorem (\w+) : ∀ b c d : ℕ, (\d+) ≤ b → b < (\d+) \+ (\d+) → b < c → c < d → (\d+) \+ b \+ c \+ d ≤ 195 →\s*Nat\.gcd \(Nat\.gcd (\d+) b\) \(Nat\.gcd c d\) = 1 → S4 !\[(\d+), b, c, d\]')
nm=0
for f in glob.glob(D+'S4R_*.lean')+glob.glob(D+'S4B_*.lean')+glob.glob(D+'S4Range*.lean'):
    s=open(f).read()
    for m in pat.finditer(s):
        n,lo,lo2,N,a1,a2,a3=m.groups()
        assert lo==lo2 and a1==a2==a3,(f,m.group(0))
        if n in thm: print("DUP",n,f)
        thm[n]=(os.path.basename(f),int(a1),int(lo),int(N)); nm+=1
print("range theorem statements parsed",nm)
# also check the theorem body passes the matching a: need proof uses rangeOK_sound with literal; skip
bad=0; tot_b=0
for a in range(1,48):
    f=D+'S4A_%02d.lean'%a
    s=open(f).read()
    m=re.search(r'theorem S4A_%d : ∀ b c d : ℕ, %d < b → b < c → c < d → %d \+ b \+ c \+ d ≤ 195 →\s*Nat\.gcd \(Nat\.gcd %d b\) \(Nat\.gcd c d\) = 1 → S4 !\[%d, b, c, d\]'%(a,a,a,a,a),s)
    assert m,(a,'statement')
    hc=re.search(r'have hcase : (.*?) := by omega',s,re.S).group(1)
    dis=re.findall(r'\((\d+) ≤ b ∧ b < (\d+) \+ (\d+)\)',hc)
    assert len(dis)==hc.count('∨')+1
    ivs=[(int(l),int(l2),int(n)) for l,l2,n in dis]
    pos=a+1; 
    for lo,lo2,n in ivs:
        assert lo==lo2
        if lo!=pos: print("GAP/OVERLAP a=%d expected %d got %d"%(a,pos,lo)); bad+=1
        pos=lo+n
    bmax=(192-a)//3
    # check feasibility: b max such that exists c=b+1,d=b+2
    bm2=max(b for b in range(a+1,200) if a+b+(b+1)+(b+2)<=195)
    assert bm2==bmax
    if pos-1!=bmax: print("END MISMATCH a=%d covered to %d, bmax %d"%(a,pos-1,bmax)); bad+=1
    # branches: names
    body=s.split('rcases hcase with')[1] if 'rcases hcase with' in s else s.split(':= by omega')[1]
    names=re.findall(r'exact (\w+) b c d h\.1 h\.2',body)
    if len(names)!=len(ivs): print("branch count mismatch",a); bad+=1
    for (lo,_,n),nmn in zip(ivs,names):
        if nmn not in thm: print("UNKNOWN thm",nmn); bad+=1; continue
        fn,aa,l,N=thm[nmn]
        if (aa,l,N)!=(a,lo,n): print("STATEMENT MISMATCH",a,lo,n,nmn,thm[nmn]); bad+=1
    # imports vs files used
    tot_b+=bmax-a
print("S4A files 1..47 checked; problems:",bad)
# a>=48
print("a>=48 infeasible:", all(4*a+6>195 for a in range(48,200)), " 4*47+6=",4*47+6," 4*48+6=",4*48+6)
# S4All coverage
cover=[]
for k in range(1,6):
    s=open(D+'S4All_%d.lean'%k).read()
    m=re.search(r'∀ a b c d : ℕ, (\d+) ≤ a → a ≤ (\d+)',s); lo,hi=int(m.group(1)),int(m.group(2))
    cases=[int(x) for x in re.findall(r'a = (\d+)',re.search(r'have hcase : (.*?) := by omega',s,re.S).group(1))]
    assert cases==list(range(lo,hi+1)),(k,cases)
    ex=re.findall(r'exact S4A_(\d+) b c d',s); assert [int(x) for x in ex]==cases
    cover+=cases
print("S4All a-coverage",cover==list(range(1,48)))
# S4Final
s=open(D+'S4Final.lean').read()
print(re.search(r'have hcase.*?:= by omega',s,re.S).group(0))
