import sys,collections
from fractions import Fraction as Fr
rows=[l.rstrip('\n').split('\t') for f in (sys.argv[1:] or ['fit.tsv']) for l in open(f) if not l.startswith('src')]
H='src m v cls res U1 U2 ML qs Qesc Qx q0 p0 maxv mr lb nm pg gmax ms nrel idx sum'.split()
R=[]
for r in rows:
    d=dict(zip(H,r)); d['m']=int(d['m']); d['q0']=int(d['q0']); d['p0']=int(d['p0'])
    d['qsq']=int(d['qs'].split('/')[1]) if d['qs']!='none' else None
    d['qe']=int(d['Qesc'].split(':')[0]) if not d['Qesc'].startswith('>') else 999
    d['qxx']=int(d['Qx'].split(':')[0]) if not d['Qx'].startswith('>') else 999
    R.append(d)
inclass=[d for d in R if d['cls']=='true' and d['res'] in('true','na')]
print('rows',len(R),'class(DC,L1O,nSF)&residU(or na)',len(inclass), 'strict resid true',sum(d['res']=='true' for d in inclass))
print('no witness:',[ (d['src'],d['v']) for d in R if d['qsq'] is None])
def rep(name,f,S):
    rs=[(Fr(d['qsq'],f(d)),d) for d in S if d['qsq']]
    mx=max(rs,key=lambda x:x[0]); viol=[x for x in rs if x[0]>1]
    print(f'{name}: max ratio {mx[0]} ({float(mx[0]):.3f}) at {mx[1]["src"]} m={mx[1]["m"]} {mx[1]["v"]} qstar={mx[1]["qs"]}; violations(>1) {len(viol)}/{len(rs)}')
    return viol
for S,lab in [(R,'ALL'),(inclass,'CLASS')]:
    print('==',lab)
    rep('q*/((m+1)q0)',lambda d:(d['m']+1)*d['q0'],S)
    rep('q*/q0',lambda d:d['q0'],S)
    rep('q*/(2q0)',lambda d:2*d['q0'],S)
    rep('q*/(3q0)',lambda d:3*d['q0'],S)
    rep('q*/(2m+2)',lambda d:2*d['m']+2,S)
    rep('q*/(3(m+1))',lambda d:3*(d['m']+1),S)
    rep('q*/p0',lambda d:d['p0'],S)
    rep('q*/(2p0)',lambda d:2*d['p0'],S)
    rep('q*/(q0+p0)',lambda d:d['q0']+d['p0'],S)
    rep('q*/(2q0+m)',lambda d:2*d['q0']+d['m'],S)
    rep('q*/(q0+2m+2)',lambda d:d['q0']+2*d['m']+2,S)
    rep('Qesc/(m+1)',lambda d:1,[]) if False else None
    e=[(Fr(d['qe'],d['m']+1),d) for d in S]; mx=max(e,key=lambda x:x[0]); print('max Qesc/(m+1)',mx[0],float(mx[0]),mx[1]['src'],mx[1]['v'],mx[1]['Qesc'])
    e=[(Fr(d['qe'],d['q0']),d) for d in S]; mx=max(e,key=lambda x:x[0]); print('max Qesc/q0',mx[0],float(mx[0]),mx[1]['src'],mx[1]['v'])
    e=[(Fr(d['qxx'],d['m']+1),d) for d in S]; mx=max(e,key=lambda x:x[0]); print('max Qexact/(m+1)',mx[0],float(mx[0]),mx[1]['src'],mx[1]['v'],mx[1]['Qx'])
    print('Qesc>q* count',sum(d['qsq'] and d['qe']>d['qsq'] for d in S),'Qesc==q*',sum(d['qe']==d['qsq'] for d in S),'Qesc<q*',sum(d['qsq'] and d['qe']<d['qsq'] for d in S))
    print('Qexact<=m+1',sum(d['qxx']<=d['m']+1 for d in S),'/',len(S))
    # q* distribution by src
    c=collections.defaultdict(list)
    for d in S: c[d['src']].append(d)
    for k,L in c.items():
        print(f'  {k}: n={len(L)} q*/q0 max={max(Fr(d["qsq"],d["q0"]) for d in L if d["qsq"])} q* range {min(d["qsq"] for d in L if d["qsq"])}-{max(d["qsq"] for d in L if d["qsq"])} Qesc range {min(d["qe"] for d in L)}-{max(d["qe"] for d in L)} Qx max {max(d["qxx"] for d in L)} q0 set {sorted(set(d["q0"] for d in L))}')
