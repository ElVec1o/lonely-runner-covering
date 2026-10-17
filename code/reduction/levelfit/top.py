import sys
from fractions import Fraction as Fr
exec(open('analyze.py').read().split("inclass=")[0])
inc=[d for d in R if d['cls']=='true' and d['res']!='false']
for key,f in [('q*/2p0',lambda d:2*d['p0']),('q*/q0',lambda d:d['q0']),('q*/3(m+1)',lambda d:3*(d['m']+1))]:
    print('==',key)
    for d in sorted(inc,key=lambda d:-Fr(d['qsq'],f(d)))[:8]:
        print(f"{float(Fr(d['qsq'],f(d))):.3f} m={d['m']} q*={d['qsq']} q0={d['q0']} p0={d['p0']} Qesc={d['Qesc']} nm={d['nm']} ms={d['ms']} idx={d['idx']} maxv={d['maxv']} {d['src']} {d['v']}")
