# thin glue (text generation only): writes S4A_<aa>.lean and S4All_<k>.lean from the range-theorem statements in the module files
import re,glob,os,collections,sys
L=sys.argv[1].rstrip('/')+'/'   # usage: python3 layers.py <path to lean/LRSpectrumFull>; the generated files S4A_*.lean and S4All_*.lean are written there
os.chdir(L)
files=sorted(glob.glob('S4R_*.lean')+['S4Range5.lean','S4Range11b12n3.lean','S4Range22.lean','S4Range28.lean','S4Range41.lean']+glob.glob('S4B_*.lean'))
pat=re.compile(r'theorem (\S+) : ∀ b c d : ℕ, (\d+) ≤ b → b < \d+ \+ (\d+) → b < c → c < d → (\d+) \+')
per=collections.defaultdict(list)
for f in files:
    m=pat.search(open(f).read()); per[int(m.group(4))].append((int(m.group(2)),int(m.group(3)),m.group(1),f[:-5]))
def wr(fn,s):
    if os.path.exists(fn) and open(fn).read()==s: return
    open(fn,'w').write(s); print('WROTE',fn)
G=10; maxa=max(per)
for a in range(1,maxa+1):
    rs=sorted(per[a]); 
    s=f"/-\n# generated (s4_asm/layers.py): all b for a = {a}; modules: {', '.join(r[3] for r in rs)}\n-/\n"
    for r in rs: s+=f"import LRSpectrumFull.{r[3]}\n"
    s+="\nnamespace LRSpectrumFull\nnamespace D0\n\n"
    s+=f"theorem S4A_{a} : ∀ b c d : ℕ, {a} < b → b < c → c < d → {a} + b + c + d ≤ 195 →\n    Nat.gcd (Nat.gcd {a} b) (Nat.gcd c d) = 1 → S4 ![{a}, b, c, d] := by\n  intro b c d hb hbc hcd hs hg\n"
    disj=" ∨ ".join(f"({r[0]} ≤ b ∧ b < {r[0]} + {r[1]})" for r in rs)
    s+=f"  have hcase : {disj} := by omega\n"
    s+=("  have h := hcase\n" if len(rs)==1 else f"  rcases hcase with {' | '.join(['h']*len(rs))}\n")
    for r in rs: s+=f"  · exact {r[2]} b c d h.1 h.2 hbc hcd hs hg\n"
    s+=f"\n#print axioms S4A_{a}\n\nend D0\nend LRSpectrumFull\n"
    wr(f"S4A_{a:02d}.lean",s)
k=1;lo=1
while lo<=maxa:
    hi=min(lo+G-1,maxa)
    s=f"/-\n# generated (s4_asm/layers.py): all b, a in [{lo}, {hi}]\n-/\n"
    for a in range(lo,hi+1): s+=f"import LRSpectrumFull.S4A_{a:02d}\n"
    s+="\nnamespace LRSpectrumFull\nnamespace D0\n\n"
    s+=f"theorem S4All_{k} : ∀ a b c d : ℕ, {lo} ≤ a → a ≤ {hi} → a < b → b < c → c < d → a + b + c + d ≤ 195 →\n    Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 → S4 ![a, b, c, d] := by\n  intro a b c d h1 h2 hb hbc hcd hs hg\n"
    s+=f"  have hcase : {' ∨ '.join(f'a = {a}' for a in range(lo,hi+1))} := by omega\n  rcases hcase with {' | '.join(['rfl']*(hi-lo+1))}\n"
    for a in range(lo,hi+1): s+=f"  · exact S4A_{a} b c d hb hbc hcd hs hg\n"
    s+=f"\n#print axioms S4All_{k}\n\nend D0\nend LRSpectrumFull\n"
    wr(f"S4All_{k}.lean",s); k+=1; lo=hi+1
print("maxa",maxa,"groups",k-1)
