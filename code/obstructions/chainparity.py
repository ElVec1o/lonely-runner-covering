# Brute-force check: for odd q=2m+1, chains of the doubling graph on N={v<=2m: gcd(v,q)>1}.
# Claim: every chain has even length iff q is prime (N empty) or q=9.
import math, sys
def odd_chain_exists(q):
    m=(q-1)//2; top=2*m
    for s in range(1,top+1,2):          # chain starts: odd s, chain s,2s,4s,... <= 2m
        if math.gcd(s,q)>1:
            L=0; x=s
            while x<=top: L+=1; x*=2
            if L%2==1: return True
    return False
def is_prime(n): return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
Q=int(sys.argv[1]) if len(sys.argv)>1 else 20001
bad=[]
for q in range(3,Q+1,2):
    allEven = not odd_chain_exists(q)
    pred = is_prime(q) or q==9
    if allEven!=pred: bad.append(q)
print("q range 3..%d odd; mismatches with prediction (prime or 9): %s"%(Q,bad))
