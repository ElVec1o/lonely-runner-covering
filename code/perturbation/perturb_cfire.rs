// perturb_cfire: how often condition (c) of Corollary "cor:uncond" holds (Remark "rem:cempty").
// Standard library only, exact u128 integer arithmetic.
// Condition (c): 2 <= b, 2b > n-1, with s = n-b and j0 = min{ j >= s : gcd(j,b) = 1 }, and
//     s (n-2k) (j0 + n - 1)  >  2 k b j0 (n-1),     for 1 <= k, 2k < n.
// Counted: triples (n,b,k) with 3 <= n <= NMAX, 1 <= k <= KMAX, 2 <= b <= n-1 satisfying 2b > n-1 and (c).
// Usage: perturb_cfire [NMAX] [KMAX]      defaults 2000 10
// Controls printed first: (1) the condition is evaluated a second time by a different expression
//   (cross-multiplied rational form: s(n-2k)/(2kbj0) > (n-1)/(j0+n-1)) and the two counts must agree;
//   (2) for k>=2 the inequality  s(n-2k)(j0+n-1) <= 2(n-4) j0 (n-1)  used in the paper's proof of emptiness is
//   checked on every triple that is evaluated (violations must be 0). The count at k=1 is the quantity quoted
//   in the Remark; the counts for 2<=k<=KMAX must be 0.
fn gcd(a:u128,b:u128)->u128{ if b==0 {a} else {gcd(b,a%b)} }
fn main(){
  let a:Vec<String>=std::env::args().collect();
  let nmax:u128=a.get(1).map(|x| x.parse().unwrap()).unwrap_or(2000);
  let kmax:u128=a.get(2).map(|x| x.parse().unwrap()).unwrap_or(10);
  let mut fires=vec![0u64;(kmax+1) as usize]; let mut fires2=vec![0u64;(kmax+1) as usize];
  let mut tested=vec![0u64;(kmax+1) as usize]; let mut proof_viol=0u64;
  for n in 3..=nmax { for b in 2..n { if 2*b<=n-1 { continue; }
    let s=n-b; let mut j0=s; while gcd(j0,b)!=1 { j0+=1; }
    for k in 1..=kmax { if 2*k>=n { break; }
      tested[k as usize]+=1;
      let lhs=s*(n-2*k)*(j0+n-1); let rhs=2*k*b*j0*(n-1);
      if lhs>rhs { fires[k as usize]+=1; }
      // second form: (s(n-2k)) * (j0+n-1) vs (2kbj0) * (n-1), compared via cross-multiplication of fractions
      let (x,y)=(s*(n-2*k), 2*k*b*j0); if x*(j0+n-1) > y*(n-1) { fires2[k as usize]+=1; }
      if k>=2 && lhs > 2*(n-4)*j0*(n-1) { proof_viol+=1; }
    } } }
  let t1:u64=fires.iter().sum(); let t2:u64=fires2.iter().sum();
  println!("NMAX={} KMAX={}", nmax,kmax);
  for k in 1..=kmax as usize { println!("k={:>2}: triples tested {:>10}, condition (c) holds {:>8}", k, tested[k], fires[k]); }
  println!("total over k=1: {}   total over 2<=k<=KMAX: {}", fires[1], t1-fires[1]);
  println!("control (two expressions agree): {}", t1==t2);
  println!("control (proof inequality of the Remark, k>=2): violations {}", proof_viol);
  if t1!=t2 || proof_viol>0 { std::process::exit(1); }
}
