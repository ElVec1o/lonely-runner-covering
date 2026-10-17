// Falsification of G1 (prime filtering below level v with zero residues) and G2 (multiplier bookkeeping).
// Exact integers. p in {3,5,7}, m in 1..=3, N = p^(m+1).
fn nu(p:u64,x:u64)->u32{ if x==0 {return 0;} let mut x=x; let mut v=0; while x%p==0 {x/=p; v+=1;} v } // padicValNat convention nu(0)=0
fn rp(p:u64,x:u64)->u64{ if x==0 {return 0;} let v=nu(p,x); (x/p.pow(v))%p }
fn main(){
 let mut rng=0x2545F4914F6CDD1Du64; let mut rnd=|b:u64| { rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; rng%b };
 let (mut g1n,mut g1f,mut g2n,mut g2f)=(0u64,0u64,0u64,0u64);
 for &p in &[3u64,5,7] { for m in 1..=3u32 { let n=p.pow(m+1); let pm=p.pow(m); let q=|x:u64| (x%n)/pm%p;
  for _ in 0..20000 {
   // G1
   let v=rnd(m as u64+1) as u32; // 0..m ; v<=m
   let sz=1+rnd(6) as usize; let mut d=vec![]; let mut f:Vec<Vec<u64>>=vec![];
   let mut budget=vec![p-1; v as usize];
   for _ in 0..sz { // element: zero residue, or level < v
     if rnd(4)==0 || v==0 { let x=n*rnd(5); d.push(x); let mut fs=vec![]; for c in 1..p { if rnd(2)==0 {fs.push(c);} } f.push(fs); }
     else { let j=rnd(v as u64) as u32; let mut u=1+rnd(n); while u%p==0 {u=1+rnd(n);} let x=p.pow(j)*u + n*rnd(3);
       let b=&mut budget[j as usize]; let c=rnd(*b+1); *b-=c; let mut fs=vec![]; while (fs.len() as u64)<c { let y=rnd(p); if !fs.contains(&y) {fs.push(y);} } d.push(x); f.push(fs); } }
   g1n+=1; let md=p.pow(m+1-v);
   let ok=(0..n).filter(|l| l%md==1%md).any(|l| d.iter().zip(f.iter()).all(|(&x,fs)| !fs.contains(&q(l*x))));
   if !ok {g1f+=1; if g1f<5 {println!("G1 fail p={} m={} v={} D={:?} F={:?}",p,m,v,d,f);} }
   // G2: lam = (1+p^(m-j)k)*lamB, lamB = 1 mod p^(m+1-j); x at level j: q(lam x) = q(x)+k r(x); level > j fixed.
   let j=rnd(m as u64) as u32; let k=rnd(p); let lb=(1+p.pow(m+1-j)*rnd(n))%n; let lam=((1+p.pow(m-j)*k)%n)*lb%n;
   let mut u=1+rnd(n); while u%p==0 {u=1+rnd(n);} let x=p.pow(j)*u; g2n+=1;
   if q(lam*x) != (q(x)+k*rp(p,x))%p {g2f+=1;}
   let jj=j+1+rnd((m-j) as u64 +1) as u32; let y=p.pow(jj)*u; // level > j (maybe > m)
   if q(lam*y)!=q(y) {g2f+=1;}
   if rp(p,lam*x % n.max(1)) != rp(p,x) && (lam*x)%n!=0 { if rp(p,(lam*x)%n)!=rp(p,x%n) {g2f+=1000;} }
   // difference invariance: e = x - y at level >= v, lam = 1 mod p^(m+1-v)
   let vv=rnd(m as u64+1) as u32; let l2=(1+p.pow(m+1-vv)*rnd(n))%n; let a=rnd(n); let e=p.pow(vv)*rnd(n); let b=(a+n*n-e)%n; // a-b = e
   let dl=((l2*a)%n+n-(l2*b)%n)%n; let d0=(a+n-b)%n; if q(dl)!=q(d0) {g2f+=1000000;}
  } } }
 println!("G1: {} random instances, {} failures; G2: {} instances, {} failures", g1n,g1f,g2n,g2f);
}
