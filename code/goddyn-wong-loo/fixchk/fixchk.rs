// Exact integer arithmetic. Usage: fixchk primes | witA <rmin> <rmax> <mode>
use std::env;
fn is_prime(n:u64)->bool{ if n<2{return false;} let mut i=2; while i*i<=n { if n%i==0 {return false;} i+=1;} true }
fn gcd(a:u128,b:u128)->u128{ if b==0{a}else{gcd(b,a%b)} }
fn inv(a:u64,q:u64)->u64{ // a^{-1} mod q, gcd=1
  let (mut t,mut nt,mut r,mut nr)=(0i128,1i128,q as i128,(a%q) as i128);
  while nr!=0 { let qq=r/nr; let x=t-qq*nt; t=nt; nt=x; let y=r-qq*nr; r=nr; nr=y; }
  (((t%q as i128)+q as i128)%q as i128) as u64 }
// t=p/D ; true iff min over x in v (excluding index skip) of ||x t|| >= mu/Q
fn ok(v:&[u64],skip:usize,p:u128,d:u128,mu:u128,qq:u128)->bool{
  for (i,&x) in v.iter().enumerate(){ if i==skip {continue;}
    let a=(x as u128*p)%d; let m=a.min(d-a); if m*qq < mu*d {return false;} }
  true }
fn main(){
  let a:Vec<String>=env::args().collect();
  if a[1]=="primes" {
    let n=20_000_000usize; let mut s=vec![true;n+1]; s[0]=false; s[1]=false;
    let mut i=2; while i*i<=n { if s[i]{ let mut j=i*i; while j<=n { s[j]=false; j+=i; } } i+=1; }
    let mut pi=vec![0u32;n+1]; for k in 1..=n { pi[k]=pi[k-1]+s[k] as u32; }
    // window (b) of the prime-window lemma: primes q with floor(1.5 r) < q <= 2r, r<=n/2 (so 2r<=n)
    let mut bad4_even:Vec<usize>=vec![]; let mut bad4_all=0; let mut bad5_even=0;
    let mut min4=u32::MAX; let mut min4_arg=0;
    for r in 2..=n/2 { let c=pi[2*r]-pi[(3*r)/2];
      if c<4 { bad4_all=r; if r%2==0 {bad4_even.push(r);} }
      if c<5 && r%2==0 { bad5_even=r; }
      if r>=34 && r%2==0 && c<min4 {min4=c;min4_arg=r;} }
    println!("window (b) (floor(1.5r),2r], r<=10^7 (sieve to 2e7): even r with <4 primes: {:?}", bad4_even);
    println!("largest r (any parity) with <4: {}; largest even r with <5: {}; min count over even r in [34,1e7]: {} at r={}", bad4_all, bad5_even, min4, min4_arg);
    // window (a) of the prime-window lemma (floor(1.5n),2n-3], n<=10^7
    let mut bad3:Vec<usize>=vec![]; let mut min3=u32::MAX; let mut min3arg=0;
    for nn in 4..=n/2 { let c=pi[2*nn-3]-pi[(3*nn)/2]; if c<3 {bad3.push(nn);} if nn>=31 && c<min3 {min3=c;min3arg=nn;} }
    println!("window (a) (floor(1.5n),2n-3], n<=10^7: n in [4,1e7] with <3 primes: {:?}; min count for n>=31: {} at n={}", bad3,min3,min3arg);
    // same but 4 for sanity
    let mut b4=0; for nn in 31..=n/2 { let c=pi[2*nn-3]-pi[(3*nn)/2]; if c<4 {b4=nn;} } println!("largest n>=31 with <4 primes in window (a): {}", b4);
    // analytic bound D(n) (Dusart 5393/60184 forms), f64 evidence only, n=1e5..1e12 log grid
    let mut minD=f64::MAX; let mut nn=1.0e5f64; while nn<=1e15 { let l=(1.5*nn).ln(); let x=2.0*nn-3.0;
      let dd=x/(x.ln()-1.0) - 1.5*nn/(l-1.1); if dd<minD {minD=dd;} nn*=1.01; }
    println!("f64 evidence: min over log grid n in [1e5,1e15] of Dusart lower(2n-3) - upper(1.5n) = {:.1}", minD);
    // direct: n in [4e4,1e5] Dusart difference vs true count, and where D>=4 first holds
    let mut firstok=0usize; for nn in 40123..=20_000_000usize/2 { let l=(1.5*nn as f64).ln(); let x=2.0*nn as f64-3.0; let dd=x/(x.ln()-1.0)-1.5*nn as f64/(l-1.1); if dd<4.0 {firstok=nn;} }
    println!("largest n in [40123,1e7] where Dusart difference D(n)<4: {}", firstok);
    return; }
  if a[1]=="witA" {
    let rmin:u64=a[2].parse().unwrap(); let rmax:u64=a[3].parse().unwrap(); let proof=a[4]=="proof";
    let mut tot=0u64; let mut fail=0u64; let mut kinds=[0u64;4];
    let mut r=rmin; while r<=rmax { if r%2==0 {
      for mu in 2..=(r-1) {
        let qq=(mu*r+1) as u128; let mu128=mu as u128;
        let mut v:Vec<u64>=(1..r).collect(); v.push(r+1); v.push(mu*r);
        for idx in 0..v.len() { let j=v[idx]; if j==r+1 {continue;} tot+=1;
          let mut found=false;
          let j_is=|k:&str|->bool{ k=="" };
          let _=j_is;
          if j==mu*r { found=ok(&v,idx,1,r as u128,mu128,qq); if found {kinds[0]+=1;} }
          else if j>r/2 { // j<=r-1
            if (mu*r)%j!=0 { found=ok(&v,idx,1,j as u128,mu128,qq); if found {kinds[0]+=1;} }
            else { // t=1/j+1/(rQ)
              let d=(j as u128)*(r as u128)*qq; let p=(r as u128)*qq+j as u128; found=ok(&v,idx,p,d,mu128,qq); if found {kinds[1]+=1;} } }
          else { // j<=r/2 : prime q in window, proof exclusions
            let lo=(3*r)/2+1; let mut q=lo; while q<=2*r { 
              if is_prime(q) { let m1=mu*r-j; let m2=mu*r+j; if m1%q!=0 && m2%q!=0 && q!=r+j+1 {
                 let aa=inv(j,q); if ok(&v,idx,aa as u128,q as u128,mu128,qq){found=true;kinds[2]+=1;} break; } }
              q+=1; } }
          if !found && !proof { // fallback: any a/q, q in (r,4r], gcd(j,q)=1
            for q in (r+1)..=(4*r) { if gcd(j as u128,q as u128)==1 { let aa=inv(j,q); if ok(&v,idx,aa as u128,q as u128,mu128,qq){found=true;kinds[3]+=1;break;} } } }
          if !found { fail+=1; if fail<=15 {println!("NO WITNESS r={} mu={} j={}",r,mu,j);} }
        } } } r+=2; }
    println!("witA r in [{},{}] even, mu in 2..r-1, mode={}: removals {} (j != r+1), failures {}; witness kinds [1/r or 1/j, 1/j+delta, proof a/q, fallback a/q] = {:?}", rmin,rmax,a[4],tot,fail,kinds);
  }
}
