// chkC.rs: exact-integer check of the explicit witness times for every deletion j != n-2 (strict > 1/(n-2)) and j = n-2 (>= 1/(n-2)),
// for synthetic (n,r,mu): s=n-r>=4, mu>=2, mu*s<=r+1 (consequence of the structure lemma), gcd(r,n-1)=1.  usage: chkC nmin nmax mumax
type U=u128;
fn g(a:U,b:U)->U{if b==0{a}else{g(b,a%b)}}
fn is_prime(x:U)->bool{ if x<2{return false;} let mut d=2; while d*d<=x{ if x%d==0{return false;} d+=1;} true }
fn inv(a:U,m:U)->U{ // a^{-1} mod m, gcd=1
  let (mut r0,mut r1)=(m as i128,(a%m) as i128); let (mut t0,mut t1)=(0i128,1i128);
  while r1!=0{ let q=r0/r1; let r2=r0-q*r1; r0=r1;r1=r2; let t2=t0-q*t1; t0=t1;t1=t2; }
  assert!(r0==1); (((t0%(m as i128))+(m as i128))%(m as i128)) as U }
fn main(){
 let a:Vec<String>=std::env::args().collect();
 let (n0,n1,mm):(U,U,U)=(a[1].parse().unwrap(),a[2].parse().unwrap(),a[3].parse().unwrap());
 let (mut triples,mut dels,mut fails)=(0u64,0u64,0u64);
 for n in n0..=n1{ for r in 2..n-3{ let s=n-r; if s<4{continue;} if g(r,n-1)!=1{continue;}
  for mu in 2..=mm{ if mu*s>r+1{continue;}
   triples+=1;
   let v:Vec<U>={let mut v:Vec<U>=(1..n).filter(|&x|x!=r).collect(); v.push(mu*r); v};
   let q0=n-2;
   for &j in &v{
     // witness t=p/D
     let (p,d,rule):(U,U,&str);
     if j==n-2 {p=1;d=n-2;rule="n-2";}
     else if j==n-1 {let q=2*r+s-1; p=inv(r,q); d=q; rule="n-1";}
     else if j==mu*r {p=1;d=r;rule="R0";}
     else if 2*j<=n { // R3: prime in (floor(1.5n), 2n-5]
        let mut found=None; let lo=(3*n)/2+1;
        for q in lo..=(2*n-5){ if !is_prime(q){continue;} let mr=mu*r; if (mr+j)%q==0||(mr-j)%q==0 {continue;} found=Some(q); break; }
        match found{ Some(q)=>{p=inv(j,q); d=q; rule="R3";} None=>{fails+=1; println!("NOPRIME n={} r={} mu={} j={}",n,r,mu,j); continue;} }
     } else if (mu*r)%j!=0 { p=1;d=j;rule="R2"; }
     else { let u=n-2; let den=j*2*mu*u*mu*r; p=2*mu*u*mu*r+j*(2*mu+1); d=den; rule="R4"; }
     dels+=1;
     let mut ok=true;
     for &x in &v{ if x==j{continue;} let rem=(x*p)%d; let m=if rem<d-rem{rem}else{d-rem};
        let good= if j==n-2 { m*q0>=d } else { m*q0>d };
        if !good{ok=false;break;} }
     if !ok{fails+=1; println!("FAIL n={} r={} mu={} j={} rule={}",n,r,mu,j,rule);}
   }
  }}}
 println!("triples {} deletions {} fails {}",triples,dels,fails);
}
