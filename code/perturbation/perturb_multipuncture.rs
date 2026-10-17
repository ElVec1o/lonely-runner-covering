// Round-4 verification + the multi-puncture form the referee's D7 requires.
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn stats(n:i128, m:&[i128], vs:&[i128])->(f64,f64){
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
  for &v in vs { sp.push(v); }
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &j in &sp { for i in 0..=j { iv.push((q(i*n-1,j*n), q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1); let mut meas=0.0f64;
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur);
      meas += gp.n as f64/gp.d as f64;
      if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur);
    meas += gp.n as f64/gp.d as f64;
    if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  (best.n as f64/best.d as f64, meas)
}
fn main(){
  println!("D3: claimed min 0.26831 over 21<=n<=44; referee says 0.207341 at n=32,M={{18,30}},v1=36");
  let (l,_)=stats(32,&[18,30],&[36]); let (e,_)=stats(32,&[18,30],&[]);
  let ceil=30.0/(32.0*36.0);
  println!("   ell'={:.8}  ell={:.8}  ceiling={:.8}  ratio={:.6}", l,e,ceil, l/(if e<ceil {e} else {ceil}));
  // full sweep 21..44, ALL M this time
  let mut w=f64::MAX; let mut wat=(0i128,0i128,0i128,0i128);
  for n in 21..=44i128 { for b1 in 1..n { for b2 in (b1+1)..n {
    let m=[b1,b2]; let (e,_)=stats(n,&m,&[]);
    let mut v1=n; while v1<=8*n {
      let (l,_)=stats(n,&m,&[v1]);
      let c=(n-2) as f64/((n*v1) as f64);
      let base=if e<c {e} else {c}; let r=l/base;
      if r<w { w=r; wat=(n,b1,b2,v1); } v1+=1; }
  }}}
  println!("   FULL sweep 21..44, all M, v1 in [n,8n]: min = {:.6} at {:?}", w, wat);
  println!();
  println!("D4: measure of residual at n=8, M={{2,6}}");
  for v1 in [8i128,24,1024,65536] { let (_,me)=stats(8,&[2,6],&[v1]);
    println!("   v1={:<6} measure={:.6}", v1, me); }
  println!();
  println!("D6: is ell(n,{{1,2}}) = 2/(3n)?");
  for n in [10i128,20,40,80] { let (e,_)=stats(n,&[1,2],&[]); println!("   n={:<4} ell*n={:.6}",n,e*n as f64); }
  println!();
  println!("D9: n=8, M={{3,5}} components");
  let (e,_)=stats(8,&[3,5],&[]); println!("   longest = {:.6}  (1/32 = {:.6})", e, 1.0/32.0);
  println!();
  println!("D7: MULTI-PUNCTURE.  min over (M,v1,v2) of ell'' / min(ell, (n-2)/(n*max(v1,v2)))");
  let mut w2=f64::MAX; let mut wat2=(0i128,0i128,0i128,0i128,0i128); let mut zero=0u64;
  for n in 9..=22i128 { for b1 in 1..n { for b2 in (b1+1)..n { for b3 in (b2+1)..n {
    let m=[b1,b2,b3]; let (e,_)=stats(n,&m,&[]);
    let mut v1=n; while v1<=3*n {
      let mut v2=n; while v2<=3*n {
        if v2!=v1 {
          let (l,_)=stats(n,&m,&[v1,v2]);
          if l==0.0 { zero+=1; }
          let mx=if v1>v2 {v1} else {v2};
          let c=(n-2) as f64/((n*mx) as f64);
          let base=if e<c {e} else {c};
          let r=l/base;
          if r<w2 { w2=r; wat2=(n,b1,b2,b3,v1); }
        }
        v2+=3; }
      v1+=3; }
  }}}}
  println!("   k=3, 9<=n<=22, all M, v1,v2 in [n,3n]: min = {:.6} at (n,M,v1)={:?}", w2, wat2);
  println!("   cases with no positive-length component: {}", zero);
}
