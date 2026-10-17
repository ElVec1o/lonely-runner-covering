// D1: my two-puncture minimum used v1,v2 stepping by 3 -- a SAMPLE, not a sweep. Redo exhaustively.
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn longest(n:i128, m:&[i128], vs:&[i128])->f64{
  let mut sp:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
  for &v in vs { sp.push(v); }
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &j in &sp { for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur);
      if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur);
    if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  best.n as f64/best.d as f64
}
fn main(){
  // referee's specific point
  let e=longest(13,&[5,6,7],&[]); let l=longest(13,&[5,6,7],&[13,14]);
  let c=11.0/182.0; let base=if e<c {e} else {c};
  println!("referee point n=13 M={{5,6,7}} W={{13,14}}: ell={:.8} ceiling={:.8} ell_W={:.8} ratio={:.6}",
           e,c,l,l/base);
  // EXHAUSTIVE
  let mut w=f64::MAX; let mut wat=(0i128,0i128,0i128,0i128,0i128,0i128); let mut cnt=0u64;
  for n in 9..=22i128 { for b1 in 1..n { for b2 in (b1+1)..n { for b3 in (b2+1)..n {
    let m=[b1,b2,b3]; let e=longest(n,&m,&[]);
    for v1 in n..=3*n { for v2 in (v1+1)..=3*n {
      let l=longest(n,&m,&[v1,v2]); cnt+=1;
      let mx=if v1>v2 {v1} else {v2};
      let c=(n-2) as f64/((n*mx) as f64);
      let base=if e<c {e} else {c}; let r=l/base;
      if r<w { w=r; wat=(n,b1,b2,b3,v1,v2); }
    }}
  }}}}
  println!("EXHAUSTIVE two-puncture, 9<=n<=22, all M, all v1<v2 in [n,3n]: {} configs", cnt);
  println!("  min ratio = {:.6}  at (n,M,W) = ({}, {{{},{},{}}}, {{{},{}}})",
           w, wat.0, wat.1, wat.2, wat.3, wat.4, wat.5);
  println!("  3/22 = {:.6}", 3.0/22.0);
}
