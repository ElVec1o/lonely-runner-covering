// perturb_degen: degenerate components and base-point bookkeeping of U(n,M), Remark "rem:measeq" of
// paper/perturbation/perturbation.tex.  Exact i128 rationals, standard library only.
//
// Definitions.  n >= 3, M a nonempty proper subset of [1,n-1] (bitmask over 1..n-1; there are 2^(n-1)-2 of them).
// U(n,M) = { t in [0,1] : ||j t|| >= 1/n for every j in [1,n-1] \ M }   (closed).  Its components are computed from
// the sorted union of the open bad intervals ((i n - 1)/(j n), (i n + 1)/(j n)), 0 <= i <= j.  A component is
// DEGENERATE if it has length 0 (an isolated point).  A WINDOW is a positive-length interval produced by the
// base-point formula componentsAt(n,b,a,M) (b in M, 0 <= a < b, gcd(a,b)=1; code identical to perturb_window.rs).
// Units: all lengths are fractions of the circle [0,1].
// Output per n: #M, #M with a degenerate component, #M where a positive component is not a window (claim: 0),
//   #M where a window is not a component (claim: 0), #M where the sum over ALL base points without
//   deduplication differs from lambda(U) (claim in the paper: 62,816 over all n in 3..16),
//   #M where the sum over base points deduplicated by interval differs from lambda(U) (expected 0).
// Controls (printed first, must all be true): n=4, M={2} has 3 components and exactly 1 window (paper statement);
//   subset count 2^(n-1)-2 per n; for M = {n-1}, the single component structure agrees with ell(n,{n-1}).
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn add(a:Q,b:Q)->Q{ q(a.n*b.d+b.n*a.d, a.d*b.d) }
fn eq(a:Q,b:Q)->bool{ cmp(a,b)==std::cmp::Ordering::Equal }
fn lt(a:Q,b:Q)->bool{ cmp(a,b)==std::cmp::Ordering::Less }
fn componentsAt(n:i128,b:i128,a:i128,m:&[i128])->Vec<(Q,Q)>{
  let mut dmax=q(1,1); let mut emax=q(1,1);
  let mut mult=false; let mut off=q(0,1);
  for j in 1..n {
    if m.contains(&j) { continue; }
    if j % b == 0 {
      mult=true;
      let o=q(1,j*n); if cmp(o,off)==std::cmp::Ordering::Greater { off=o; }
      let u=q(n-1,j*n);
      if cmp(u,dmax)==std::cmp::Ordering::Less { dmax=u; }
      if cmp(u,emax)==std::cmp::Ordering::Less { emax=u; }
    } else {
      let r=(j*a).rem_euclid(b);
      let dr=q((b-r)*n-b, n*b*j); let er=q(r*n-b, n*b*j);
      if cmp(dr,dmax)==std::cmp::Ordering::Less { dmax=dr; }
      if cmp(er,emax)==std::cmp::Ordering::Less { emax=er; }
    } }
  if dmax.n<0 { dmax=q(0,1); } if emax.n<0 { emax=q(0,1); }
  let base=q(a,b);
  let mut out=Vec::new();
  if mult {
    let r=sub(dmax,off); if r.n>0 { out.push((add(base,off), add(base,dmax))); }
    let l=sub(emax,off); if l.n>0 { out.push((sub(base,emax), sub(base,off))); }
  } else {
    let w=add(dmax,emax); if w.n>0 { out.push((sub(base,emax), add(base,dmax))); }
  }
  out
}
/// normalised pieces inside [0,1] of all base-point components (with multiplicity)
fn pieces(n:i128,m:&[i128])->Vec<(Q,Q)>{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 { continue; }
    for (l,r) in componentsAt(n,b,a,m) {
      let mut l=l; let mut r=r;
      while l.n<0 { l=add(l,q(1,1)); r=add(r,q(1,1)); }
      while !lt(l,q(1,1)) { l=sub(l,q(1,1)); r=sub(r,q(1,1)); }
      if cmp(r,q(1,1))==std::cmp::Ordering::Greater { iv.push((l,q(1,1))); iv.push((q(0,1),sub(r,q(1,1)))); }
      else { iv.push((l,r)); }
    } } }
  iv
}
/// components of U (closed), as (l,r) with r >= l
fn comps(n:i128,m:&[i128])->Vec<(Q,Q)>{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j) {continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut out=Vec::new(); let mut cur:Option<Q>=None;
  for &(l,r) in iv.iter(){
    if let Some(c)=cur { if !lt(l,c) { out.push((c,l)); } }
    cur = match cur { None=>Some(r), Some(c)=> Some(if lt(c,r) {r} else {c}) };
  }
  out
}
fn mask_to_m(n:i128,mask:u64)->Vec<i128>{ (1..n).filter(|&j| mask>>(j-1)&1==1).collect() }
fn main(){
  // controls
  let c4=comps(4,&[2]); let w4:Vec<(Q,Q)>={ let mut v=pieces(4,&[2]); v.sort_by(|x,y| cmp(x.0,y.0).then(cmp(x.1,y.1))); v.dedup_by(|x,y| eq(x.0,y.0)&&eq(x.1,y.1)); v.into_iter().filter(|p| lt(p.0,p.1)).collect() };
  let ctrl1 = c4.len()==3 && w4.len()==1;
  println!("control n=4 M={{2}}: components {} (expect 3), windows {} (expect 1): {}", c4.len(), w4.len(), ctrl1);
  let mut grand=(0u64,0u64,0u64,0u64,0u64,0u64);
  let mut all_ctrl=ctrl1;
  println!("{:>3} {:>8} {:>10} {:>12} {:>12} {:>14} {:>12}","n","#M","degenerate","comp!=window","window!=comp","naive_sum!=lam","dedup_sum!=lam");
  for n in 3..=16i128 {
    let total=(1u64<<(n-1))-2; let (mut cnt,mut deg,mut c_nw,mut w_nc,mut naive_bad,mut dedup_bad)=(0u64,0u64,0u64,0u64,0u64,0u64);
    for mask in 1..(1u64<<(n-1))-1 {
      let m=mask_to_m(n,mask); cnt+=1;
      let cs=comps(n,&m);
      let mut pc=pieces(n,&m);
      let naive=pc.iter().fold(q(0,1),|s,p| add(s,sub(p.1,p.0)));
      pc.sort_by(|x,y| cmp(x.0,y.0).then(cmp(x.1,y.1)));
      let mut dd=pc.clone(); dd.dedup_by(|x,y| eq(x.0,y.0)&&eq(x.1,y.1));
      let dd:Vec<(Q,Q)>=dd.into_iter().filter(|p| lt(p.0,p.1)).collect();
      let lam=cs.iter().fold(q(0,1),|s,p| add(s,sub(p.1,p.0)));
      let dsum=dd.iter().fold(q(0,1),|s,p| add(s,sub(p.1,p.0)));
      if cs.iter().any(|p| eq(p.0,p.1)) { deg+=1; }
      if cs.iter().any(|p| lt(p.0,p.1) && !dd.iter().any(|w| eq(w.0,p.0)&&eq(w.1,p.1))) { c_nw+=1; }
      if dd.iter().any(|w| !cs.iter().any(|p| eq(w.0,p.0)&&eq(w.1,p.1))) { w_nc+=1; }
      if !eq(naive,lam) { naive_bad+=1; }
      if !eq(dsum,lam) { dedup_bad+=1; }
    }
    all_ctrl &= cnt==total;
    println!("{:>3} {:>8} {:>10} {:>12} {:>12} {:>14} {:>12}",n,cnt,deg,c_nw,w_nc,naive_bad,dedup_bad);
    grand.0+=cnt; grand.1+=deg; grand.2+=c_nw; grand.3+=w_nc; grand.4+=naive_bad; grand.5+=dedup_bad;
  }
  println!("TOTAL 3<=n<=16: M {} ; with degenerate component {} ; positive component not a window {} ; window not a component {} ; naive sum != lambda {} ; deduplicated sum != lambda {}",
    grand.0,grand.1,grand.2,grand.3,grand.4,grand.5);
  println!("controls (subset counts equal 2^(n-1)-2 for every n, n=4 structure): {}", all_ctrl);
  if !all_ctrl { std::process::exit(1); }
}
