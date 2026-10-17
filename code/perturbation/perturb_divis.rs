// Correct refined bound: compute the ACTUAL window at a/b by minimising over every present speed,
// rather than assuming the r = b-1 class binds.
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }
fn add(a:Q,b:Q)->Q{ q(a.n*b.d+b.n*a.d, a.d*b.d) }
fn ell(n:i128, m:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j) {continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut best=Q{n:0,d:1}; let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { let gp=sub(l,cur);
      if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { let gp=sub(one,cur);
    if cmp(gp,best)==std::cmp::Ordering::Greater {best=gp;} }
  best
}
/// exact window length at base point a/b, over present speeds (j not in M)
fn window(n:i128,b:i128,a:i128,m:&[i128])->Q{
  let mut dmax=q(1,1); let mut emax=q(1,1);       // right and left half-widths
  let mut mult=false; let mut off=q(0,1);          // offset forced by present multiples
  for j in 1..n {
    if m.contains(&j) { continue; }
    if j % b == 0 {
      mult=true;
      let o=q(1,j*n); if cmp(o,off)==std::cmp::Ordering::Greater { off=o; }
      let u=q(n-1,j*n); if cmp(u,dmax)==std::cmp::Ordering::Less { dmax=u; }
      if cmp(u,emax)==std::cmp::Ordering::Less { emax=u; }
    } else {
      let r=(j*a).rem_euclid(b);
      let dr=q((b-r)*n-b, n*b*j);                  // ((b-r)/b - 1/n)/j
      let er=q(r*n-b, n*b*j);                      // (r/b - 1/n)/j
      if cmp(dr,dmax)==std::cmp::Ordering::Less { dmax=dr; }
      if cmp(er,emax)==std::cmp::Ordering::Less { emax=er; }
    }
  }
  if dmax.n<0 { dmax=q(0,1); } if emax.n<0 { emax=q(0,1); }
  if mult {
    let r1=sub(dmax,off); let r2=sub(emax,off);
    let best=if cmp(r1,r2)==std::cmp::Ordering::Greater {r1} else {r2};
    if best.n<0 { q(0,1) } else { best }
  } else { add(dmax,emax) }
}
/// window with the Lean hypothesis delta_1 <= 1/(n b) enforced
fn windowLean(n:i128,b:i128,a:i128,m:&[i128])->Q{
  let mut dmax=q(1,n*b); let mut emax=q(1,n*b);
  let mut mult=false; let mut off=q(0,1);
  for j in 1..n {
    if m.contains(&j) { continue; }
    if j % b == 0 {
      mult=true;
      let o=q(1,j*n); if cmp(o,off)==std::cmp::Ordering::Greater { off=o; }
      let u=q(n-1,j*n); if cmp(u,dmax)==std::cmp::Ordering::Less { dmax=u; }
      if cmp(u,emax)==std::cmp::Ordering::Less { emax=u; }
    } else {
      let r=(j*a).rem_euclid(b);
      let dr=q((b-r)*n-b, n*b*j); let er=q(r*n-b, n*b*j);
      if cmp(dr,dmax)==std::cmp::Ordering::Less { dmax=dr; }
      if cmp(er,emax)==std::cmp::Ordering::Less { emax=er; }
    } }
  if dmax.n<0 { dmax=q(0,1); } if emax.n<0 { emax=q(0,1); }
  if mult { let r1=sub(dmax,off); let r2=sub(emax,off);
    let best=if cmp(r1,r2)==std::cmp::Ordering::Greater {r1} else {r2};
    if best.n<0 { q(0,1) } else { best } } else { add(dmax,emax) }
}
fn meas(n:i128,m:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j) {continue;} for i in 0..=j { iv.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  iv.sort_by(|x,y| cmp(x.0,y.0));
  let mut tot=q(0,1); let mut cur=q(0,1);
  for &(l,r) in iv.iter(){
    if cmp(l,cur)==std::cmp::Ordering::Greater { tot=add(tot,sub(l,cur)); }
    if cmp(r,cur)==std::cmp::Ordering::Greater {cur=r;} }
  let one=q(1,1);
  if cmp(one,cur)==std::cmp::Ordering::Greater { tot=add(tot,sub(one,cur)); }
  tot }
fn lbM(n:i128,m:&[i128])->Q{ let mut best=q(0,1);
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 {continue;}
    let w=window(n,b,a,m); if cmp(w,best)==std::cmp::Ordering::Greater {best=w;} } } best }
fn lbLean(n:i128,m:&[i128])->Q{ let mut best=q(0,1);
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 {continue;}
    let w=windowLean(n,b,a,m); if cmp(w,best)==std::cmp::Ordering::Greater {best=w;} } } best }

/// What `lonely_of_window` can actually consume at the base point a/b.
/// `hmul` forces delta_0 >= 1/(2bn) whenever b has ANY present multiple (it is stated with the
/// crude 1/(2bn), not the sharp 1/(jn)); `hdelta_0 : 0 <= delta_0` makes the window one-sided to
/// the right of a/b; `hdelta_1 : delta_1 <= 1/(nb)` caps the far end; `hnon` is the per-speed
/// upper edge. Returns delta_1 - delta_0, or 0 if that is negative.
fn windowLonelyOfWindow(n:i128,b:i128,a:i128,m:&[i128])->Q{
  let mut d1=q(1,n*b);                 // the hdelta_1 cap
  let mut has_mult=false;
  for j in 1..n {
    if m.contains(&j) { continue; }
    if j % b == 0 { has_mult=true; }
    else {
      let r=(j*a).rem_euclid(b);
      let dr=q((b-r)*n-b, n*b*j);      // ((b-r)/b - 1/n)/j
      if cmp(dr,d1)==std::cmp::Ordering::Less { d1=dr; }
    } }
  let d0 = if has_mult { q(1,2*b*n) } else { q(0,1) };
  let w=sub(d1,d0);
  if w.n<0 { q(0,1) } else { w }
}

/// `lonely_of_criterion_c'`: regime n <= 2b, two-sided window with the true j0 and j1.
/// Criterion: (2+4/n) k b j0 j1 < (n-b)(j0+j1)(n-2k).
fn criterionCPrime(n:i128,k:i128,m:&[i128])->bool{
  for &b in m {
    if 2*b < n || b < 1 || b >= n { continue; }
    for a in 1..b { if g(a,b)!=1 { continue; }
      // unique j in [n-b, n) with (j a) % b = b-1, resp. = 1
      let (mut j0,mut j1)=(0i128,0i128);
      for j in (n-b).max(1)..n {
        let r=(j*a).rem_euclid(b);
        if r==b-1 { j0=j; }
        if r==1   { j1=j; } }
      if j0==0 || j1==0 { continue; }
      // (2n+4) k b j0 j1 < n (n-b)(j0+j1)(n-2k)
      if (2*n+4)*k*b*j0*j1 < n*(n-b)*(j0+j1)*(n-2*k) { return true; } } }
  false
}

/// `lonely_of_one_mem`: 1 in M and (2+4/n) k < (1/(2n)) (n-2k) n, i.e. n > (6+8/n) k.
fn criterionOneMem(n:i128,k:i128,m:&[i128])->bool{
  m.contains(&1) && (2*n+4)*k*2 < n*(n-2*k)
}

/// The union of everything the Lean development certifies.
fn leanCertifies(n:i128,k:i128,m:&[i128])->bool{
  if criterionOneMem(n,k,m) { return true; }
  if criterionCPrime(n,k,m) { return true; }
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 { continue; }
    let w=windowLonelyOfWindow(n,b,a,m);
    // (2+4/n) k < w (n-2k) n   <=>   (2n+4) k < w (n-2k) n^2
    if w.n*(n*n*(n-2*k)) > (2*n+4)*k*w.d { return true; } } }
  false
}

/// All components of U(n,M) adjacent to the base point a/b, as exact intervals.
/// When b has a present multiple, a/b itself is NOT uncovered and there are TWO components
/// adjacent to it, one on each side; `window` returns only the longer, which is right for ell but
/// wrong for the measure. This returns every one of them.
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

/// Total measure predicted by the base points: every component, deduplicated, summed.
/// Intervals are normalised into [0,1) and split where they wrap.
fn measFromBasePoints(n:i128,m:&[i128])->Q{
  let mut iv:Vec<(Q,Q)>=Vec::new();
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 { continue; }
    for (l,r) in componentsAt(n,b,a,m) {
      // normalise: shift so that l is in [0,1)
      let mut l=l; let mut r=r;
      while l.n<0 { l=add(l,q(1,1)); r=add(r,q(1,1)); }
      while cmp(l,q(1,1))!=std::cmp::Ordering::Less { l=sub(l,q(1,1)); r=sub(r,q(1,1)); }
      if cmp(r,q(1,1))==std::cmp::Ordering::Greater {
        iv.push((l,q(1,1))); iv.push((q(0,1),sub(r,q(1,1))));
      } else { iv.push((l,r)); }
    } } }
  // deduplicate exactly, then sum lengths of the union
  iv.sort_by(|x,y| cmp(x.0,y.0).then(cmp(x.1,y.1)));
  iv.dedup_by(|x,y| cmp(x.0,y.0)==std::cmp::Ordering::Equal && cmp(x.1,y.1)==std::cmp::Ordering::Equal);
  let mut tot=q(0,1); let mut cur=q(-1,1);
  let mut hi=q(-1,1);
  for &(l,r) in iv.iter(){
    if cmp(l,hi)==std::cmp::Ordering::Greater { // disjoint from the run so far
      if hi.n> -1 || cur.n> -1 { }
      tot=add(tot,sub(r,l)); hi=r;
    } else {
      if cmp(r,hi)==std::cmp::Ordering::Greater { tot=add(tot,sub(r,hi)); hi=r; }
    }
    let _=cur;
  }
  tot
}


/// U(n,M) as a sorted list of disjoint CLOSED intervals in [0,1] (degenerate = isolated point).
fn uncovered(n:i128,m:&[i128])->Vec<(Q,Q)>{
  let mut bad:Vec<(Q,Q)>=Vec::new();
  for j in 1..n { if m.contains(&j) {continue;}
    for i in 0..=j { bad.push((q(i*n-1,j*n),q(i*n+1,j*n))); } }
  bad.sort_by(|x,y| cmp(x.0,y.0));
  let mut out=Vec::new(); let mut cur=q(0,1);
  for &(l,r) in bad.iter(){
    if cmp(l,cur)!=std::cmp::Ordering::Less { out.push((cur,l)); }
    if cmp(r,cur)==std::cmp::Ordering::Greater { cur=r; } }
  let one=q(1,1);
  if cmp(one,cur)!=std::cmp::Ordering::Less { out.push((cur,one)); }
  out
}
/// remove the open bad set of v from a list of closed intervals
fn strip(iv:&[(Q,Q)], n:i128, v:i128)->Vec<(Q,Q)>{
  let mut out=Vec::new();
  for &(l,r) in iv {
    // bad intervals of v meeting [l,r]: indices z with (z-1/n)/v < r and (z+1/n)/v > l
    let zlo = ((l.n as i128)*v*n - l.d) / (l.d*n) - 2;
    let zhi = ((r.n as i128)*v*n + r.d) / (r.d*n) + 2;
    let mut cuts:Vec<(Q,Q)>=Vec::new();
    let mut z=zlo; while z<=zhi { cuts.push((q(z*n-1,v*n), q(z*n+1,v*n))); z+=1; }
    let mut segs=vec![(l,r)];
    for (bl,br) in cuts {
      let mut nxt=Vec::new();
      for (sl,sr) in segs {
        if cmp(br,sl)!=std::cmp::Ordering::Greater || cmp(bl,sr)!=std::cmp::Ordering::Less {
          nxt.push((sl,sr)); continue; }                    // disjoint
        if cmp(bl,sl)==std::cmp::Ordering::Greater { nxt.push((sl,bl)); }
        if cmp(br,sr)==std::cmp::Ordering::Less    { nxt.push((br,sr)); }
      }
      segs=nxt;
    }
    out.extend(segs);
  }
  out
}
fn longest(iv:&[(Q,Q)])->Q{ let mut b=q(0,1);
  for &(l,r) in iv { let w=sub(r,l); if cmp(w,b)==std::cmp::Ordering::Greater {b=w;} } b }

fn lcm(a:i128,b:i128)->i128{ a/g(a,b)*b }

/// Regenerates every figure in the divisibility section.
/// Exact i128 rational arithmetic; every sweep below is exhaustive over its printed range.
fn main(){
  // (1) covering a base point a/b is EQUIVALENT to b | v, over an explicit range
  let (nlo,nhi,vmul)=(3i128,40i128,3i128);
  let (mut t1,mut bad1)=(0u64,0u64);
  for n in nlo..=nhi { for b in 1..n { for a in 1..b.max(2) {
    if g(a,b)!=1 { continue; }
    for v in 1..=(vmul*n) {
      t1+=1;
      let r=(v*a).rem_euclid(b);
      let covers = std::cmp::min(r,b-r)*n < b;      // ||v a/b|| < 1/n
      if covers != (v % b == 0) { bad1+=1; }
    } } } }
  println!("(1) covering a/b  <=>  b | v");
  println!("    range: {} <= n <= {}, 1 <= b < n, a a unit mod b, 1 <= v <= {}n",nlo,nhi,vmul);
  println!("    {} instances, {} violations", t1, bad1);

  // (2) covering j/n is EQUIVALENT to n | v
  let (mlo,mhi)=(3i128,60i128);
  let (mut t2,mut bad2)=(0u64,0u64);
  for n in mlo..=mhi { for j in 1..n { if g(j,n)!=1 {continue;}
    for v in 1..=(vmul*n) {
      t2+=1;
      let r=(v*j).rem_euclid(n);
      let covers = std::cmp::min(r,n-r) < 1;        // ||v j/n|| < 1/n
      if covers != (v % n == 0) { bad2+=1; }
    } } }
  println!("(2) covering j/n  <=>  n | v");
  println!("    range: {} <= n <= {}, j a unit mod n, 1 <= v <= {}n",mlo,mhi,vmul);
  println!("    {} instances, {} violations", t2, bad2);

  // (3) j/n lies in U(n,M) for EVERY M, including M = [n-1]
  let (mut t3,mut bad3)=(0u64,0u64);
  for n in 3..=14i128 {
    let cand:Vec<i128>=(1..n).collect();
    let total=1u32<<(cand.len() as u32);
    for mask in 0..total {
      let m:Vec<i128>=cand.iter().enumerate().filter(|(i,_)| mask>>i & 1==1).map(|(_,&v)| v).collect();
      for j in 1..n { if g(j,n)!=1 {continue;}
        t3+=1;
        for &q in cand.iter() { if m.contains(&q) {continue;}
          let r=(q*j).rem_euclid(n);
          if std::cmp::min(r,n-r)*n < n { bad3+=1; break; }   // ||q j/n|| < 1/n would refute
        } } } }
  println!("(3) j/n in U(n,M) for every M");
  println!("    range: 3 <= n <= 14, ALL 2^(n-1) subsets M, j a unit mod n");
  println!("    {} instances, {} violations", t3, bad3);

  // (4) Criterion D reach at k=1 over 2b >= n, against the measure criterion and the truth
  println!("(4) criterion D vs the measure criterion at k=1, over b with 2b >= n");
  println!("    {:>4} {:>6} {:>14} {:>13} {:>9}","n","b's","measure crit","criterion D","truth");
  for n in [20i128,26,32,38,44,50] {
    let (mut cnt,mut old,mut newc,mut truth)=(0u64,0u64,0u64,0u64);
    for b in 1..n { if 2*b < n {continue;} cnt+=1;
      let m=[b]; let u=ell(n,&m);
      if u.n==0 { continue; }
      if u.n*n*(n-2) > 2*u.d { old+=1; }
      if u.n*n*lcm(b,n) >= 2*u.d { newc+=1; }
      // TRUTH: does ANY admissible v actually cover ALL of U(n,{b})?
      // The window fitting is NOT sufficient: the isolated equality-locus points must go too.
      let bound=(2*u.d)/(u.n*(n-2));
      let uu=uncovered(n,&m);
      let mut cov=false;
      for v in n..=bound { if strip(&uu,n,v).is_empty() { cov=true; break; } }
      if !cov { truth+=1; }
    }
    let f=|x:u64| 100.0*x as f64/cnt as f64;
    println!("    {:>4} {:>6} {:>13.1}% {:>12.1}% {:>8.1}%",n,cnt,f(old),f(newc),f(truth));
  }
}
