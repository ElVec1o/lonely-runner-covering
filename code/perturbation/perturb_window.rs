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

/// What `lonely_of_window` can consume AFTER the caps were removed: the sharp per-speed offset
/// delta_0 = max 1/(jn) over present multiples, and the far cap relaxed from 1/(nb) to 1/n.
/// Still one-sided, since hdelta_0 : 0 <= delta_0 keeps both ends right of a/b.
fn windowLeanSharp(n:i128,b:i128,a:i128,m:&[i128])->Q{
  let mut d1=q(1,n);                       // relaxed far cap
  let mut d0=q(0,1);
  for j in 1..n {
    if m.contains(&j) { continue; }
    if j % b == 0 {
      let o=q(1,j*n);                      // SHARP per-speed offset
      if cmp(o,d0)==std::cmp::Ordering::Greater { d0=o; }
    } else {
      let r=(j*a).rem_euclid(b);
      let dr=q((b-r)*n-b, n*b*j);
      if cmp(dr,d1)==std::cmp::Ordering::Less { d1=dr; }
    } }
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
/// `lonely_of_window_twosided`: when b has no present multiple the window straddles a/b and its
/// length is eps_m + eps_p, both minima over the present speeds, with the 1/n cap on each side.
fn windowLeanTwoSided(n:i128,b:i128,a:i128,m:&[i128])->Q{
  for j in 1..n { if !m.contains(&j) && j % b == 0 { return q(0,1); } }  // needs no present multiple
  let mut ep=q(1,n); let mut em=q(1,n);
  for j in 1..n { if m.contains(&j) { continue; }
    let r=(j*a).rem_euclid(b);
    let dr=q((b-r)*n-b, n*b*j); let el=q(r*n-b, n*b*j);
    if cmp(dr,ep)==std::cmp::Ordering::Less { ep=dr; }
    if cmp(el,em)==std::cmp::Ordering::Less { em=el; } }
  if ep.n<0 || em.n<0 { return q(0,1); }
  add(em,ep)
}

fn leanCertifiesFull(n:i128,k:i128,m:&[i128])->bool{
  if leanCertifiesSharp(n,k,m) { return true; }
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 { continue; }
    let w=windowLeanTwoSided(n,b,a,m);
    if w.n*(n*n*(n-2*k)) > (2*n+4)*k*w.d { return true; } } }
  false
}

fn leanCertifiesSharp(n:i128,k:i128,m:&[i128])->bool{
  if criterionOneMem(n,k,m) { return true; }
  if criterionCPrime(n,k,m) { return true; }
  for &b in m { for a in 0..b.max(1) { if g(a,b)!=1 { continue; }
    let w=windowLeanSharp(n,b,a,m);
    if w.n*(n*n*(n-2*k)) > (2*n+4)*k*w.d { return true; } } }
  false
}

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

/// iterate over every k-subset of [1,n)
fn subsets<F:FnMut(&[i128])>(n:i128,k:usize,mut f:F){
  let cand:Vec<i128>=(1..n).collect(); let cl=cand.len();
  if k>cl {return;}
  let mut idx:Vec<usize>=(0..k).collect();
  loop{
    let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect();
    f(&m);
    let mut p=k; let mut done=true;
    while p>0 { p-=1; if idx[p]!=p+cl-k { idx[p]+=1; for z in (p+1)..k {idx[z]=idx[z-1]+1;} done=false; break; } }
    if done {break;}
  }
}

fn main(){
  let cmdv:Vec<String>=std::env::args().collect();
  let cmd=cmdv.get(1).map(|x| x.as_str()).unwrap_or("all");

  if cmd=="exact" || cmd=="all" {
    // Theorem "exact formula": ell(n,M) = max over base points of the window. Exhaustive.
    println!("== exact formula: ell(n,M) == max_(b,a) w(n,b,a,M), exhaustive ==");
    println!("{:>2} {:>4} {:>9} {:>10} {:>8}","k","n","sets","equal","unsound");
    let mut grand=0u64;
    for k in 1..=4usize { for n in [16i128,20,24,28,32,36] {
      let (mut tt,mut eq,mut vi)=(0u64,0u64,0u64);
      subsets(n,k,|m|{ tt+=1; let e=ell(n,m); let l=lbM(n,m);
        match cmp(l,e){ std::cmp::Ordering::Equal=>eq+=1,
                        std::cmp::Ordering::Greater=>vi+=1, _=>{} } });
      grand+=tt;
      println!("{:>2} {:>4} {:>9} {:>9.2}% {:>8}",k,n,tt,100.0*eq as f64/tt as f64,vi);
    }}
    println!("total pairs (n,M) checked: {}", grand);
  }

  if cmd=="measure" || cmd=="all" {
    // Corollary: lambda(U(n,M)) <= 2|M|/n. Exhaustive, reports the extremal ratio.
    println!("\n== measure bound lambda(U) <= 2k/n, exhaustive ==");
    println!("{:>2} {:>4} {:>9} {:>16} {:>8}","k","n","sets","max ratio","viol");
    for k in 1..=3usize { for n in [16i128,22,28,34,40] {
      let (mut tt,mut vi)=(0u64,0u64); let mut worst=0.0f64; let mut wm=String::new();
      subsets(n,k,|m|{ tt+=1; let mu=meas(n,m); let bd=q(2*(k as i128),n);
        if cmp(mu,bd)==std::cmp::Ordering::Greater {vi+=1;}
        let r=(mu.n as f64/mu.d as f64)/(bd.n as f64/bd.d as f64);
        if r>worst {worst=r; wm=format!("{:?}",m);} });
      println!("{:>2} {:>4} {:>9} {:>15.4}  {:>7}   M={}",k,n,tt,worst,vi,wm);
    }}
  }

  if cmd=="measexact" || cmd=="all" {
    println!("== is lambda(U(n,M)) EXACTLY the sum of the base-point components? ==");
    println!("{:>2} {:>4} {:>8} {:>10} {:>8}","k","n","sets","equal","over");
    for k in 1..=3usize { for n in [12i128,16,20,24,28] {
      let (mut tt,mut eq,mut ov)=(0u64,0u64,0u64);
      subsets(n,k,|m|{ tt+=1; let a=meas(n,m); let b=measFromBasePoints(n,m);
        match cmp(b,a){ std::cmp::Ordering::Equal=>eq+=1,
                        std::cmp::Ordering::Greater=>ov+=1, _=>{} } });
      println!("{:>2} {:>4} {:>8} {:>9.2}% {:>8}",k,n,tt,100.0*eq as f64/tt as f64,ov);
    }}
  }

  if cmd=="leansharp" || cmd=="all" {
    println!("\n== Lean reach: before and after removing the two caps ==");
    for k in 1..=3usize {
      let (mut old,mut new,mut full,mut crit)=(Vec::new(),Vec::new(),Vec::new(),Vec::new());
      for n in [22i128,26,30,34,38,42] {
        let (mut tt,mut a1,mut a2,mut a3,mut a4)=(0u64,0u64,0u64,0u64,0u64); let kk=k as i128;
        subsets(n,k,|m|{ tt+=1;
          if leanCertifies(n,kk,m) {a1+=1;}
          if leanCertifiesSharp(n,kk,m) {a2+=1;}
          if leanCertifiesFull(n,kk,m) {a4+=1;}
          let e=ell(n,m);
          if e.n*(n*(n-2*kk)) > 2*kk*e.d {a3+=1;} });
        let f=|x:u64| 100.0*x as f64/tt as f64;
        old.push(f(a1)); new.push(f(a2)); full.push(f(a4)); crit.push(f(a3));
      }
      let j=|v:&Vec<f64>| v.iter().map(|x| format!("{:.2}",x)).collect::<Vec<_>>().join(", ");
      println!("  k={}  (n = 22, 26, 30, 34, 38, 42)", k);
      println!("     Lean, crude caps : {}", j(&old));
      println!("     Lean, caps removed: {}", j(&new));
      println!("     Lean, + two-sided : {}", j(&full));
      println!("     criterion ceiling : {}", j(&crit));
    }
  }

  if cmd=="leanreach" || cmd=="all" {
    println!("\n== what the Lean development actually certifies (exhaustive) ==");
    println!("union of lonely_of_window, lonely_of_criterion_c', lonely_of_one_mem");
    for k in 1..=3usize {
      let mut v=Vec::new();
      for n in [22i128,26,30,34,38,42] {
        let (mut tt,mut ok)=(0u64,0u64); let kk=k as i128;
        subsets(n,k,|m|{ tt+=1; if leanCertifies(n,kk,m) {ok+=1;} });
        v.push(100.0*ok as f64/tt as f64);
      }
      println!("  k={}  {}", k, v.iter().map(|x| format!("{:.2}",x)).collect::<Vec<_>>().join(", "));
    }
  }

  if cmd=="reach" || cmd=="all" {
    // Reach of: Thm 3.1 criterion / Cor (window) / what Lean certifies, old c=4 and new c=2+4/n.
    println!("\n== reach, exhaustive over all k-subsets ==");
    for k in 1..=3usize {
      let (mut c,mut w,mut le,mut ol)=(vec![],vec![],vec![],vec![]);
      for n in [22i128,26,30,34,38,42] {
        let (mut tt,mut ac,mut aw,mut al,mut ao)=(0u64,0u64,0u64,0u64,0u64);
        let kk=k as i128;
        subsets(n,k,|m|{ tt+=1;
          let e=ell(n,m); let ww=lbM(n,m); let l=lbLean(n,m);
          if e.n*(n*(n-2*kk)) > 2*kk*e.d {ac+=1;}
          if ww.n*(n*(n-2*kk)) > 2*kk*ww.d {aw+=1;}
          if l.n*(n*n*(n-2*kk)) > (2*n+4)*kk*l.d {al+=1;}
          if l.n*(n*(n-2*kk)) > 4*kk*l.d {ao+=1;} });
        let f=|x:u64| 100.0*x as f64/tt as f64;
        c.push(f(ac)); w.push(f(aw)); le.push(f(al)); ol.push(f(ao));
      }
      let j=|v:&Vec<f64>| v.iter().map(|x| format!("{:.2}",x)).collect::<Vec<_>>().join(", ");
      println!("k={}  (n = 22, 26, 30, 34, 38, 42)", k);
      println!("  Thm 3.1 criterion      : {}", j(&c));
      println!("  Cor (window formula)   : {}", j(&w));
      println!("  Lean, c = 2+4/n        : {}", j(&le));
      println!("  Lean, c = 4 (old)      : {}", j(&ol));
    }
  }
}
