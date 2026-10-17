// Falsification search: for k=2, does a covering R = {v1,v2} exist?
// A covering R means U(n,M) is contained in B_{v1} ∪ B_{v2}, i.e. NO lonely time,
// i.e. a counterexample to the Lonely Runner Conjecture at n runners.
// Every bound used is rigorous:
//   * v1 = min R <= 2k/(ell (n-2k)) = 4/(ell (n-4))          [Covering Lemma]
//   * a connected set inside B_v lies in ONE constituent interval, so a component
//     of the residual of length L forces v2 < 2/(L n)          [connectivity]
// Exact i128 rational arithmetic throughout; no floating point is load-bearing.
#[derive(Clone,Copy,Debug)] struct Q{n:i128,d:i128}
fn g(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {g(b,a%b)} }
fn q(n:i128,d:i128)->Q{ let s=if d<0 {-1} else {1}; let (n,d)=(n*s,d*s);
  let k=g(n.abs(),d); if k==0 {Q{n:0,d:1}} else {Q{n:n/k,d:d/k}} }
fn cmp(a:Q,b:Q)->std::cmp::Ordering{ (a.n*b.d).cmp(&(b.n*a.d)) }
fn sub(a:Q,b:Q)->Q{ q(a.n*b.d-b.n*a.d, a.d*b.d) }

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
fn subsets2(n:i128, mut f:impl FnMut(i128,i128)){
  for b1 in 1..n { for b2 in (b1+1)..n { f(b1,b2); } } }


/// Can a single v2 cover a residual that is only isolated points?
/// Each point p/q needs ||v2 p/q|| < 1/n, a condition on v2 mod q. Scan one period
/// of Q = lcm(q_i). Returns Some(v2 class) if one works, None if none does,
/// or Err via the cap flag if Q exceeds the cap.
fn cover_isolated(n:i128, pts:&[Q], cap:i128)->(bool,bool){
  let mut qq:i128=1;
  for p in pts { let d=p.d; let gg=g(qq,d); qq = qq/gg*d; if qq>cap { return (false,true); } }
  for r in 0..qq {
    let mut ok=true;
    for p in pts {
      // ||r * p|| < 1/n  where p = p.n/p.d, and p.d | qq
      let num = (r % p.d) * p.n % p.d;          // (r*p) mod 1, as num/p.d
      let dist = std::cmp::min(num, p.d-num);   // ||.|| = dist/p.d
      if dist * n >= p.d { ok=false; break; }
    }
    if ok { return (true,false); }
  }
  (false,false)
}


/// CLASSIFICATION OF TIGHT MODIFICATIONS.
///
/// V is tight when LR(V) = 1/n exactly, i.e. no t has ||v t|| > 1/n for every v in V.
/// So the object to cover is the STRICT uncovered region -- the positive-length components of
/// U(n,M) -- and the covering sets are the CLOSED bad sets {t : ||v t|| <= 1/n}.
///
/// The enumeration is finite for the same two reasons as the counterexample search, since the
/// Covering Lemma assumes LR(V) <= 1/n and therefore covers the tight case too:
///   * min R <= 2k/(ell (n-2k));
///   * the closed bad intervals of v are disjoint when n > 2, so a connected residual piece of
///     length L lies in one of them, forcing v < 2/(Ln).
fn strip_closed(iv:&[(Q,Q)], n:i128, v:i128)->Vec<(Q,Q)>{
  let mut out=Vec::new();
  for &(l,r) in iv {
    let zlo = ((l.n as i128)*v*n - l.d) / (l.d*n) - 2;
    let zhi = ((r.n as i128)*v*n + r.d) / (r.d*n) + 2;
    let mut segs=vec![(l,r)];
    let mut z=zlo;
    while z<=zhi {
      let (bl,br)=(q(z*n-1,v*n), q(z*n+1,v*n));
      let mut nxt=Vec::new();
      for (sl,sr) in segs {
        // CLOSED removal: touching at an endpoint removes that endpoint
        if cmp(br,sl)==std::cmp::Ordering::Less || cmp(bl,sr)==std::cmp::Ordering::Greater {
          nxt.push((sl,sr)); continue; }
        if cmp(bl,sl)==std::cmp::Ordering::Greater { nxt.push((sl,bl)); }
        if cmp(br,sr)==std::cmp::Ordering::Less    { nxt.push((br,sr)); }
      }
      segs=nxt; z+=1;
    }
    out.extend(segs);
  }
  // the strict region is open: degenerate pieces are not part of it
  out.into_iter().filter(|&(l,r)| cmp(l,r)!=std::cmp::Ordering::Equal).collect()
}

fn strict_region(n:i128,m:&[i128])->Vec<(Q,Q)>{
  uncovered(n,m).into_iter().filter(|&(l,r)| cmp(l,r)!=std::cmp::Ordering::Equal).collect()
}

struct T{ n:i128, capped:u64, tests:u128, hit:Option<Vec<i128>> }

fn cover_tight(c:&mut T, res:&[(Q,Q)], rem:usize, chosen:&mut Vec<i128>)->bool{
  if res.is_empty() { c.hit=Some(chosen.clone()); return true; }
  if rem==0 { return false; }
  let n=c.n;
  let lr=longest(res);
  if lr.n==0 { return false; }               // cannot happen: degenerates already dropped
  let vb=(2*lr.d)/(lr.n*n);
  if vb > 5_000_000 { c.capped+=1; return false; }
  let mut v=n;
  while v<=vb {
    if !chosen.contains(&v) {
      c.tests+=1;
      let nxt=strip_closed(res,n,v);
      chosen.push(v);
      if cover_tight(c,&nxt,rem-1,chosen) { chosen.pop(); return true; }
      chosen.pop();
    }
    v+=1;
  }
  false
}

fn subsets_k(n:i128,k:usize, f:&mut impl FnMut(&[i128])){
  let cand:Vec<i128>=(1..n).collect(); let cl=cand.len();
  if k>cl {return;}
  let mut idx:Vec<usize>=(0..k).collect();
  loop{ let m:Vec<i128>=idx.iter().map(|&i| cand[i]).collect(); f(&m);
    let mut p=k; let mut done=true;
    while p>0 { p-=1; if idx[p]!=p+cl-k { idx[p]+=1; for z in (p+1)..k {idx[z]=idx[z-1]+1;} done=false; break; } }
    if done {break;} } }

fn main(){
  use std::io::Write;
  let a:Vec<String>=std::env::args().collect();
  let k:usize  = a.get(1).and_then(|s|s.parse().ok()).unwrap_or(2);
  let nlo:i128 = a.get(2).and_then(|s|s.parse().ok()).unwrap_or(5);
  let nhi:i128 = a.get(3).and_then(|s|s.parse().ok()).unwrap_or(40);
  let ckpt:String = a.get(4).cloned()
    .unwrap_or_else(|| format!("tight_k{}_{}_{}.ckpt", k, nlo, nhi));
  println!("== classification of TIGHT {}-speed modifications, {} <= n <= {} ==", k, nlo, nhi);
  println!("   no cap on the inserted speeds; the Covering Lemma bounds min R");
  println!("   checkpoint: {}\n", ckpt);
  let kk=k as i128;
  let (mut gt,mut gc):(u128,u64)=(0,0);
  let mut found:Vec<String>=Vec::new();
  let mut start_n = nlo;

  // ---- resume from checkpoint if one matches this run ----
  if let Ok(txt)=std::fs::read_to_string(&ckpt) {
    let mut lines=txt.lines();
    if let Some(hdr)=lines.next() {
      let f:Vec<&str>=hdr.split_whitespace().collect();
      if f.len()>=6 && f[0]=="CKPT" && f[1]==k.to_string()
         && f[2]==nlo.to_string() && f[3]==nhi.to_string() {
        let done:i128=f[4].parse().unwrap_or(nlo-1);
        gt=f[5].parse().unwrap_or(0);
        gc=f.get(6).and_then(|x|x.parse().ok()).unwrap_or(0);
        for l in lines { if !l.is_empty() { found.push(l.to_string()); } }
        start_n=done+1;
        println!("   RESUMED from checkpoint: n <= {} already done, {} found\n", done, found.len());
      }
    }
  }

  // work model: enumeration cost at n grows like C(n-1,k)*n, used only for the ETA
  let work=|n:i128|->f64{
    let mut c=1.0f64;
    for i in 0..kk { c *= ((n-1-i) as f64)/((i+1) as f64); }
    c*(n as f64)
  };
  let total:f64=(nlo..=nhi).filter(|n| 2*kk < *n).map(&work).sum();
  let mut done_work:f64=(nlo..start_n).filter(|n| 2*kk < *n).map(&work).sum();
  let t0=std::time::Instant::now();
  let w0=done_work;

  for n in start_n..=nhi {
    if 2*kk >= n { continue; }
    let mut ctx=T{n,capped:0,tests:0,hit:None};
    subsets_k(n,k,&mut |m:&[i128]|{
      let u=strict_region(n,m);
      let l=longest(&u);
      if l.n==0 { return; }
      let vb=(2*kk*l.d)/(l.n*(n-2*kk));
      let mut v1=n;
      while v1<=vb {
        let res=strip_closed(&u,n,v1);
        let mut chosen=vec![v1];
        ctx.tests+=1;
        if cover_tight(&mut ctx,&res,k-1,&mut chosen) {
          let mut r=ctx.hit.clone().unwrap(); r.sort();
          let mut v:Vec<i128>=(1..n).filter(|x| !m.contains(x)).collect();
          v.extend(r.iter());
          v.sort();
          found.push(format!("n={:<4} M={:?} R={:?}   V={:?}", n, m, r, v));
          ctx.hit=None;
        }
        v1+=1;
      }
    });
    gt+=ctx.tests; gc+=ctx.capped;
    done_work+=work(n);

    // ---- progress + ETA ----
    let el=t0.elapsed().as_secs_f64();
    let frac=(done_work-w0)/(total-w0).max(1.0);
    let eta=if frac>1e-9 { el*(1.0-frac)/frac } else { f64::NAN };
    println!("   n={:<4} done {}/{}  {:5.1}%  elapsed {:.0}s  ETA {:.0}s  tests {}  found {}",
             n, n-nlo+1, nhi-nlo+1, 100.0*(done_work/total), el, eta, gt, found.len());
    std::io::stdout().flush().ok();

    // ---- atomic checkpoint: temp file then rename ----
    let tmp=format!("{}.tmp", ckpt);
    let mut body=format!("CKPT {} {} {} {} {} {}\n", k, nlo, nhi, n, gt, gc);
    for f in found.iter() { body.push_str(f); body.push('\n'); }
    if std::fs::write(&tmp,&body).is_ok() { let _=std::fs::rename(&tmp,&ckpt); }
  }

  found.sort(); found.dedup();
  for f in found.iter() { println!("   TIGHT  {}", f); }
  println!("\n   {} tight configurations, {} enumeration steps, {} capped", found.len(), gt, gc);
  if gc>0 { println!("   WARNING: {} branches capped and UNDECIDED", gc); }
  std::io::stdout().flush().ok();
}
