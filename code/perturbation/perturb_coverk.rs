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
/// TIGHT MODE. When set, `strip` removes the CLOSED bad set, so "covered" means
/// ||v t|| <= 1/n for every v, i.e. LR(V) <= 1/n. The known two-speed tight sets must then be
/// rediscovered. This is the end-to-end positive control for the whole pipeline: without it, any
/// bug making `can_cover` return false unconditionally would pass every other check and reproduce
/// the paper's result exactly.
static mut TIGHT: bool = false;
fn tight()->bool{ unsafe { TIGHT } }

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
        let disj = if tight() {
          cmp(br,sl)==std::cmp::Ordering::Less || cmp(bl,sr)==std::cmp::Ordering::Greater
        } else {
          cmp(br,sl)!=std::cmp::Ordering::Greater || cmp(bl,sr)!=std::cmp::Ordering::Less };
        if disj { nxt.push((sl,sr)); continue; }
        if cmp(bl,sl)==std::cmp::Ordering::Greater
           && !(tight() && cmp(sl,bl)==std::cmp::Ordering::Equal) { nxt.push((sl,bl)); }
        if cmp(br,sr)==std::cmp::Ordering::Less
           && !(tight() && cmp(br,sr)==std::cmp::Ordering::Equal) { nxt.push((br,sr)); }
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

/// Positive control: the stripper must actually be able to report a cover.
fn selftest(){
  println!("== positive controls for `strip` ==");
  let full  = vec![(q(59,200), q(61,200))];
  println!("  contained interval fully removed : {}", strip(&full,10,10).is_empty());
  let part  = vec![(q(28,100), q(30,100))];
  let r2 = strip(&part,10,10);
  println!("  partial overlap trimmed exactly  : {}",
     r2.len()==1 && cmp(r2[0].0,q(28,100))==std::cmp::Ordering::Equal
                 && cmp(r2[0].1,q(29,100))==std::cmp::Ordering::Equal);
  println!("  disjoint interval survives       : {}", !strip(&vec![(q(10,100),q(12,100))],10,10).is_empty());
  println!("  straddling interval splits in two: {}", strip(&vec![(q(28,100),q(32,100))],10,10).len()==2);
  filter_control();
  let (o1,_)=cover_isolated(10,&vec![q(1,4)],1000);
  let (o2,_)=cover_isolated(10,&vec![q(1,2)],1000);
  println!("  isolated 1/4 and 1/2 coverable   : {} {}", o1, o2);
  println!();
}

/// Does the residual still contain a point j/n with gcd(j,n)=1?
/// Those lie in U(n,M) for EVERY M (`mem_uncovered_of_coprime`), and a speed covering one
/// satisfies n | v (`dvd_of_covers_trivial`). Both are VERIFIED in PerturbDivis.lean, so
/// pruning on this is sound, not heuristic.
fn trivial_time_survives(n:i128, res:&[(Q,Q)])->bool{
  for j in 1..n { if g(j,n)!=1 {continue;}
    let p=q(j,n);
    for &(l,r) in res { if cmp(l,p)!=std::cmp::Ordering::Greater
                        && cmp(p,r)!=std::cmp::Ordering::Greater { return true; } } }
  false
}

/// Control for the filter: it must fire on the full uncovered region and stop firing
/// once a multiple of n has been applied.
fn filter_control(){
  let n=32i128; let m=[30i128];
  let u=uncovered(n,&m);
  let a = trivial_time_survives(n,&u);
  let b = trivial_time_survives(n,&strip(&u,n,32));   // 32 = n, must kill every j/n
  let c = trivial_time_survives(n,&strip(&u,n,60));   // 60, not a multiple of 32, must not
  println!("  divisibility filter: fires on U = {} (expect true)", a);
  println!("  silent after v=n=32                = {} (expect true)", !b);
  println!("  still fires after v=60             = {} (expect true)", c);
  if !(a && !b && c) { println!("  *** FILTER CONTROL FAILED - results are void ***"); }
}

struct Ctx{ n:i128, vcap:i128, isocap:i128, capped:u64, tests:u128, cover:Option<Vec<i128>> }

/// Can the residual be covered by `rem` further speeds, each >= n?
/// Bounds used, both rigorous:
///   * a connected piece of the residual must lie in ONE constituent interval of B_v,
///     so a component of length L forces v < 2/(Ln);
///   * a residual with no positive-length component is a finite set of rationals and
///     ||v p/q|| < 1/n depends only on v mod q, so one period decides it.
fn can_cover(c:&mut Ctx, res:&[(Q,Q)], rem:usize, chosen:&mut Vec<i128>)->bool{
  // In tight mode the region is the open (strict) one, so degenerate pieces are not in it.
  let owned:Vec<(Q,Q)>;
  let res:&[(Q,Q)] = if tight() {
    owned = res.iter().cloned().filter(|&(l,r)| cmp(l,r)!=std::cmp::Ordering::Equal).collect();
    &owned
  } else { res };
  if res.is_empty() { c.cover=Some(chosen.clone()); return true; }
  if rem==0 { return false; }
  let n=c.n;
  let lr=longest(res);
  if lr.n==0 {
    // finite point set
    if rem>=1 {
      let pts:Vec<Q>=res.iter().map(|&(a,_)| a).collect();
      let (ok,cap)=cover_isolated(n,&pts,c.isocap);
      if cap { c.capped+=1; return false; }
      if ok { chosen.push(-1); c.cover=Some(chosen.clone()); chosen.pop(); return true; }
    }
    return false;
  }
  // The bound 2/(ell n) is the CONNECTIVITY argument and is valid only when a single speed
  // remains: with two or more left, a residual component may be covered jointly and neither
  // speed need satisfy it. For rem >= 2 use the covering lemma (Theorem 1.7) on the residual,
  // min <= 2*rem/(ell (n - 2 rem)), which is uniform in the number of remaining speeds.
  let r=rem as i128;
  let vb = if r>=2 {
    if n-2*r<=0 { c.capped+=1; c.vcap } else { (2*r*lr.d)/(lr.n*(n-2*r)) }
  } else {
    (2*lr.d)/(lr.n*n)
  };
  let hi = if vb>c.vcap { c.capped+=1; c.vcap } else { vb };
  // Sound pruning, from the VERIFIED divisibility obstruction: at the last level the
  // remaining speed must cover every surviving j/n, so n divides it.
  // The pruning rests on ||v t|| < 1/n forcing n | v.  In TIGHT mode covered means
  // ||v t|| <= 1/n, where a surviving j/n can be covered AT EQUALITY by a v with n not
  // dividing it, so the pruning is UNSOUND there and must be switched off.
  let step = if !tight() && rem==1 && trivial_time_survives(n,res) { n } else { 1 };
  let mut v = if step==n { n } else { n };
  while v<=hi {
    if !chosen.contains(&v) {
      c.tests+=1;
      let nxt=strip(res,n,v);
      chosen.push(v);
      if can_cover(c,&nxt,rem-1,chosen) { chosen.pop(); return true; }
      chosen.pop();
    }
    v+=step;
  }
  false
}

fn subsets_k(n:i128,k:usize, f:&mut impl FnMut(&[i128])){
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

/// END-TO-END POSITIVE CONTROL. In tight mode the pipeline must rediscover the known two-speed
/// tight sets. If this prints nothing, the search is incapable of reporting a cover and every
/// null result from it is worthless.
/// STRICT-MODE control for the bug class tight mode cannot see.
/// Tight mode drops degenerate pieces on purpose. The main search's null results depend on
/// KEEPING them: at n=8, M={2,3} the times that survive R={11,13} are the isolated points
/// 1/8 and 7/8. An interval subtraction that dropped a degenerate endpoint would report a
/// spurious cover here -- a false counterexample to the conjecture -- and every tight-mode
/// control would still pass.
fn degenerate_retention_control(){
  println!("== STRICT-mode control: isolated survivors must be retained ==");
  let n=8i128; let m=[2i128,3];
  let u=uncovered(n,&m);
  let r1=strip(&u,n,11);
  let r2=strip(&r1,n,13);
  let want=[q(1,8), q(7,8)];
  let mut ok=true;
  for w in want.iter() {
    let present = r2.iter().any(|&(l,r)| cmp(l,*w)!=std::cmp::Ordering::Greater
                                      && cmp(*w,r)!=std::cmp::Ordering::Less);
    println!("   {}/{} survives R={{11,13}} : {}", w.n, w.d, present);
    if !present { ok=false; }
  }
  println!("   residual is nonempty (no spurious cover) : {}", !r2.is_empty());
  if !ok || r2.is_empty() {
    println!("   *** STRICT CONTROL FAILED: degenerate survivors are being dropped. ***");
    println!("   *** Every null result from the main search is void. ***");
  }
  println!();
}

fn endtoend_control(){
  println!("== END-TO-END positive control: rediscover the known tight sets (k=2) ==");
  unsafe { TIGHT = true; }
  let mut found:Vec<String>=Vec::new();
  for n in 5..=12i128 {
    subsets_k(n,2,&mut |m:&[i128]|{
      // strict region: positive-length components only
      let u:Vec<(Q,Q)>=uncovered(n,m).into_iter()
            .filter(|&(l,r)| cmp(l,r)!=std::cmp::Ordering::Equal).collect();
      if u.is_empty() { return; }
      let mut ctx=Ctx{n,vcap:200,isocap:100_000,capped:0,tests:0,cover:None};
      // in tight mode the covering-lemma bound does not apply, so scan a fixed window
      for v1 in n..=(4*n) {
        let res=strip(&u,n,v1);
        let mut chosen=vec![v1];
        if can_cover(&mut ctx,&res,1,&mut chosen) {
          if let Some(mut c)=ctx.cover.clone() {
            c.sort();
            found.push(format!("n={} M={:?} R={:?}",n,m,c)); }
          ctx.cover=None;
        }
      }
    });
  }
  unsafe { TIGHT = false; }
  found.sort(); found.dedup();
  for f in found.iter() { println!("   FOUND {}", f); }
  println!("   {} tight configurations rediscovered", found.len());
  if found.is_empty() {
    println!("   *** END-TO-END CONTROL FAILED: the search cannot report a cover. ***");
    println!("   *** Every null result from this program is void. ***");
  }
  println!();
}

fn main(){
  let a:Vec<String>=std::env::args().collect();
  let k:usize   = a.get(1).and_then(|s|s.parse().ok()).unwrap_or(2);
  let nlo:i128  = a.get(2).and_then(|s|s.parse().ok()).unwrap_or(9);
  let nhi:i128  = a.get(3).and_then(|s|s.parse().ok()).unwrap_or(30);
  let vcap:i128 = a.get(4).and_then(|s|s.parse().ok()).unwrap_or(2_000_000);
  selftest();
  degenerate_retention_control();
  endtoend_control();
  println!("== k={} falsification search, {} <= n <= {} ==", k, nlo, nhi);
  println!("A COVER would be a counterexample to LRC at n runners.\n");
  println!("{:>4} {:>9} {:>12} {:>14} {:>8} {:>8}","n","sets","(M,v1)","tests","COVERS","capped");
  let kk=k as i128;
  let (mut gc,mut gp,mut gt,mut gcap):(u64,u128,u128,u64)=(0,0,0,0);
  for n in nlo..=nhi {
    if 2*kk>=n { continue; }
    let (mut sets,mut pairs,mut covers)=(0u64,0u128,0u64);
    let mut ctx=Ctx{n,vcap,isocap:5_000_000,capped:0,tests:0,cover:None};
    subsets_k(n,k,&mut |m:&[i128]|{
      sets+=1;
      let u=uncovered(n,m);
      let l=longest(&u);
      if l.n==0 { return; }
      // Covering Lemma: min R <= 2k/(ell (n-2k))
      let vb=(2*kk*l.d)/(l.n*(n-2*kk));
      let mut v1=n;
      while v1<=vb {
        pairs+=1;
        let res=strip(&u,n,v1);
        let mut chosen=vec![v1];
        ctx.tests+=1;
        if can_cover(&mut ctx,&res,k-1,&mut chosen) {
          covers+=1;
          println!("  *** COVER n={} M={:?} R={:?}", n, m, ctx.cover.clone().unwrap());
          ctx.cover=None;
        }
        v1+=1;
      }
    });
    gc+=covers; gp+=pairs; gt+=ctx.tests; gcap+=ctx.capped;
    println!("{:>4} {:>9} {:>12} {:>14} {:>8} {:>8}", n, sets, pairs, ctx.tests, covers, ctx.capped);
  }
  println!("\nTOTAL  (M,v1): {}   tests: {}   COVERS: {}   capped: {}", gp, gt, gc, gcap);
  if gcap>0 { println!("WARNING: {} branches hit a cap and are UNDECIDED.", gcap); }
}
