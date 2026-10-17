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

/// Positive control: the stripper must actually be able to report a cover.
/// n=10, v=10: the bad interval around 3/10 is (29/100, 31/100).
fn selftest(){
  println!("== positive controls for `strip` ==");
  let full  = vec![(q(59,200), q(61,200))];        // [0.295,0.305], strictly inside (0.29,0.31)
  let r1 = strip(&full,10,10);
  println!("  contained interval fully removed : {}  (expect empty, got {} pieces)",
           r1.is_empty(), r1.len());
  let part  = vec![(q(28,100), q(30,100))];        // [0.28,0.30], overlaps on the right
  let r2 = strip(&part,10,10);
  let ok2 = r2.len()==1 && cmp(r2[0].0,q(28,100))==std::cmp::Ordering::Equal
                        && cmp(r2[0].1,q(29,100))==std::cmp::Ordering::Equal;
  println!("  partial overlap trimmed to [.28,.29]: {}  (got {:?})", ok2,
           r2.iter().map(|&(a,b)|(a.n,a.d,b.n,b.d)).collect::<Vec<_>>());
  let miss  = vec![(q(10,100), q(12,100))];        // disjoint from every bad interval of 10? 
  let r3 = strip(&miss,10,10);
  println!("  disjoint interval survives       : {}  ({} pieces)", !r3.is_empty(), r3.len());
  let two   = vec![(q(28,100), q(32,100))];        // straddles the whole bad interval
  let r4 = strip(&two,10,10);
  println!("  straddling interval splits in two: {}  ({} pieces)", r4.len()==2, r4.len());
  // isolated-point coverer must fire when a covering class exists
  let pts = vec![q(1,4)];                          // t=1/4; v2 ≡ 0 mod 4 gives ||v2 t||=0
  let (ok,_) = cover_isolated(10,&pts,1000);
  println!("  isolated point 1/4 is coverable  : {}  (expect true)", ok);
  let pts2 = vec![q(1,2)];                         // t=1/2; ||v 1/2|| is 0 or 1/2, 0 when v even
  let (ok2b,_) = cover_isolated(10,&pts2,1000);
  println!("  isolated point 1/2 is coverable  : {}  (expect true)", ok2b);
  println!();
}

fn main(){
  let nmax:i128 = std::env::args().nth(1).and_then(|s|s.parse().ok()).unwrap_or(30);
  let v2cap:i128 = std::env::args().nth(2).and_then(|s|s.parse().ok()).unwrap_or(2_000_000);
  let isocap:i128 = 5_000_000;
  selftest();
  println!("== k=2 falsification search, 9 <= n <= {} ==", nmax);
  println!("A COVER would be a counterexample to LRC at n runners.");
  println!("v1 bound from the Covering Lemma; v2 bound from connectivity. v2 cap {}.\n", v2cap);
  println!("{:>4} {:>7} {:>11} {:>12} {:>10} {:>10} {:>9}",
           "n","sets","(M,v1)","v2 tested","COVERS","iso cases","capped");
  let (mut gcov,mut gcap,mut giso):(u64,u64,u64)=(0,0,0);
  let mut grand:u128=0;
  for n in 9..=nmax {
    let (mut sets,mut pairs,mut v2t,mut covers,mut iso,mut capped)=(0u64,0u64,0u128,0u64,0u64,0u64);
    subsets2(n,|b1,b2|{
      sets+=1;
      let m=[b1,b2];
      let u=uncovered(n,&m);
      let l=longest(&u);
      if l.n==0 { return; }
      let vb = if n>4 { (4*l.d)/(l.n*(n-4)) } else { 0 };
      for v1 in n..=vb {
        pairs+=1;
        let res = strip(&u,n,v1);
        let lr = longest(&res);
        if res.is_empty() {
          covers+=1;
          println!("  *** COVER (v1 alone): n={} M={{{},{}}} v1={}", n,b1,b2,v1);
          continue;
        }
        if lr.n==0 {
          // residual is a finite set of points
          iso+=1;
          let pts:Vec<Q> = res.iter().map(|&(a,_)| a).collect();
          let (ok,cap) = cover_isolated(n,&pts,isocap);
          if cap { capped+=1; }
          else if ok {
            covers+=1;
            println!("  *** COVER (isolated): n={} M={{{},{}}} v1={} pts={}", n,b1,b2,v1,pts.len());
          }
          continue;
        }
        // v2 < 2/(lr * n)
        let vb2 = (2*lr.d)/(lr.n*n);
        let hi = if vb2 > v2cap { capped+=1; v2cap } else { vb2 };
        let mut v2=n;
        while v2 <= hi {
          if v2!=v1 {
            v2t+=1;
            if strip(&res,n,v2).is_empty() {
              covers+=1;
              println!("  *** COVER: n={} M={{{},{}}} R={{{},{}}}", n,b1,b2,v1,v2);
            }
          }
          v2+=1;
        }
      }
    });
    grand+=v2t; gcov+=covers; gcap+=capped; giso+=iso;
    println!("{:>4} {:>7} {:>11} {:>12} {:>10} {:>10} {:>9}",
             n,sets,pairs,v2t,covers,iso,capped);
  }
  println!("\ntotal v2 tested: {}", grand);
  println!("COVERS FOUND: {}   isolated-residual cases: {}   capped (UNDECIDED): {}", gcov, giso, gcap);
  if gcap>0 { println!("NOTE: {} branches hit a cap and are NOT decided.", gcap); }
}
