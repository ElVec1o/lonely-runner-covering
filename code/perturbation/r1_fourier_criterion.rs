// Archive edit: the undecided branch prints the tuple (one added println); no other change to the original.
// Floating point (f64) throughout: the output is evidence, not proof.
// MULTI-MODE FOURIER criterion.
//   measure(T_S ∩ good_4) = (5/9)*mu + 2*Re sum_{m>0} ghat(m) * conj(F(m*v4)),
// where g = indicator of [2/9,7/9] (the GOOD phases) and F(k) = int_{T_S} e^{-2 pi i k t} dt.
// Truncating at M modes needs a tail bound: |F(k)| <= N/(pi*|k|) for a union of N intervals,
// and |ghat(m)| <= 1/(pi*m), so the tail is at most (N/(pi^2 v4)) * sum_{m>M} 2/m^2 <= 2N/(pi^2 v4 M).
// If the truncated value minus the tail bound is > 0, then T_S meets good_4: some component ESCAPES.
fn gcd(a:i64,b:i64)->i64{ if b==0 {a.abs()} else {gcd(b,a%b)} }
fn nid(x:f64)->f64{ let f=x-x.floor(); if f<1.0-f {f} else {1.0-f} }
fn components(v:&[i64], d:f64)->Vec<(f64,f64)>{
  let mut pts:Vec<f64>=vec![0.0,1.0];
  for &vi in v { let f=vi as f64;
    for k in 0..=vi { pts.push(k as f64/f + d/f); pts.push((k as f64+1.0)/f - d/f); } }
  pts.retain(|x| *x>=0.0 && *x<=1.0); pts.sort_by(|a,b| a.partial_cmp(b).unwrap());
  let ins=|t:f64|->bool{ v.iter().all(|&vi| nid((vi as f64)*t)>=d-1e-12) };
  let mut out=Vec::new(); let mut i=0;
  while i+1<pts.len(){ let (a,b)=(pts[i],pts[i+1]);
    if b-a>1e-12 && ins(0.5*(a+b)){ let mut j=i+1; let mut end=b;
      while j+1<pts.len() && ins(0.5*(pts[j]+pts[j+1])) { end=pts[j+1]; j+=1; }
      out.push((a,end)); i=j; } else { i+=1; } }
  out
}
fn main(){
  let d=2.0/9.0; let pi=std::f64::consts::PI; let tau=2.0*pi;
  let mm:i64=std::env::args().nth(1).and_then(|s|s.parse().ok()).unwrap_or(40);
  let (mut tot,mut dec,mut undec,mut viol)=(0u64,0u64,0u64,0u64);
  for v1 in 1..50i64 { for v2 in (v1+1)..120i64 {
    if gcd(v1,v2)!=1 {continue;}
    let v3=v1+v2;
    let comps=components(&[v1,v2,v3],d);
    if comps.len()<3 {continue;}
    let n=comps.len() as f64;
    let mu:f64=comps.iter().map(|(a,b)| b-a).sum();
    let ell=comps.iter().map(|(a,b)| b-a).fold(0.0f64,f64::max);
    let vmax=((4.0/9.0)/ell).floor() as i64;
    for v4 in (v3+1)..=vmax {
      if gcd(v1,v4)>2||gcd(v2,v4)>2||gcd(v3,v4)>2 {continue;}
      tot+=1;
      let f=v4 as f64;
      let mut acc = (5.0/9.0)*mu;
      for m in 1..=mm {
        let fm=m as f64; let k=fm*f;
        // ghat(m) = (e^{-2 pi i m 2/9} - e^{-2 pi i m 7/9}) / (2 pi i m)
        let (c1,s1)=((tau*fm*2.0/9.0).cos(), -(tau*fm*2.0/9.0).sin());
        let (c2,s2)=((tau*fm*7.0/9.0).cos(), -(tau*fm*7.0/9.0).sin());
        let (nr,ni)=(c1-c2, s1-s2);                 // numerator
        // divide by (2 pi i m):  (nr + i ni)/(i*2 pi m) = (ni - i nr)/(2 pi m)
        let (gr,gi)=(ni/(tau*fm), -nr/(tau*fm));
        // F(k) = sum over components of (e^{-2 pi i k b} - e^{-2 pi i k a})/(-2 pi i k)
        let (mut fr,mut fi)=(0.0f64,0.0f64);
        for &(a,b) in comps.iter(){
          let (cb,sb)=((tau*k*b).cos(), -(tau*k*b).sin());
          let (ca,sa)=((tau*k*a).cos(), -(tau*k*a).sin());
          let (dr,di)=(cb-ca, sb-sa);
          // divide by (-2 pi i k): (dr + i di)/(-i 2 pi k) = (-di + i dr)/(2 pi k) * (-1)... do directly
          fr += di/(tau*k)*(-1.0)*(-1.0);           // Re[(dr+i di)/(-2 pi i k)] =  di/(2 pi k) * (-1)?
          fi += dr/(tau*k);
        }
        // careful: 1/(-2 pi i k) = i/(2 pi k).  (dr + i di) * i/(2 pi k) = (-di + i dr)/(2 pi k)
        // so Re = -di/(2 pi k), Im = dr/(2 pi k).  Recompute cleanly:
        let (mut Fr,mut Fi)=(0.0f64,0.0f64);
        for &(a,b) in comps.iter(){
          let (cb,sb)=((tau*k*b).cos(), -(tau*k*b).sin());
          let (ca,sa)=((tau*k*a).cos(), -(tau*k*a).sin());
          let (dr,di)=(cb-ca, sb-sa);
          Fr += -di/(tau*k); Fi += dr/(tau*k);
        }
        let _=(fr,fi);
        // term = 2*Re( ghat(m) * conj(F) ) = 2*(gr*Fr + gi*Fi)
        acc += 2.0*(gr*Fr + gi*Fi);
      }
      let tail = 2.0*n/(pi*pi*f*(mm as f64));
      if acc - tail > 1e-12 {
        dec+=1;
        let esc = comps.iter().any(|&(a,b)| {
          let lo=f*b-2.0/9.0; let hi=f*a+2.0/9.0; lo.ceil() > hi.floor()+1e-9 });
        if !esc { viol+=1; }
      } else { undec+=1; println!("   undecided tuple (v1,v2,v3,v4) = ({},{},{},{})", v1,v2,v3,v4); }
    }
  }}
  println!("MULTI-MODE Fourier criterion, M = {} modes:", mm);
  println!("   pairs      : {}", tot);
  println!("   DECIDES    : {}  ({:.2}%)", dec, 100.0*(dec as f64)/(tot as f64));
  println!("   undecided  : {}  ({:.2}%)", undec, 100.0*(undec as f64)/(tot as f64));
  println!("   CROSS-VALIDATION failures : {}", viol);
}
