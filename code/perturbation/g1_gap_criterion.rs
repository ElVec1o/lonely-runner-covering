// Floating point is used only in the ground-truth column (tolerance 1e-12); the gap criterion itself is integer.
// Sharp AND uniform criterion via the gap structure of a progression.
// Normal form: the admissible k form an interval K of length L (from the x-condition);
// the y-condition asks whether {k*c mod n : k in K} meets an interval J of length M.
// The GAP STRUCTURE of that point set is invariant under shifting K, hence independent of the
// translation w. So "largest gap < M" is a criterion that is sharp and uniform at once.
fn gcd(a:i64,b:i64)->i64{ if b==0 {a.abs()} else {gcd(b,a%b)} }
fn nid(x:f64)->f64{ let f=x-x.floor(); if f<1.0-f {f} else {1.0-f} }
fn largest_gap(c:i64,n:i64,l:i64)->i64{
  let mut pts:Vec<i64>=(0..l).map(|k| ((k*c)%n+n)%n).collect();
  pts.sort(); pts.dedup();
  let mut g=0i64;
  for i in 0..pts.len(){
    let d = if i+1<pts.len() { pts[i+1]-pts[i] } else { pts[0]+n-pts[i] };
    if d>g {g=d;}
  }
  g
}
fn truth(v1:i64,v2:i64,v3:i64,v4:i64)->bool{
  for k in 0..v2 { let t=(2.0/9.0+(k as f64))/(v2 as f64);
    if nid((v1 as f64)*t)>=2.0/9.0-1e-12 && nid((v2 as f64)*t)>=2.0/9.0-1e-12
    && nid((v3 as f64)*t)>=2.0/9.0-1e-12 && nid((v4 as f64)*t)>=2.0/9.0-1e-12 {return true;} }
  false
}
fn main(){
  let (mut tot,mut dec,mut viol,mut undec)=(0u64,0u64,0u64,0u64);
  for v1 in 1..40i64 { for v2 in (v1+1)..80i64 {
    if gcd(v1,v2)!=1 {continue;}
    let v3=v1+v2;
    for v4 in (v3+1)..(4*v3) {
      if gcd(v1,v4)>2||gcd(v2,v4)>2||gcd(v3,v4)>2 {continue;}
      let n=v2/gcd(v2,gcd(v1,v4));
      if n<6 {continue;}
      if gcd(v1,n)!=1 {continue;}                       // normal form needs a invertible
      tot+=1;
      // c = v4 * v1^{-1} mod n
      let mut inv=1i64; for x in 1..n { if (v1*x)%n==1%n {inv=x; break;} }
      let c=((v4%n)*inv)%n;
      // x-condition: t*v1 in an interval of length 1/3  -> L = floor(n/3) admissible k
      let l=n/3;
      if l<1 {continue;}
      // y-condition: interval of length 5/9 -> M = floor(5n/9)
      let m=(5*n)/9;
      let g=largest_gap(c,n,l);
      if g < m { dec+=1; if !truth(v1,v2,v3,v4) {viol+=1;} } else { undec+=1; }
    }
  }}
  println!("three-distance gap criterion (sharp and uniform in the translation):");
  println!("   cases in normal form : {}", tot);
  println!("   criterion DECIDES    : {}  ({:.2}%)", dec, 100.0*(dec as f64)/(tot as f64));
  println!("   undecided            : {}  ({:.2}%)", undec, 100.0*(undec as f64)/(tot as f64));
  println!("   GROUND-TRUTH VIOLATIONS (decides but no t exists): {}", viol);
}
