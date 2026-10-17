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

// perturb_ratio: the ratio of ell(n,{n-2}) n^2 to 2/P(n-2), P(m) the least prime not dividing m
// (Section "A ceiling", paper/perturbation/perturbation.tex: values 1.163, 1.036, 1.009, 1.002 at
// n = 50, 200, 800, 3200).  Exact i128 rationals; ratio printed to 6 decimals from the exact fraction.
// ell(n,{b}) is evaluated by the exact base-point formula max over a (gcd(a,b)=1) of window(n,b,a,{b}).
// Controls: for n = 50 and 200 the formula is compared with the independent interval sweep ell() (must agree
// exactly); for n = 20..60 the formula is compared with the sweep for every b in [2,n-1].
// Usage: perturb_ratio [n ...]    default 50 200 800 3200
fn ell_formula(n:i128,b:i128)->Q{ let m=[b]; let mut best=q(0,1);
  for a in 0..b.max(1) { if g(a,b)!=1 {continue;} let w=window(n,b,a,&m); if cmp(w,best)==std::cmp::Ordering::Greater {best=w;} } best }
fn least_prime_not_dividing(m:i128)->i128{ let mut p=2; loop { let mut isp=true; let mut d=2; while d*d<=p { if p%d==0 {isp=false;break;} d+=1; } if isp && m%p!=0 {return p;} p+=1; } }
fn main(){
  let mut ok=true;
  for n in 20..=60i128 { for b in 2..n { let f=ell_formula(n,b); let s=ell(n,&[b]); if cmp(f,s)!=std::cmp::Ordering::Equal { ok=false; println!("DISAGREE n={} b={}",n,b); } } }
  println!("control: formula == sweep for all 20<=n<=60, 2<=b<n : {}", ok);
  let args:Vec<i128>=std::env::args().skip(1).map(|x| x.parse().unwrap()).collect();
  let ns:Vec<i128>= if args.is_empty() { vec![50,200,800,3200] } else { args };
  println!("{:>6} {:>6} {:>5} {:>22} {:>10}", "n","b=n-2","P","ell*n^2*P/2 (exact -> dec)","sweep==formula");
  for n in ns { let b=n-2; let f=ell_formula(n,b); let p=least_prime_not_dividing(b);
    let chk = if n<=200 { if cmp(ell(n,&[b]),f)==std::cmp::Ordering::Equal {"yes"} else {ok=false;"NO"} } else {"n/a"};
    // ratio = f * n^2 / (2/P) = f.n * n^2 * P / (f.d * 2)
    let num=f.n*n*n*p; let den=f.d*2; let r=(num as f64)/(den as f64);
    println!("{:>6} {:>6} {:>5} {:>12}/{:<12} {:>10.6} {}", n,b,p,num,den,r,chk); }
  if !ok { std::process::exit(1); }
}
