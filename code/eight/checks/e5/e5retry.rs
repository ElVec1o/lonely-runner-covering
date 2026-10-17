// Falsification of the Giri-Kravitz 2D rounding step (MSSGap7 route), exact rationals.
fn gcd(a:i128,b:i128)->i128{ if b==0 {a.abs()} else {gcd(b,a%b)} }
#[derive(Clone,Copy)] struct Q{n:i128,d:i128}
fn q(n:i128,d:i128)->Q{let g=gcd(n,d).max(1);let s=if d<0{-1}else{1};Q{n:s*n/g,d:s*d/g}}
fn add(a:Q,b:Q)->Q{q(a.n*b.d+b.n*a.d,a.d*b.d)} fn mul(a:Q,b:Q)->Q{q(a.n*b.n,a.d*b.d)}
fn sub(a:Q,b:Q)->Q{add(a,Q{n:-b.n,d:b.d})}
fn nid(a:Q)->Q{let r=a.n.rem_euclid(a.d);q(r.min(a.d-r),a.d)}
fn ge(a:Q,b:Q)->bool{a.n*b.d>=b.n*a.d}
fn round(a:Q)->i128{ (2*a.n+a.d).div_euclid(2*a.d) }
struct R(u64); impl R{fn next(&mut self)->u64{self.0^=self.0<<13;self.0^=self.0>>7;self.0^=self.0<<17;self.0}}
fn main(){
 let mut rng=R(0x9E3779B97F4A7C15); let (mut tests,mut fails,mut nolrc)=(0u64,0u64,0u64);
 while tests<200000 {
  let qq=28+(rng.next()%30) as i128; let mut v=vec![0i128;7];
  for k in 0..7 { let m=1+(rng.next()%6) as i128; let dl=(rng.next()%3) as i128-1; v[k]=qq*m+dl; }
  if v.iter().any(|&x|x<=0) {continue;}
  let s=q(1,qq);
  let z:Vec<i128>=v.iter().map(|&x|round(mul(s,q(x,1)))).collect();
  let d:Vec<Q>=(0..7).map(|k|sub(q(z[k],1),mul(s,q(v[k],1)))).collect();
  if !d.iter().all(|x|ge(q(1,28),q(x.n.abs(),x.d))) {continue;}
  if (0..7).all(|k|z[k]*v[0]==z[0]*v[k]) {continue;}
  tests+=1;
  // pick pair minimizing positive slope gap
  let mut best:Option<(usize,usize,Q)>=None;
  for i in 0..7{for j in 0..7{ let g=sub(q(z[j],v[j]),q(z[i],v[i])); if g.n>0 { if best.map_or(true,|b|ge(b.2,g)&&!(b.2.n*g.d==g.n*b.2.d)) {best=Some((i,j,g));} }}}
  let (i,j,_)=best.unwrap(); let (x,y)=(z[i]+z[j],-(v[i]+v[j]));
  let c:Vec<i128>=(0..7).map(|k|x*v[k]+y*z[k]).collect();
  assert!(c.iter().all(|&e|e!=0)); assert!(c[i]==-c[j]);
  // LRC witness for |c| with gap>=1/7: search tau = m/(|c_a|+|c_b|)
  let mut tau=None;
  'o: for a in 0..7{for b in 0..7{ let den=c[a].abs()+c[b].abs(); for m in 0..den { let t=q(m,den);
     if (0..7).all(|k|ge(nid(mul(t,q(c[k],1))),q(1,7))) {tau=Some(t);break 'o;} }}}
  let Some(tau)=tau else {nolrc+=1;continue};
  let a1=mul(tau,q(y,1)); let k1=round(a1); let r=sub(a1,q(k1,1));
  let t=add(mul(tau,q(x,1)),mul(r,s));
  if !(0..7).all(|k|ge(nid(mul(t,q(v[k],1))),q(1,8))) {fails+=1; println!("FAIL v={:?} z={:?}",v,z);}
 }
 println!("tests={} fails={} no_lrc6_witness_found={}",tests,fails,nolrc);
}
