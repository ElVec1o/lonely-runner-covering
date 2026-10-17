// t2sweep: exact ML for V = ([1,m]\{r}) u {w}, (m+1)|w, gcd(V)=1. ML attained at t=c/s, s=v_i+v_j.
// Usage: t2sweep m0 m1 W        sweep m0<=m<=m1, w<=W*m; prints "m r w num den flag", ML=num/den,
//                               flag = 1 iff the q=2m+1 case of Theorem A applies
//        t2sweep cover < table  reads the sweep output, prints the families covered by neither
//                               Theorem A (some q in [m+2,2m+1]) nor Theorem B, then a summary
//        t2sweep v x1 x2 ...    exact ML of one family
use std::sync::{Arc,Mutex};
fn gcd(a:u64,b:u64)->u64{ if b==0{a}else{gcd(b,a%b)} }
// returns (num,den) of ML
fn ml(v:&[u64])->(u64,u64){
  let (mut bn,mut bd)=(0u64,1u64);
  let n=v.len();
  for i in 0..n{ for j in i..n{ let s=v[i]+v[j];
    for c in 1..=s/2 { // candidate t=c/s; value = min_k ||v_k c/s||
      // quick reject: need all >= bn/bd, i.e. d_k*bd > bn*s ... use >= to allow ties skip
      let mut mn=u64::MAX; let mut ok=true;
      for &x in v { let r=(x*c)%s; let d=r.min(s-r);
        if d*bd <= bn*s { ok=false; break; } if d<mn{mn=d;} }
      if ok { let g=gcd(mn,s); bn=mn/g; bd=s/g; }
    }}}
  (bn,bd)
}
fn main(){
  let a:Vec<String>=std::env::args().collect();
  if a[1]=="cover" { cover(); return; }
  if a[1]=="v" { let v:Vec<u64>=a[2..].iter().map(|s|s.parse().unwrap()).collect(); let (n,d)=ml(&v); println!("{}/{}",n,d); return; }
  let m0:u64=a[1].parse().unwrap(); let m1:u64=a[2].parse().unwrap(); let wmul:u64=a[3].parse().unwrap();
  let mut jobs=vec![];
  for m in m0..=m1 { for r in 1..=m { let mut w=m+1; while w<=wmul*m { jobs.push((m,r,w)); w+=m+1; } } }
  let total=jobs.len(); eprintln!("jobs {}",total);
  let jobs=Arc::new(jobs); let idx=Arc::new(Mutex::new(0usize)); let out=Arc::new(Mutex::new(Vec::new()));
  let mut hs=vec![];
  for _ in 0..8 { let (jobs,idx,out)=(jobs.clone(),idx.clone(),out.clone());
    hs.push(std::thread::spawn(move||{ loop{
      let k={let mut g=idx.lock().unwrap(); let k=*g; *g+=1; k}; if k>=jobs.len(){break;}
      if k%5000==0 { eprintln!("progress {}/{}",k,jobs.len()); }
      let (m,r,w)=jobs[k];
      let mut v:Vec<u64>=(1..=m).filter(|&x|x!=r).collect(); if v.contains(&w){continue;} v.push(w);
      let g=v.iter().fold(0,|a,&b|gcd(a,b)); if g!=1{continue;}
      let (n,d)=ml(&v);
      let q=2*m+1; let cov = gcd(r,q)==1 && { let x=w%q; x!=0 && x!=r%q && x!=(q-r%q)%q };
      out.lock().unwrap().push((m,r,w,n,d,cov));
    }}));}
  for h in hs{h.join().unwrap();}
  let mut o=out.lock().unwrap(); o.sort();
  for &(m,r,w,n,d,cov) in o.iter(){ println!("{} {} {} {} {} {}",m,r,w,n,d,cov as u8); }
}

// Theorem A: q>m, (q>m+r or q=2r), gcd(r,q)=1, w not 0,+-r mod q  => ML >= 2/q (used with q<=2m+1).
// Theorem B: 2r>m, r does not divide w                            => ML >= 1/r >= 2/(2m+1).
fn cover(){
  use std::io::BufRead;
  let (mut tot,mut unc,mut below,mut eq)=(0u64,0u64,0u64,Vec::new());
  for l in std::io::stdin().lock().lines(){
    let l=l.unwrap(); let x:Vec<u64>=l.split_whitespace().map(|s|s.parse().unwrap()).collect();
    if x.len()<5 {continue;}
    let (m,r,w,n,d)=(x[0],x[1],x[2],x[3],x[4]); tot+=1;
    if n*(2*m+1)<2*d {below+=1;} if n*(2*m+1)==2*d {eq.push((m,r,w));}
    let mut c=false;
    for q in m+2..=2*m+1 { if !(q>m+r || q==2*r) {continue;} if gcd(r,q)!=1 {continue;}
      let y=w%q; if y==0 || y==r%q || y==(q-r%q)%q {continue;} c=true; break; }
    if !c && 2*r>m && w%r!=0 { c=true; }
    if !c { unc+=1; println!("{}",l); }
  }
  println!("# families {} ; below 2/(2m+1): {} ; equality (m,r,w): {:?} ; uncovered by Thm A/B: {}",tot,below,eq,unc);
}
