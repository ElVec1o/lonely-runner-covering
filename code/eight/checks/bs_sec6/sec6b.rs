// finite checks for Barajas-Serra 6.3 table / h=m, 6.5 (ii.1)(b), 6.6 (16) and (b).
// Exact integers mod N = 7^(m+1). q(x) = floor((x mod N)/7^m). No floating point.
fn nu(x:u64,n:u64)->u32{ let mut x=x%n; if x==0 {return 99;} let mut v=0; while x%7==0 {x/=7; v+=1;} v }
fn r(x:u64,n:u64)->u64{ let mut x=x%n; while x%7==0 {x/=7;} x%7 }
fn ell(s:u32)->u32{ if s==0 {return 0;} let mut best=8; for st in 0..7 { for l in 1..=7 { let mut iv=0u32; for t in 0..l { iv|=1<<((st+t)%7);} if s&!iv==0 && l<best {best=l;} } } best }
fn md(a:i64)->u64{ a.rem_euclid(7) as u64 }
struct P{n:u64,m:u32,pm:u64}
impl P{
 fn q(&self,x:u64)->u64{ (x%self.n)/self.pm }
 fn sub(&self,a:u64,b:u64)->u64{ (a%self.n+self.n-b%self.n)%self.n }
 fn et(&self,x:u64,y:u64)->u64{ let (rx,ry)=(r(x,self.n),r(y,self.n)); let (qx,qy)=(self.q(x),self.q(y));
   if ry==2*rx%7 {(2*qx+14-qy)%7} else if rx==2*ry%7 {(2*qy+14-qx)%7} else if rx==ry {(qx+7-qy)%7} else {panic!()} }
 fn lam(&self,h:u32,k:u64)->u64{ if h==self.m { k } else { (1+7u64.pow(self.m-h)*k)%self.n } }
 fn mul(&self,l:u64,a:&[u64])->Vec<u64>{ a.iter().map(|&x| (l as u128*x as u128 % self.n as u128) as u64).collect() }
 fn inv(&self,x:u64)->u64{ (1..self.n).find(|&y| (x as u128*y as u128)%(self.n as u128)==1).unwrap() }
 // Lemma-5 style finish: some lambda_k in Lambda_0 (k=0..6) with q(A) avoiding {0,6}
 fn fin0(&self,a:&[u64])->bool{ (0..7).any(|k| self.mul(self.lam(0,k),a).iter().all(|&x| {let v=self.q(x); v!=0&&v!=6})) }
 fn good(&self,a:&[u64])->bool{ a.iter().all(|&x| {let v=self.q(x); v!=0&&v!=6}) }
 // lengths of q-images of the three classes relative to class of a[0]
 fn ells(&self,a:&[u64])->(u32,u32,u32){ let s=r(a[0],self.n); let mut m=[0u32;3];
   for &x in a { let rx=r(x,self.n); let i= if rx==s {0} else if rx==2*s%7 {1} else if rx==4*s%7 {2} else {panic!()}; m[i]|=1<<self.q(x);} (ell(m[0]),ell(m[1]),ell(m[2])) }
}
fn table63(et:u64,u:u64,borrow:bool)->u64{ // printed table, row q(e45)
  let t0=[0,6,0,3,6,0,6]; let t1=[6,0,6,0,99,6,5];
  if et==0 {t0[u as usize]} else if u==4 { if borrow {6} else {5} } else {t1[u as usize]} }
fn main(){
 let args:Vec<String>=std::env::args().collect(); let which=args.get(1).map(|s|s.as_str()).unwrap_or("all");
 // ---------- Z7 part ----------
 if which=="all"||which=="z7" {
  // 6.3 table arithmetic: rows q(e13), q(e23), q(e12) implied by invariants et = q13-q45, u = 3q13+5q23
  let pq13=[[0,6,0,3,6,0,6],[0,1,0,1,6,0,6]]; let pq23=[[0,5,6,3,0,1,6],[0,1,6,0,0,1,6]];
  let mut bad=0; for e in 0..2u64 { for u in 0..7u64 { for b in [false,true] { if !(e==1&&u==4) && b {continue;}
     let q45=table63(e,u,b); let q13=(q45+e)%7; let q23=md(3*u as i64-2*q13 as i64);
     let (a13,a23)= if e==1&&u==4 { if b {(0,5)} else {(6,0)} } else {(pq13[e as usize][u as usize],pq23[e as usize][u as usize])};
     let q12=[md(q13 as i64-q23 as i64), md(q13 as i64-q23 as i64-1)];
     let ok= a13==q13 && a23==q23; if !ok {bad+=1;}
     println!("6.3 table et={} u={} borrow={} : q45={} q13={} q23={} q12 in {{{},{}}} printed(q13,q23)=({},{}) {}", e,u,b,q45,q13,q23,q12[0],q12[1],a13,a23, if ok {"OK"} else {"MISMATCH"}); } } }
  println!("6.3 table rows q13,q23 mismatches: {}", bad);
  // 6.3 h=m bad pairs: q(A1) in {1..4}, q(d3)=1, q(d4)=i, q(d5)=j, lambda_k k in {0,1}
  let mut bp=vec![]; for i in 0..7i64 { for j in 0..7i64 { let hit=|k:i64| [i+2*k,j+4*k].iter().any(|&v| md(v)==0||md(v)==6);
     if hit(0)&&hit(1) { bp.push((md(2-i),md(2*i-j))); } } }
  bp.sort(); println!("6.3 h=m bad (et34,et45) pairs: {:?}", bp);
  let isbad=|a:u64,b:u64| bp.contains(&(a,b));
  let mut f=0; for a in 0..7u64 { for b in 0..7u64 { if (0..4).all(|e| isbad((a+7-(e&1))%7,(b+7-(e>>1))%7)) {f+=1;} } }
  println!("6.3 h=m: (a,b) with all four (a-e1,b-e2) bad: {}", f);
  // 6.5 (ii.1)(b): q(A1)={1,2,3}, q(A4)={i,i+4}; k in 0..3
  let ex:Vec<i64>=(0..7).filter(|&i| !(0..3).any(|k:i64| [i+4*k,i+4+4*k].iter().all(|&v| md(v)!=0&&md(v)!=6))).collect();
  println!("6.5(b): i with no k in {{0,1,2}} good: {:?} (paper: 2,6)", ex);
  // 6.6 (a): q(A1)={k,k+2}, q(A2)={2k-a,2k-a+1} (from (13)) or {a-2k,a-2k+1} (as printed), q(d5)=4b+4k
  for (name,sg) in [("from (13): q(d4)=2k-a",1i64),("as printed: q(d4)=a-2k",-1)] {
    let mut b16=vec![]; for a in 0..7i64 { for b in 0..7i64 {
      let okk=|k:i64| { let q4=md(sg*(2*k-a)); [k,k+2,q4 as i64,q4 as i64+1,4*b+4*k].iter().all(|&v| md(v)!=0&&md(v)!=6) };
      if !(1..4).any(okk) { b16.push((a,b)); } } }
    println!("6.6(a) bad set, {}: {:?}  (printed: (4,2),(4,4),(5,4),(6,4),(6,6))", name, b16);
    let isb=|a:i64,b:i64| b16.contains(&(md(a) as i64,md(b) as i64));
    let c1=b16.iter().filter(|p| p.0<4).count(); println!("   bad with a notin {{4,5,6}}: {}", c1);
    let c2=b16.iter().filter(|p| (p.0==3||p.0==4||p.0==5)&&!(p.1==2||p.1==4)).count(); // e24 in {4N/7,5N/7}: a in {3,4,5}
    let c3=b16.iter().filter(|p| (p.0==6||p.0==5||p.0==0)&&!(p.1==4||p.1==6)).count(); // e24 in {6N/7,0}: a in {5,6,0,6}
    println!("   e24 in {{4,5}}N/7 and et25 in bad but not in {{2,4}}: {} ; e24 in {{6N/7,0}} and not in {{4,6}}: {}", c2,c3);
    let mut f4=0; for a in 0..7 { for b in 0..7 { if (0..4).all(|e| isb(a-(e&1),b-(e>>1))) {f4+=1;} } }
    println!("   (a,b) with all four (a-e1,b-e2) bad: {}", f4);
  }
  // 6.6 (b): q(A2)={k,k+2}, q(A1)={4a+4k,4a+4k+1}, q(d5) = 4(b + q(d2)) [from (13)] or a-b+k [printed]
  for (name,v) in [("from (13): q(d5)=4(b+q(d2))",0),("as printed: q(d5)=a-b+k",1)] {
    let mut bb=vec![]; for a in 0..7i64 { for b in 0..7i64 {
      let okk=|k:i64| { let q2=md(4*a+4*k) as i64; let q5= if v==0 {4*(b+q2)} else {a-b+k};
        [k,k+2,q2,q2+1,q5].iter().all(|&x| md(x)!=0&&md(x)!=6) };
      if !(1..4).any(okk) { bb.push((a,b)); } } }
    let av:std::collections::BTreeSet<i64>=bb.iter().map(|p|p.0).collect();
    println!("6.6(b) {}: bad (et24,et25) = {:?}; et24 values {:?} (paper: subset of {{2,4,6}})", name, bb, av);
    let mut bb7=vec![]; for a in 0..7i64 { for b in 0..7i64 {
      let okk=|k:i64| { let q2=md(4*a+4*k) as i64; let q5= if v==0 {4*(b+q2)} else {a-b+k};
        [k,k+2,q2,q2+1,q5].iter().all(|&x| md(x)!=0&&md(x)!=6) };
      if !(0..7).any(okk) { bb7.push((a,b)); } } }
    println!("   same with all k in 0..7: {:?}", bb7);
  }
 }
 // ---------- integer part ----------
 for m in [2u32,3] {
  if which=="z7" {break;}
  let n=7u64.pow(m+1); let p=P{n,m,pm:7u64.pow(m)}; let t=n/7;
  let cls=|c:u64| -> Vec<u64> { (0..n).filter(|x| x%7==c).collect() };
  let (c1,c2,c4)=(cls(1),cls(2),cls(4));
  // ===== 6.3 (ii.2.b), h<m =====
  { let mut cnt=0u64; let mut fet=0u64; let mut fconc=0u64; let mut ffin=0u64; let mut f2x=0u64; let mut ffin_any=0u64; let mut samples=0;
    let mut rng=0x9e3779b97f4a7c15u64; let mut rnd=|| { rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; rng };
    let mut triples=vec![];
    if m==2 { for &d1 in &c1 { for &d2 in &c1 { for &d3 in &c1 { triples.push((d1,d2,d3)); } } } }
    else { for _ in 0..3_000_000 { let pick=|x:u64| c1[(x%c1.len() as u64) as usize]; let (a,b,c)=(rnd(),rnd(),rnd()); triples.push((pick(a),pick(b),pick(c))); } }
    for &(d1,d2,d3) in &triples {
      let (e13,e23)=(p.sub(d1,d3),p.sub(d2,d3)); let h=nu(e13,n); if h>=m || nu(e23,n)!=h {continue;}
      let (r13,r23)=(r(e13,n),r(e23,n)); if !(r13==3*r23%7 && (r13==1||r13==6)) {continue;}
      let d4s:Vec<u64>= if m==2 {c2.clone()} else {(0..6).map(|_| c2[(rnd()%c2.len() as u64) as usize]).collect()};
      for &d4 in &d4s { let d5s:Vec<u64>= if m==2 {c4.clone()} else {(0..6).map(|_| c4[(rnd()%c4.len() as u64) as usize]).collect()};
       for &d5 in &d5s {
        let e45=p.sub(2*d4,d5); if nu(e45,n)!=h {continue;}
        let sg= if r(e45,n)==r13 {1} else if r(e45,n)==7-r13 {-1} else {continue;};
        cnt+=1; if m==3 {samples+=1;}
        let a=[d1,d2,d3,d4,d5];
        let g=|x:&[u64]| if sg==1 {p.sub(2*x[3],x[4])} else {p.sub(x[4],2*x[3])}; // sigma*e45
        let f=p.sub(e13,g(&a)); // f = e13 - sigma e45 (sign chosen so that et in {0,1})
        // step 1: lambda1 at level nu(f)
        let vf=nu(f,n); let l1:u64 = if vf>m {1} else if vf<m { (0..7).map(|k| p.lam(vf,k)).find(|&l| p.q(l*f%n)==0).unwrap() }
                        else { p.inv(f/t) }; // makes lambda f = N/7
        let a1=p.mul(l1,&a);
        let (e13b,e23b)=(p.sub(a1[0],a1[2]),p.sub(a1[1],a1[2]));
        let et=(p.q(e13b)+7-p.q(g(&a1)))%7; if et>1 {fet+=1; continue;}
        let u=(3*p.q(e13b)+5*p.q(e23b))%7;
        let borrow= p.q(p.sub(a1[0],a1[1])) != (p.q(e13b)+7-p.q(e23b))%7;
        let target=table63(et,u,borrow);
        let l2=(0..7).map(|k| p.lam(h,k)).find(|&l| p.q(l*g(&a1)%n)==target).unwrap();
        let a2=p.mul(l2,&a1);
        let (l1_,_,_)=p.ells(&a2); let et45=p.et(a2[3],a2[4]);
        let conc = if et==0&&u==3 { let b2=p.mul(2,&a2); let (x,_,_)=p.ells(&b2); let e=p.et(b2[3],b2[4]); (x<=3 && e!=2&&e!=4) || x<=2 }
                   else { (l1_<=3 && et45!=2&&et45!=4) || l1_<=2 };
        if !conc {fconc+=1; if fconc<=5 {println!("  6.3 conc fail m={} a={:?} h={} et={} u={} borrow={} l1={} et45={}",m,a,h,et,u,borrow,l1_,et45);} }
        let fin = if et==0&&u==3 { p.fin0(&p.mul(2,&a2)) } else { p.fin0(&a2) };
        if !fin {ffin+=1;}
        if et==0&&u==3 && !p.fin0(&a2) && !p.fin0(&p.mul(2,&a2)) {f2x+=1;}
        if !fin && !(0..n).filter(|x|x%7!=0).any(|l| p.good(&p.mul(l,&a))) {ffin_any+=1;}
      } } }
    println!("m={} 6.3(ii.2.b) {} configs{}: et not in {{0,1}}: {}; table conclusion fails: {}; Lambda0 finish fails: {} (of which no unit at all: {}); 2x case both fail: {}",
      m,cnt, if m==3 {" (sampled)"} else {" (exhaustive)"}, fet,fconc,ffin,ffin_any,f2x); }
  // ===== 6.3 h = m, nu(e34)=nu(e45)=m (incl. =0 residue reported separately) =====
  { let (mut cnt,mut fclaim,mut fend,mut fall,mut zero)=(0u64,0u64,0u64,0u64,0u64);
    for &d3 in &c1 { for tt in 0..7u64 { let d4=(2*d3+tt*t)%n; for tp in 0..7u64 { let d5=(2*d4+tp*t)%n;
      let a=[(d3+3*t)%n,(d3+t)%n,d3,d4,d5]; cnt+=1; if tt==0||tp==0 {zero+=1;}
      let (q34,q45)=(p.q(p.sub(2*d3,d4)),p.q(p.sub(2*d4,d5)));
      let mut endok=false;
      for e1 in 0..2u64 { for e2 in 0..2u64 {
        let ls:Vec<u64>=(0..7).map(|k| p.lam(1,k)).filter(|&l| p.q(l*(7*d3)%n)==4*e1+2*e2).collect();
        if ls.is_empty() {fclaim+=1000000;}
        for &l in &ls { let b=p.mul(l,&a); let pr=(p.et(b[2],b[3]),p.et(b[3],b[4]));
          if pr!=((q34+7-e1)%7,(q45+7-e2)%7) {fclaim+=1;}
          // end: normalize q(d3)=1 by Lambda0, then k in {0,1}
          let l0=(0..7).map(|k| p.lam(0,k)).find(|&l0| p.q(l0*b[2]%n)==1).unwrap(); let c=p.mul(l0,&b);
          if (0..2).any(|k| p.good(&p.mul(p.lam(0,k),&c))) {endok=true;} } } }
      if !endok {fend+=1;} if !(0..7).any(|k| p.good(&p.mul(p.lam(0,k),&a))) && !endok {fall+=0;}
    } } }
    let _=fall;
    println!("m={} 6.3 h=m, e34,e45 in (N/7)Z: {} configs (zero residue in {}): carry claim failures {}; paper end-route fails {}", m,cnt,zero,fclaim,fend); }
  // ===== 6.5 (ii.1)(b) =====
  { let (mut cnt,mut fz,mut exc,mut fl7,mut excany)=(0u64,0u64,0u64,0u64,0u64); let mut exinfo=std::collections::BTreeMap::new();
    let lamlow:Vec<u64>={ let mut v=vec![]; for h in 0..m { for k in 0..7 { v.push(p.lam(h,k)); } } v };
    for &d3 in &c1 { for &d5 in &c4 { let a=[(d3+2*t)%n,(d3+t)%n,d3,(d5+4*t)%n,d5]; cnt+=1;
      // normalize q(A1)={1,2,3} (q(d3)=1) by Lambda0
      let norm=|b:&[u64]| { let l0=(0..7).map(|k| p.lam(0,k)).find(|&l0| p.q(l0*b[2]%n)==1).unwrap(); p.mul(l0,b) };
      let b=norm(&a); let i=p.q(b[4]) as i64;
      let ok3=|c:&[u64]| (0..3).any(|k| p.good(&p.mul(p.lam(0,k),c)));
      if ok3(&b) == (i==2||i==6) {fz+=1;}
      let e=p.sub(2*a[3],a[2]); // e(d3,d4) = 2 d4 - d3
      if e==5*t { exc+=1; let a2=p.mul(2,&a); let (x1,_,x4)=(p.ells(&a2).0,0,{let s=r(a2[0],n); let _=s; let mut mm=0u32; for &x in &a2[3..] {mm|=1<<p.q(x);} ell(mm)});
          let e34=p.sub(2*a[3],a[2])/t; *exinfo.entry((x1,x4,e34)).or_insert(0)+=1;
          let any=(0..n).filter(|x|x%7==1).any(|l| ok3(&norm(&p.mul(l,&a))) ) || (0..n).filter(|x|x%7==1).any(|l| p.fin0(&p.mul(2*l%n,&a)));
          if !any {excany+=1;}
          let r2=(0..7).any(|k1| p.fin0(&p.mul(2*p.lam(1,k1)%n,&a))); let r0=(0..7).any(|k1| p.fin0(&p.mul(p.lam(1,k1),&a)));
          *exinfo.entry((100+r2 as u32,100+r0 as u32,0)).or_insert(0)+=1; }
      else if !ok3(&b) { // Lemma 7 route: some lambda in Lambda_h (h<m) makes et(d3,d4) notin {4,5}, then Lambda0 finishes
          let w=lamlow.iter().any(|&l| { let c=p.mul(l,&a); let x=p.et(c[2],c[3]); x!=4&&x!=5 && ok3(&norm(&c)) });
          if !w {fl7+=1;} }
    } }
    println!("m={} 6.5(ii.1)(b): {} configs; Z7 claim 'fails iff i in {{2,6}}' violated: {}; Lemma-7 route fails (non-exceptional): {}; exceptional 2d4-d3=5N/7: {} configs, (l(2A1),l(2A4),e34/(N/7)) = {:?}; exceptional not closed by (1+7Z) or 2(1+7Z): {}",
      m,cnt,fz,fl7,exc,exinfo,excany); }
  // ===== 6.6 (a) (16) and (b) with nu(e24)=nu(e25)=m etc: direct integer test of the Z7 predictions =====
  if m==2 { let md7=|x:i64| x.rem_euclid(7);
    let b16:Vec<(u64,u64)>={ let mut v=vec![]; for a in 0..7i64 { for b in 0..7i64 {
      let okk=|k:i64| [k,k+2,2*k-a,2*k-a+1,4*b+4*k].iter().all(|&x| md7(x)!=0&&md7(x)!=6); if !(1..4).any(okk) {v.push((a as u64,b as u64));} } } v };
    let (mut cnt,mut fpred)=(0u64,0u64);
    for &d2 in &c1 { for &d4 in &c2 { for &d5 in &c4 { let a=[(d2+2*t)%n,d2,(d4+t)%n,d4,d5]; cnt+=1;
      let lk=|k:u64| (0..7).map(|j| p.lam(0,j)).find(|&l| p.q(l*d2%n)==k).unwrap();
      let works=(1..4).any(|k| p.good(&p.mul(lk(k),&a)));
      let pr=(p.et(d2,d4),p.et(d2,d5)); if works == b16.contains(&pr) {fpred+=1;} } } }
    println!("m=2 6.6(a): {} configs; Z7 prediction (bad iff (et24,et25) in computed B16) wrong: {}", cnt,fpred);
    // end route for nu(e24)=nu(e25)=m: some lambda in Lambda1 then k in {1,2,3}
    let (mut c2n,mut fr)=(0u64,0u64);
    let inv2=p.inv(2);
    for &d2 in &c1 { for tt in 1..7u64 { let d4=(2*d2+n-tt*t)%n; for tp in 1..7u64 { let d5=((d2+tp*t)%n)*inv2%n; c2n+=1;
      let a=[(d2+2*t)%n,d2,(d4+t)%n,d4,d5];
      let w=(0..7).any(|k1| { let b=p.mul(p.lam(1,k1),&a); (1..4).any(|k| { let l=(0..7).map(|j| p.lam(0,j)).find(|&l| p.q(l*b[1]%n)==k).unwrap(); p.good(&p.mul(l,&b)) }) });
      if !w {fr+=1;} } } }
    println!("m=2 6.6(a) nu(e24)=nu(e25)=m: {} configs, not closed by Lambda1 then k in 1..3: {}", c2n, fr);
    // (b): e12 = N/7, e34 = 2N/7
    let (mut cb,mut fb13,mut fbpr)=(0u64,0u64,0u64); let mut badet24=std::collections::BTreeSet::new();
    for &d2 in &c1 { for &d4 in &c2 { for &d5 in &c4 { let a=[(d2+t)%n,d2,(d4+2*t)%n,d4,d5]; cb+=1;
      let lk=|k:u64| (0..7).map(|j| p.lam(0,j)).find(|&l| p.q(l*d4%n)==k).unwrap();
      for k in 1..4u64 { let b=p.mul(lk(k),&a); let (x,y)=(p.et(b[1],b[3]) as i64,p.et(b[1],b[4]) as i64);
        if p.q(b[4]) as i64 != md7(4*(y+p.q(b[1]) as i64)) {fb13+=1;} if p.q(b[4]) as i64 != md7(x-y+k as i64) {fbpr+=1;} }
      if !(1..4).any(|k| p.good(&p.mul(lk(k),&a))) { badet24.insert(p.et(d2,d4)); } } } }
    println!("m=2 6.6(b): {} configs; q(d5) formula from (13) wrong: {}, printed formula wrong: {}; et24 values with k in 1..3 failing: {:?}", cb,fb13,fbpr,badet24);
  }
 }
}
