// Exhaustive Z7 checks of Barajas-Serra Lemmas 5, 6, 12 (as stated, s normalized to 1:
// q(lam_k d) = q(d) + j k for d in A_j, j in {1,2,4}). Sets are subsets of Z7 (bitmasks).
fn ell(s:u32)->u32{ if s==0 {return 0;} let mut best=8; for st in 0..7 { for l in 1..=7 { let mut iv=0; for t in 0..l { iv|=1<<((st+t)%7);} if s&!iv==0 && l<best {best=l;} } } best }
fn shift(s:u32,c:u32)->u32{ let mut r=0; for x in 0..7 { if s>>x&1==1 { r|=1<<((x+c)%7);} } r }
fn ok(q1:u32,q2:u32,q4:u32,ks:&[u32])->bool{ ks.iter().any(|&k| (shift(q1,k)|shift(q2,2*k%7)|shift(q4,4*k%7)) & 0b1000001 == 0) }
fn elems(s:u32)->Vec<u32>{ (0..7).filter(|x| s>>x&1==1).collect() }
fn main(){
  let all:Vec<u32>=(0..7).collect();
  // Lemma 5
  let (mut n5,mut f5,mut exc5)=(0,0,0);
  for q1 in 0..128u32 { for q2 in 0..128u32 { for q4 in 0..128u32 {
    let (l1,l2,l4)=(ell(q1),ell(q2),ell(q4)); if l1+l2+l4>5 {continue;} n5+=1;
    if ok(q1,q2,q4,&all) {continue;}
    let exc = (l1,l2,l4)==(3,1,1) && elems(q2).iter().all(|&i| elems(q4).iter().all(|&j| { let e=(2*i+14-j)%7; e==2||e==4 }));
    if exc {exc5+=1} else {f5+=1; if f5<5 {println!("L5 fail {:07b} {:07b} {:07b}",q1,q2,q4);} } }}}
  println!("Lemma 5: {} configs, {} fail outside the stated exception, {} in exception", n5, f5, exc5);
  // Lemma 6: q(A1) subset {1..l1}, 1 in q(A1), ell(A1)=l1
  let mut f6=[0;4]; let mut n6=[0;4];
  for q1 in 0..128u32 { if q1&2==0 || q1 & 0b1000001 !=0 {continue;} let l1=ell(q1); if !(q1>>(l1+1)==0) {continue;}
   for q2 in 0..128u32 { for q4 in 0..128u32 { let (l2,l4)=(ell(q2),ell(q4));
    let good=ok(q1,q2,q4,&all);
    // (i)
    let c1 = ((l1,l2,l4)==(5,0,1) && elems(q4).iter().all(|&j| {let e=(2*j+6)%7; e!=4&&e!=6}))
          || ((l1,l2,l4)==(5,1,0) && elems(q2).iter().all(|&i| {let e=(2+7-i)%7; e!=2&&e!=3}));
    // (ii)
    let c2 = (l1,l2,l4)==(4,0,2) || ((l1,l2,l4)==(4,2,0) && { let i=(0..7).find(|&i| q2==(1<<i)|(1<<((i+1)%7))).unwrap(); (2+7-i)%7!=4 });
    let c3 = (l1,l2,l4)==(3,3,0);
    for (t,c) in [c1,c2,c3].iter().enumerate(){ if *c { n6[t]+=1; if !good { f6[t]+=1; if f6[t]<4 {println!("L6({}) fail {:07b} {:07b} {:07b}",t+1,q1,q2,q4);} } } }
  }}}
  println!("Lemma 6: configs (i),(ii),(iii) = {:?}, failures = {:?}", &n6[..3], &f6[..3]);
  // Lemma 12: |A1|=3,|A2|=2, A4 empty. (i) l1<=3 ; (ii) l1=4 and e(d,d') in {0,1,6} for d with q(A1) in {q(d)..q(d)+3}
  let (mut n12,mut f12)=([0;2],[0;2]);
  for q1 in 1..128u32 { if q1.count_ones()>3 {continue;} let l1=ell(q1); for q2 in 1..128u32 { if q2.count_ones()>2 {continue;}
    let good=ok(q1,q2,0,&all);
    if l1<=3 { n12[0]+=1; if !good {f12[0]+=1;} }
    if l1==4 { // find start d
      let st=(0..7).find(|&s| { let mut iv=0; for t in 0..4 {iv|=1<<((s+t)%7);} q1&!iv==0 && q1>>s&1==1 }).unwrap();
      if elems(q2).iter().all(|&i| { let e=(2*st+14-i)%7; e==0||e==1||e==6 }) { n12[1]+=1; if !good {f12[1]+=1; if f12[1]<4 {println!("L12(ii) fail {:07b} {:07b}",q1,q2);} } } }
  }}
  println!("Lemma 12 (as sets, |q(A1)|<=3, |q(A2)|<=2): configs {:?}, failures {:?}", n12, f12);
}
