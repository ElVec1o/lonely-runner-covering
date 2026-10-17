// Lemma 5 failure profiles (l1,l2,l4) and minimal cardinalities (|q(A1)|,|q(A2)|,|q(A4)|).
use std::collections::BTreeMap;
fn ell(s:u32)->u32{ if s==0 {return 0;} let mut best=8; for st in 0..7 { for l in 1..=7 { let mut iv=0; for t in 0..l { iv|=1<<((st+t)%7);} if s&!iv==0 && l<best {best=l;} } } best }
fn shift(s:u32,c:u32)->u32{ let mut r=0; for x in 0..7 { if s>>x&1==1 { r|=1<<((x+c)%7);} } r }
fn main(){
  let mut prof:BTreeMap<(u32,u32,u32),(u32,(u32,u32,u32))>=BTreeMap::new();
  for q1 in 0..128u32 { for q2 in 0..128u32 { for q4 in 0..128u32 {
    let (l1,l2,l4)=(ell(q1),ell(q2),ell(q4)); if l1+l2+l4>5 {continue;}
    if (0..7).any(|k| (shift(q1,k)|shift(q2,2*k%7)|shift(q4,4*k%7)) & 0b1000001 == 0) {continue;}
    let c=(q1.count_ones(),q2.count_ones(),q4.count_ones());
    let e=prof.entry((l1,l2,l4)).or_insert((0,(9,9,9))); e.0+=1; if c.0+c.1+c.2 < e.1.0+e.1.1+e.1.2 { e.1=c; } }}}
  for (p,(n,c)) in prof { println!("profile (l1,l2,l4)={:?}: {} failing set-triples, min cardinalities {:?}", p, n, c); }
}
