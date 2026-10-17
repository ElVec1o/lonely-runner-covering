// Mirrors of the planned Lean decide statements (Nat arithmetic, values < 7).
const C: [[u64;5];10] = [[0,0,0,0,0],[0,0,0,0,1],[0,0,0,1,1],[0,0,1,1,1],[0,0,1,1,2],[0,1,1,2,2],[0,1,1,2,3],[0,1,2,2,3],[0,1,2,3,3],[0,1,2,3,4]];
fn qm(a:u64,p:usize,j:u64)->u64{ (j*a + C[p][(j-1) as usize])%7 }
fn gd(v:u64)->bool{ v%7!=0 && v%7!=6 }
fn arc(v:&[u64],len:u64)->Option<u64>{ (0..7).find(|&t| v.iter().all(|&x| (x+7-t)%7 < len)) }
fn main(){
  // Farey: all b < M: (floor(jb/M))_{j=2..5} in C
  for m in 1..=5u32 { let mm=7u64.pow(m); let mut bad=0; for b in 0..mm { let c:[u64;5]=[0,2*b/mm,3*b/mm,4*b/mm,5*b/mm]; if !C.contains(&c){bad+=1;} } println!("Farey M=7^{}: {} bad", m, bad); }
  // F1a/F1b with a1=0
  let (mut nf, mut bad1) = (0,0);
  for a in 0..343u64 { let v=[0,a%7,(a/7)%7,a/49]; if arc(&v,5).is_some(){continue;} nf+=1;
    for pc in 0..10000usize { let p=[pc%10,(pc/10)%10,(pc/100)%10,pc/1000];
      if !(1..=4u64).any(|j| arc(&(0..4).map(|i| qm(v[i],p[i],j)).collect::<Vec<_>>(),5).is_some()) { bad1+=1; } } }
  println!("F1: {} non-arc a-tuples (expect 24), {} failures", nf, bad1);
  let mut bad2=0; for a in 0..49u64 { let v=[0,a%7,a/7]; for pc in 0..1000usize { let p=[pc%10,(pc/10)%10,pc/100];
      if !(1..=4u64).any(|j| arc(&(0..3).map(|i| qm(v[i],p[i],j)).collect::<Vec<_>>(),4).is_some()) { bad2+=1; } } }
  println!("F2: {} failures", bad2);
  let mut bad3=0; for a in 0..7u64 { for p0 in 0..10 { for p1 in 0..10 { let v=[0,a];let p=[p0,p1];
      if !(1..=5u64).any(|j| arc(&(0..2).map(|i| qm(v[i],p[i],j)).collect::<Vec<_>>(),2).is_some()) { bad3+=1; } }}}
  println!("F3: {} failures", bad3);
  // Z1': t, J in 1..6: exists k: all u with (u-t)%7<5 good(u+kJ)
  let mut z=0; for t in 0..7u64 { for jj in 1..7u64 { if !(0..7u64).any(|k| (0..7u64).all(|u| (u+7-t)%7>=5 || gd(u+k*jj))) {z+=1;} }}
  println!("Z1: {} failures", z);
  let mut z=0; for t in 0..7u64 { for w in 0..7u64 { for jj in 1..7u64 { for rr in [2*jj%7, 4*jj%7] {
     if !(0..7u64).any(|k| (0..7u64).all(|u| (u+7-t)%7>=4 || gd(u+k*jj)) && gd(w+k*rr)) {z+=1;} }}}}
  println!("Z2: {} failures", z);
  let mut z=0; let mut znc=0; for t in 0..7u64 { for w1 in 0..7u64 { for w2 in 0..7u64 { for jj in 1..7u64 {
     for (r1,r2) in [(2*jj%7,2*jj%7),(2*jj%7,4*jj%7),(4*jj%7,2*jj%7)] {
     if !(0..7u64).any(|k| (0..7u64).all(|u| (u+7-t)%7>=2 || gd(u+k*jj)) && gd(w1+k*r1) && gd(w2+k*r2)) {z+=1;} }
     let (r1,r2)=(4*jj%7,4*jj%7); if !(0..7u64).any(|k| (0..7u64).all(|u| (u+7-t)%7>=2 || gd(u+k*jj)) && gd(w1+k*r1) && gd(w2+k*r2)) {znc+=1;} }}}}
  println!("Z3: {} failures; NC ratios (4,4): {} failures", z, znc);
  // dispatch: 4 classes in {1,2,4}: some base b gives pattern in allowed set
  let allowed=[[4,0,0],[3,1,0],[3,0,1],[2,2,0],[2,1,1]]; let mut dz=0;
  for code in 0..81 { let mut c=code; let mut cnt=[0;7]; for _ in 0..4 { cnt[[1,2,4][c%3]]+=1; c/=3; }
    if ![1usize,2,4].iter().any(|&b| allowed.contains(&[cnt[b],cnt[2*b%7],cnt[4*b%7]])) {dz+=1;} }
  println!("dispatch: {} uncovered of 81", dz);
}
