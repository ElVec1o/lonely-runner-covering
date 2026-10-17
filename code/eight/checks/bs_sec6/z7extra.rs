fn ell(s:u32)->u32{ if s==0 {return 0;} let mut best=8; for st in 0..7 { for l in 1..=7 { let mut iv=0u32; for t in 0..l { iv|=1<<((st+t)%7);} if s&!iv==0 && l<best {best=l;} } } best }
fn main(){
  let el=|s:u32| (0..7).filter(move |x| s>>x&1==1);
  let (mut fa,mut fb,mut na,mut nb)=(0,0,0,0);
  for s in 0..128u32 { let dd:Vec<u32>=el(s).flat_map(|x| el(s).map(move |y| (x+7-y)%7)).collect();
    if dd.iter().all(|d| [6,0,1].contains(d)) { na+=1; if ell(s)>2 {fa+=1;} }
    if dd.iter().all(|d| [5,6,0,1,2].contains(d)) { nb+=1; if ell(s)>3 {fb+=1; println!("R8b fail {:07b}",s);} } }
  println!("R8a: {} sets, {} with ell>2; R8b: {} sets, {} with ell>3", na,fa,nb,fb);
  let mut f61=0; let mut n61=0; for s in 0..128u32 { if s&1==1 || s.count_ones()!=4 {continue;} n61+=1;
    if !(1..7).any(|u| { let mut t=0u32; for x in el(s) { t|=1<<(x*u%7);} ell(t)==4 }) {f61+=1;} }
  println!("6.1: {} 4-subsets of Z7*, {} not rescalable to a length-4 interval", n61, f61);
}
