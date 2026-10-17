// exact check of paper Sec.5 Case 3 claim (12): pair same class mod 7, exists j<=5 with l(q(j x1),q(j x2))<=2
fn main(){ for m in 2..=3u32 { let n=7u64.pow(m+1); let p=7u64.pow(m); let mut bad=0; let mut tot=0;
  for x in 1..n { if x%7==0 {continue;} for y in (x+7..n).step_by(7) {
    tot+=1; let ok=(1..=5u64).any(|j| { let a=(j*x%n)/p; let b=(j*y%n)/p; let d=(a+7-b)%7; d<=1||d==6 });
    if !ok { bad+=1; if bad<=3 {println!("m={} fail x={} y={} q1=({},{})",m,x,y,x/p,y/p);} } } }
  println!("m={}: {} same-class pairs, {} violate (12)",m,tot,bad);} }
