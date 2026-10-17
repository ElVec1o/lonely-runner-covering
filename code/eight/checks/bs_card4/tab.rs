fn main(){
  let mut masks=vec![];
  for a in 0..5u32 { for r in 1..5u32 { for c in 0..8u32 {
    let mut q=[0u32;5]; q[1]=a; q[2]=(2*a+(c&1))%5; q[3]=(q[2]+a+((c>>1)&1))%5; q[4]=(q[3]+a+((c>>2)&1))%5;
    let mut m=0u32;
    for j in 1..5u32 { for k in 0..5u32 { let v=(q[j as usize]+k*((j*r)%5))%5; if v!=0&&v!=4 { m|=1<<((j-1)*5+k);} } }
    masks.push(m);}}}
  let mut d=masks.clone(); d.sort(); d.dedup();
  println!("[{}]", d.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(", "));
}
