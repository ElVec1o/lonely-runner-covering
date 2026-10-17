fn arc(v:&[u64],len:u64)->bool{ (0..7).any(|t| v.iter().all(|&x| (x+7-t)%7 < len)) }
fn main(){ let mut b=vec![]; for a in 0..343u64 { if !arc(&[0,a%7,(a/7)%7,a/49],5) { b.push(a);} } println!("{:?}",b); }
