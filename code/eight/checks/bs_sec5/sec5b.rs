fn qs(a: u64, eps: u32) -> [u64;6] { let mut v=[0u64;6]; v[1]=a%7; for j in 1..5 { v[j+1]=(v[j]+a+((eps>>(j-1))&1) as u64)%7; } v }
fn arc(vals: &[u64], len: u64) -> bool { (0..7).any(|t| vals.iter().all(|&v| (v+7-t)%7 < len)) }
fn main(){
    let g=|v:u64| v!=0 && v!=6;
    for t in 0..1u64 { for w1 in 0..7u64 { for w2 in 0..7u64 { for r1 in [2u64,4] { for r2 in [2u64,4] {
        if ![1u64,2,3,4].iter().any(|&o| { let kap=(o+7-t)%7; g((w1+kap*r1)%7) && g((w2+kap*r2)%7) }) { println!("Z3 fail t={} w1={} w2={} r1={} r2={}",t,w1,w2,r1,r2); } }}}}}
    let mut c=0; for a in 0..49u64 { for e in 0..(1u64<<8) {
        let el: Vec<[u64;6]> = (0..2).map(|i| qs((a/7u64.pow(i))%7, ((e>>(4*i))&15) as u32)).collect();
        if !(1..=5).any(|j| arc(&el.iter().map(|x|x[j]).collect::<Vec<_>>(),2)) { c+=1; if c<=8 {println!("F3 fail a=({},{}) eps=({:04b},{:04b}) q1..5 {:?} {:?}", a%7, a/7, e&15, e>>4, &el[0][1..], &el[1][1..]);} } }}
}
