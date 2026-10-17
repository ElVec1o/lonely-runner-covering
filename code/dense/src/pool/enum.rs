// enum.rs -- minimal bad sets of the dense window [1,2m] with witness times p/q (exact integers).
// usage: enum m   -> prints "mask p q size elems" per minimal set. u64 masks (bit x-1), m<=31.
use std::collections::HashMap;
fn gcd(a:u64,b:u64)->u64{ if a==0{b}else{gcd(b%a,a)} }
fn main(){
    let m:u64=std::env::args().nth(1).unwrap().parse().unwrap();
    let n=2*m; let t=m+1; assert!(n<=63);
    let qmax=2*n*t;
    let mut seen:HashMap<u64,(u64,u64)>=HashMap::new();
    for q in 1..=qmax { for p in 0..q {
        if gcd(p,q)!=1 {continue;}
        let mut mask=0u64; let mut r=0u64;
        for x in 1..=n { r+=p; if r>=q {r-=q;} let mn=if r<q-r {r} else {q-r}; if t*mn<q { mask|=1u64<<(x-1);} }
        if mask!=0 { seen.entry(mask).or_insert((p,q)); }
    }}
    let mut raw:Vec<(u64,(u64,u64))>=seen.into_iter().collect();
    raw.sort_by_key(|&(s,(_,q))|(s.count_ones(),q,s));
    let mut sets:Vec<(u64,(u64,u64))>=vec![];
    for &(s,w) in &raw { if !sets.iter().any(|&(u,_)| u&s==u) { sets.push((s,w)); } }
    for (s,(p,q)) in &sets {
        let el:Vec<String>=(1..=n).filter(|x| s>>(x-1)&1==1).map(|x|x.to_string()).collect();
        println!("{} {} {} {} {}",s,p,q,s.count_ones(),el.join(","));
    }
}
