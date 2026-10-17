// Minimal bad sets of the dense window [1,2m] (exact integers, u128 masks, bit x-1 <-> velocity x).
use std::collections::HashMap;
pub fn gcd(a:u64,b:u64)->u64{ if a==0{b}else{gcd(b%a,a)} }
pub struct Edges { pub m:u32, pub n:u32, pub es:Vec<u128>, pub wit:Vec<(u32,u32)>, pub distinct:usize }
pub fn bit(x:u32)->u128{ 1u128<<(x-1) }
pub fn enumerate(m:u32, nth:usize)->Edges{
    let n=2*m; let t=(m+1) as u64; assert!(n<=124);
    let qmax=2*(n as u64)*t;
    let mut hs=vec![];
    for tid in 0..nth { hs.push(std::thread::spawn(move||{
        let mut seen:HashMap<u128,(u32,u32)>=HashMap::new();
        let mut q=1+tid as u64;
        while q<=qmax {
            for p in 1..=q/2 { if gcd(p,q)!=1 {continue;}
                let mut mask=0u128; let mut r=0u64;
                for x in 1..=n { r+=p; if r>=q {r-=q;} let mn=if r<q-r {r} else {q-r}; if t*mn<q { mask|=1u128<<(x-1);} }
                if mask!=0 { seen.entry(mask).or_insert((p as u32,q as u32)); } }
            q+=nth as u64; }
        seen })); }
    let mut all:HashMap<u128,(u32,u32)>=HashMap::new();
    for h in hs { for (k,v) in h.join().unwrap() { let e=all.entry(k).or_insert(v); if (v.1,v.0)<(e.1,e.0) {*e=v;} } }
    let distinct=all.len();
    let mut raw:Vec<(u128,(u32,u32))>=all.into_iter().collect();
    raw.sort_by_key(|&(s,(p,q))|(s.count_ones(),q,p,s));
    let mut es:Vec<u128>=vec![]; let mut wit=vec![];
    for &(s,w) in &raw { if !es.iter().any(|&u| u&s==u) { es.push(s); wit.push(w);} }
    Edges{m,n,es,wit,distinct}
}
