// pool.rs -- column pool for the cover-capacity ILP.
// Parts = unions of minimal bad sets (edge-connected growth), size <= S, then extended by vertices
// that do not raise the capacity (closure up to size S). cost = alpha(U) = |U| - tau_U (exact).
// Writes binary file: per part: u64 mask, u8 cost. Prints stats. Cap on pool size is REPORTED as saturation.
// usage: pool m S cap out.bin
use std::collections::{HashMap,HashSet};
fn gcd(a:u64,b:u64)->u64{ if a==0{b}else{gcd(b%a,a)} }
pub fn edges(m:u64)->Vec<u64>{
    let n=2*m; let t=m+1; let qmax=2*n*t; let mut seen:HashSet<u64>=HashSet::new(); let mut raw=vec![];
    for q in 1..=qmax { for p in 0..q { if gcd(p,q)!=1 {continue;}
        let mut mask=0u64; let mut r=0u64;
        for x in 1..=n { r+=p; if r>=q {r-=q;} let mn=if r<q-r {r} else {q-r}; if t*mn<q { mask|=1u64<<(x-1);} }
        if mask!=0 && seen.insert(mask) { raw.push(mask);} }}
    raw.sort_by_key(|s|s.count_ones()); let mut sets:Vec<u64>=vec![];
    for &s in &raw { if !sets.iter().any(|&u| u&s==u) { sets.push(s);} } sets }
// min hitting number of edges contained in u, elements from u
fn tau(es:&[u64],u:u64,hit:u64,used:u32,best:&mut u32){
    if used>=*best {return;}
    let mut tg=0u64; let mut ts=99;
    for &e in es { if e&!u==0 && e&hit==0 { let c=e.count_ones(); if c<ts {ts=c;tg=e; if c==1{break;}} } }
    if tg==0 { *best=used; return; }
    let mut r=tg; while r!=0 { let b=r&r.wrapping_neg(); r^=b; tau(es,u,hit|b,used+1,best); }
}
pub fn alpha(es:&[u64],u:u64)->u32{ let mut b=99; tau(es,u,0,0,&mut b); u.count_ones()-b }
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let m:u64=a[1].parse().unwrap(); let s:u32=a[2].parse().unwrap(); let cap:usize=a[3].parse().unwrap();
    let es=edges(m); let n=2*m;
    let full:u64=(1u64<<n)-1;
    // grow unions of edges
    let mut seen:HashSet<u64>=HashSet::new(); let mut frontier:Vec<u64>=vec![];
    for &e in &es { if e.count_ones()<=s && seen.insert(e){ frontier.push(e);} }
    let mut all=frontier.clone(); let mut sat=false;
    while !frontier.is_empty() {
        let mut nxt=vec![];
        for &u in &frontier { for &e in &es {
            if e&u==0 {continue;} let w=u|e; if w==u || w.count_ones()>s {continue;}
            if seen.insert(w){ nxt.push(w); if seen.len()>cap {sat=true;} } } }
        if sat {break;} all.extend(nxt.iter().cloned()); frontier=nxt;
        eprintln!("unions so far {}",all.len());
    }
    eprintln!("edge-unions: {} saturated={}",all.len(),sat);
    // cost + closure (add vertices not raising alpha)
    let mut out:HashMap<u64,u32>=HashMap::new();
    for &u in &all { let c=alpha(&es,u);
        // closure by greedy full extension is not unique; enumerate extension sets up to size s by DFS
        let mut stack=vec![u]; let mut vis:HashSet<u64>=HashSet::new(); vis.insert(u);
        while let Some(x)=stack.pop() {
            let e=out.entry(x).or_insert(c); let _=e;
            if x.count_ones()>=s {continue;}
            let mut r=full&!x; while r!=0 { let b=r&r.wrapping_neg(); r^=b; let y=x|b;
                if vis.contains(&y){continue;} if alpha(&es,y)==c { vis.insert(y); stack.push(y);} }
        }
    }
    // keep only maximal-by-inclusion at same cost? keep all (LP dedupes), but drop dominated
    eprintln!("parts incl. extensions: {}",out.len());
    let mut hist:HashMap<(u32,u32),usize>=HashMap::new();
    for (&u,&c) in &out { *hist.entry((u.count_ones(),c)).or_default()+=1; }
    let mut h:Vec<_>=hist.into_iter().collect(); h.sort(); for ((sz,c),k) in h { eprintln!(" size {} cost {}: {}",sz,c,k); }
    let mut buf:Vec<u8>=vec![]; for (&u,&c) in &out { buf.extend_from_slice(&u.to_le_bytes()); buf.push(c as u8); }
    std::fs::write(&a[4],buf).unwrap();
}
