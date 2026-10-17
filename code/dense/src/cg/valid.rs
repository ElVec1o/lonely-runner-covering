// Exact validity oracle: tau(S) >= |L| (L = S cap Low), edges inside S, u128 masks.
pub struct Ctx { pub m:u32, pub n:u32, pub es:Vec<u128>, pub by_min:Vec<Vec<u32>>, pub adj:Vec<Vec<u32>>, pub low:u128, pub high:u128, pub full:u128 }
impl Ctx {
    pub fn new(m:u32, es:Vec<u128>)->Ctx{
        let n=2*m; let mut by_min=vec![vec![];n as usize]; let mut adj=vec![vec![];n as usize];
        for (i,&e) in es.iter().enumerate(){ by_min[e.trailing_zeros() as usize].push(i as u32);
            let mut r=e; while r!=0 { let b=r.trailing_zeros(); r&=r-1; adj[b as usize].push(i as u32);} }
        let full=if n==128 {!0u128} else {(1u128<<n)-1};
        let low=(1u128<<(m+1))-1; let high=full&!low;
        Ctx{m,n,es,by_min,adj,low,high,full}
    }
    pub fn local(&self,s:u128,out:&mut Vec<u128>){ out.clear(); let mut r=s;
        while r!=0 { let v=r.trailing_zeros() as usize; r&=r-1; for &i in &self.by_min[v] { let e=self.es[i as usize]; if e&!s==0 { out.push(e);} } } }
    pub fn y_independent(&self)->bool{ self.es.iter().all(|&e| e&!self.high!=0) }
    // exact: is S a valid block (alpha(S)==|S cap Y|)?  Requires Y independent.
    pub fn valid(&self,s:u128,buf:&mut Vec<u128>)->bool{
        let l=(s&self.low).count_ones(); if l==0 {return true;}
        self.local(s,buf); !hs_exists(buf,0,l-1) }
}
pub fn hs_exists(es:&[u128],hit:u128,k:u32)->bool{
    let mut best=0u128; let mut bc=200u32;
    for &e in es { if e&hit==0 { let c=e.count_ones(); if c<bc {bc=c;best=e;} } }
    if best==0 {return true;}
    if k==0 {return false;}
    let mut used=0u128; let mut cnt=0u32;
    for &e in es { if e&hit==0 && e&used==0 { used|=e; cnt+=1; } }
    if cnt>k {return false;}
    let mut r=best; while r!=0 { let b=r&r.wrapping_neg(); r^=b; if hs_exists(es,hit|b,k-1){return true;} }
    false }
