// Exact cover search over the block family: cover Low by blocks (T_j,L_j), T_j pairwise disjoint in Y.
// Branch on the uncovered low with fewest available blocks; in branch i the earlier candidates 0..i are EXCLUDED
// (sound and complete: a solution containing candidate j<i was explored in branch j). Each block set is found once.
// Pruning (exact integers): (a) a low with no available block; (b) share bound sum_l min_{avail b ni l} |T_b|/|L_b| <= free Y.
use crate::common::*; use std::time::Instant;
pub const SC:u64=720720; // lcm(1..16)
pub struct Fam { pub t:Vec<u128>, pub l:Vec<u128>, pub tc:Vec<u32>, pub lc:Vec<u32>, pub share:Vec<u64>, pub by_low:Vec<Vec<u32>>, pub by_y:Vec<Vec<u32>>, pub prof:Vec<i32> }
pub fn make_pos(f:&Fam)->(Vec<(u128,i32)>,u128){ let pos:Vec<(u128,i32)>=(0..f.t.len()).filter(|&i|f.lc[i]>f.tc[i]).map(|i|(f.t[i],f.lc[i] as i32-f.tc[i] as i32)).collect(); let yp=pos.iter().fold(0u128,|x,&(t,_)|x|t); (pos,yp) }
pub fn make_fam(blocks:&[(u128,u128)],low:u128,maxpart:u32,seed:u64)->Fam{
    let maxp:i32=std::env::var("XC_MAXPROFIT").ok().and_then(|s|s.parse().ok()).unwrap_or(99);
    let minp:i32=std::env::var("XC_MINPROFIT").ok().and_then(|s|s.parse().ok()).unwrap_or(-99);
    let mut v:Vec<(u128,u128)>=blocks.iter().cloned().filter(|&(t,l)| l!=0 && t!=0 && t.count_ones()+l.count_ones()<=maxpart && (l.count_ones() as i32)-(t.count_ones() as i32)>=minp && (l.count_ones() as i32)-(t.count_ones() as i32)<=maxp).collect();
    // deterministic order: share asc, |L| desc, then masks; random tie-break if seed!=0
    let key=|b:&(u128,u128)|->(u64,u32,u128,u128){ let (tc,lc)=(b.0.count_ones() as u64,b.1.count_ones()); (tc*SC/(lc as u64),32-lc,b.0,b.1) };
    v.sort_by_key(key);
    if seed!=0 { let mut r=crate::search::Rn(seed|1); for i in (1..v.len()).rev(){ let j=(r.next()%(i as u64+1)) as usize; v.swap(i,j);} }
    let nlow=(128-low.leading_zeros()) as usize; let mut by_low=vec![vec![];nlow];
    let (mut t,mut l,mut tc,mut lc,mut sh)=(vec![],vec![],vec![],vec![],vec![]);
    for (i,&(a,b)) in v.iter().enumerate(){ assert!(b.count_ones()<=16); t.push(a); l.push(b); tc.push(a.count_ones()); lc.push(b.count_ones());
        sh.push(a.count_ones() as u64*SC/(b.count_ones() as u64)); assert!(a.count_ones() as u64*SC%(b.count_ones() as u64)==0);
        for x in bits(b){ by_low[x as usize].push(i as u32); } }
    let prof:Vec<i32>=(0..t.len()).map(|i|lc[i] as i32-tc[i] as i32).collect();
    let mut by_y=vec![vec![];128]; for (i,&x) in t.iter().enumerate(){ for y in bits(x){ by_y[y as usize].push(i as u32); } }
    for lst in by_low.iter_mut().chain(by_y.iter_mut()){ lst.sort_by_key(|&i|(std::cmp::Reverse(prof[i as usize]),i)); }
    Fam{t,l,tc,lc,share:sh,by_low,by_y,prof}
}
pub struct Rn(pub u64);
impl Rn{ pub fn next(&mut self)->u64{ let mut x=self.0; x^=x<<13; x^=x>>7; x^=x<<17; self.0=x; x.wrapping_mul(0x2545F4914F6CDD1D) } }
pub struct Srch<'a>{ pub f:&'a Fam, pub low:u128, pub highcnt:u32, pub excl:Vec<bool>, pub used:u128, pub cov:u128,
    pub chosen:Vec<u32>, pub nodes:u64, pub nodecap:u64, pub found:u64, pub maxsol:u64, pub sols:Vec<Vec<u32>>,
    pub resume:Vec<usize>, pub replay:bool, pub cur:Vec<(usize,usize)>, pub t0:Instant, pub last_rep:Instant, pub last_ck:Instant,
    pub ckpath:String, pub capped:bool, pub deadline:f64, pub frac0:f64, pub start_el:f64, pub m:u32, pub rnd:Option<Rn>, pub bound_on:bool, pub prunes:[u64;3], pub pos:Vec<(u128,i32)>, pub gcache:std::collections::HashMap<u128,i32>, pub ypos:u128, pub use_rho:bool, pub high:u128, pub order:u8, pub only_top:Option<usize>, pub top_n:usize, pub stop:Option<&'a std::sync::atomic::AtomicBool>, pub gnodes:Option<&'a std::sync::atomic::AtomicU64> }
impl<'a> Srch<'a>{
    // upper bound on total profit obtainable from pairwise Y-disjoint positive blocks avoiding `used` (exact DFS if small)
    fn gbound(&mut self,used:u128)->i32{
        let key=used&self.ypos; if let Some(&g)=self.gcache.get(&key){return g;}
        let mut av:Vec<(u128,i32)>=self.pos.iter().cloned().filter(|&(t,_)|t&used==0).collect();
        av.sort(); av.dedup_by(|a,b|{ if a.0==b.0 { if a.1>b.1 {b.1=a.1;} true } else {false} });
        let yp:u128=av.iter().fold(0,|x,&(t,_)|x|t);
        let g= if av.len()>250 { let mx=av.iter().map(|&(t,p)|(p as f64)/(t.count_ones() as f64)).fold(0.0,f64::max); (yp.count_ones() as f64*mx).floor() as i32 }
               else { fn dfs(av:&[(u128,i32)],i:usize,used:u128,acc:i32,best:&mut i32,rest:&[i32]){ if acc>*best {*best=acc;} if i>=av.len()||acc+rest[i]<=*best {return;}
                         if av[i].0&used==0 { dfs(av,i+1,used|av[i].0,acc+av[i].1,best,rest); } dfs(av,i+1,used,acc,best,rest); }
                      let mut rest=vec![0i32;av.len()+1]; for i in (0..av.len()).rev(){ rest[i]=rest[i+1]+av[i].1; } let mut best=0; dfs(&av,0,0,0,&mut best,&rest); best };
        if self.gcache.len()>500_000 { self.gcache.clear(); }
        self.gcache.insert(key,g); g }
    fn frac(&self)->f64{ let mut f=0.0; let mut w=1.0; for &(i,n) in &self.cur { if n==0 {break;} f+=w*(i as f64)/(n as f64); w/=n as f64; } f }
    fn save(&self){ if self.ckpath.is_empty() {return;} let s:Vec<String>=self.cur.iter().map(|&(i,_)|i.to_string()).collect();
        let txt=format!("nodes {}\nfound {}\npath {}\n",self.nodes,self.found,s.join(" ")); atomic_write(&self.ckpath,txt.as_bytes()); }
    pub fn rec(&mut self,depth:usize)->bool{
        self.nodes+=1;
        if self.nodes>self.nodecap {self.capped=true;if self.rnd.is_none(){self.save();}return false;}
        if self.nodes&0x3FFF==0 {
            if let Some(g)=self.gnodes { g.fetch_add(0x4000,std::sync::atomic::Ordering::Relaxed); }
            if let Some(st)=self.stop { if st.load(std::sync::atomic::Ordering::Relaxed) { self.capped=true; return false; } }
            let el=self.t0.elapsed().as_secs_f64();
            if el>self.deadline {self.capped=true;if self.rnd.is_none(){self.save();}return false;}
            if self.last_rep.elapsed().as_secs_f64()>=30.0 { self.last_rep=Instant::now();
                let fr=self.frac(); let prog=(fr-self.frac0).max(1e-18); let run=el-self.start_el;
                let eta= if fr>self.frac0 { run*(1.0-fr)/prog } else {f64::NAN};
                println!("m={} nodes {:.2}M depth {} found {} frac {:.3e} rate {:.2}Mn/s eta {:.0}s (estimate) rss {:.2}GB",self.m,self.nodes as f64/1e6,depth,self.found,fr,self.nodes as f64/1e6/el.max(1e-9),eta,rss()); }
            if self.rnd.is_none() && self.last_ck.elapsed().as_secs_f64()>=120.0 { self.last_ck=Instant::now(); self.save(); }
        }
        let unc=self.low&!self.cov;
        if unc==0 { self.found+=1; if self.sols.len()<self.maxsol as usize { self.sols.push(self.chosen.clone()); } return self.found>=self.maxsol; }
        let freey=(self.highcnt-self.used.count_ones()) as u64;
        let rho:i32=freey as i32-unc.count_ones() as i32;
        let gm= if self.use_rho { self.gbound(self.used) } else { 1000 };
        if rho+gm<0 { self.prunes[2]+=1; return false; }
        // scan (lists sorted by profit desc: stop when profit + rho + gm < 0)
        let slack=rho+gm;
        let mut best_l=usize::MAX; let mut best_c=usize::MAX; let mut bound=0u64; let mut yav=0u128;
        let mut r=unc; while r!=0 { let l=r.trailing_zeros() as usize; r&=r-1;
            let mut c=0usize; let mut ms=u64::MAX;
            for &b in &self.f.by_low[l] { let bi=b as usize; if self.f.prof[bi]+slack<0 {break;}
                if !self.excl[bi] && self.f.t[bi]&self.used==0 {
                let dl=(self.f.l[bi]&unc).count_ones() as i32-self.f.tc[bi] as i32; if dl+slack<0 {continue;}
                c+=1; yav|=self.f.t[bi]; let s=self.f.share[bi]; if s<ms {ms=s;} } }
            if c==0 { self.prunes[0]+=1; return false; }
            bound+=ms; if c<best_c {best_c=c;best_l=l;} }
        { let dead=(self.high&!self.used&!yav).count_ones() as i32; if dead>slack { self.prunes[2]+=1; return false; } }
        if self.bound_on && bound>freey*SC { self.prunes[1]+=1; return false; }
        // item choice: a low (default) or, when slack==0 (every free y must be used), the free y with fewest candidates
        let mut item_is_y=false; let mut best_y=usize::MAX;
        if slack==0 { let mut by=usize::MAX; let mut yr=self.high&!self.used; while yr!=0 { let y=yr.trailing_zeros() as usize; yr&=yr-1; let mut c=0usize;
                for &b in &self.f.by_y[y] { let bi=b as usize; if self.f.prof[bi]<0 {break;}
                    if !self.excl[bi] && self.f.t[bi]&self.used==0 && (self.f.l[bi]&unc).count_ones() as i32>=self.f.tc[bi] as i32 { c+=1; if c>=best_c {break;} } }
                if c<best_c { best_c=c; by=y; item_is_y=true; if c==0 {self.prunes[0]+=1; return false;} } }
            if item_is_y { best_y=by; } }
        let mut cand:Vec<u32>=Vec::with_capacity(best_c);
        if item_is_y { for &b in &self.f.by_y[best_y] { let bi=b as usize; if self.f.prof[bi]<0 {break;}
                if !self.excl[bi] && self.f.t[bi]&self.used==0 && (self.f.l[bi]&unc).count_ones() as i32>=self.f.tc[bi] as i32 { cand.push(b); } } }
        else { for &b in &self.f.by_low[best_l] { let bi=b as usize; if self.f.prof[bi]+slack<0 {break;}
            if !self.excl[bi] && self.f.t[bi]&self.used==0 {
            let dl=(self.f.l[bi]&unc).count_ones() as i32-self.f.tc[bi] as i32; if dl+slack<0 {continue;} cand.push(b); } } }
        if let Some(r)=self.rnd.as_mut() { for i in (1..cand.len()).rev(){ let j=(r.next()%(i as u64+1)) as usize; cand.swap(i,j);} let pf=&self.f.prof; match self.order { 0=>cand.sort_by_key(|&b|std::cmp::Reverse(pf[b as usize])), 1=>{}, _=>cand.sort_by_key(|&b|pf[b as usize]) } }
        let n=cand.len();
        let mut start=0; let mut replaying=false;
        if depth==0 { self.top_n=n; if let Some(i)=self.only_top { start=i.min(n); } }
        if self.replay && depth<self.resume.len() { start=self.resume[depth].min(n); replaying=true; } else { self.replay=false; }
        let mut exs:Vec<u32>=vec![]; for j in 0..start { self.excl[cand[j] as usize]=true; exs.push(cand[j]); }
        let mut result=false;
        for i in start..n {
            if depth==0 && self.only_top.is_some() && i>start { break; }
            if i>start { self.replay=false; }
            let b=cand[i] as usize; let (ou,oc)=(self.used,self.cov);
            self.used|=self.f.t[b]; self.cov|=self.f.l[b]; self.chosen.push(b as u32);
            if self.cur.len()<=depth { self.cur.push((i,n)); } else { self.cur[depth]=(i,n); } self.cur.truncate(depth+1);
            let got=self.rec(depth+1);
            self.chosen.pop(); self.used=ou; self.cov=oc;
            if got || self.capped { result=got; break; }
            self.excl[b]=true; exs.push(b as u32);
        }
        let _=replaying;
        for b in exs { self.excl[b as usize]=false; }
        self.cur.truncate(depth);
        result
    }
}
