// xc.rs -- exact search over the zero-reduced-cost columns. Tight rows (dual>0) covered exactly once,
// other rows (except free singletons listed) covered >=1. Columns from .kept.npy (mask u64 LE, cost u8).
// usage: xc m kept.npy tightfile nodecap [free_rows comma 1-based, default 1,m+1]
// Progress every 10M nodes; prints solution masks. Node cap hit => UNDECIDED (never reported as none).
use std::time::Instant;
struct S{cols:Vec<(u64,u8)>,byrow:Vec<Vec<u32>>,tight:u64,req:u64,nodes:u64,cap:u64,sol:Vec<u32>,found:bool,t0:Instant,capped:bool,nfound:u64}
impl S{
 fn rec(&mut self,cov:u64,ctop:u64){
  if self.found||self.capped {return;}
  self.nodes+=1; if self.nodes>self.cap {self.capped=true;return;}
  if self.nodes%20_000_000==0 { eprintln!("nodes {}M depth {} elapsed {:.0}s",self.nodes/1_000_000,self.sol.len(),self.t0.elapsed().as_secs_f64()); }
  let need=self.req&!cov; if need==0 { self.found=true; return; }
  // choose required uncovered row with fewest candidates
  let mut best=64usize; let mut bc=usize::MAX; let mut r=need;
  while r!=0 { let b=r.trailing_zeros() as usize; r&=r-1;
    let mut c=0usize; for &j in &self.byrow[b] { let (mk,_)=self.cols[j as usize]; if mk&self.tight&ctop==0 {c+=1; if c>=bc {break;}} }
    if c<bc {bc=c;best=b; if c==0 {return;}} }
  let cand:Vec<u32>=self.byrow[best].iter().cloned().filter(|&j| self.cols[j as usize].0&self.tight&ctop==0).collect();
  for j in cand { let mk=self.cols[j as usize].0; self.sol.push(j);
    self.rec(cov|mk,ctop|(mk&self.tight)); if self.found {return;} self.sol.pop(); if self.capped {return;} }
 }
}
fn main(){
 let a:Vec<String>=std::env::args().collect(); let m:usize=a[1].parse().unwrap(); let n=2*m;
 let d=std::fs::read(&a[2]).unwrap(); let hl=u16::from_le_bytes([d[8],d[9]]) as usize; let body=&d[10+hl..];
 let mut cols=vec![]; for ch in body.chunks(9) { cols.push((u64::from_le_bytes(ch[..8].try_into().unwrap()),ch[8])); }
 let tight_rows:Vec<usize>=std::fs::read_to_string(&a[3]).unwrap().split_whitespace().map(|x|x.parse().unwrap()).collect();
 let mut tight=0u64; for r in &tight_rows { tight|=1u64<<r; }
 let cap:u64=a[4].parse().unwrap();
 let free:Vec<usize>=if a.len()>5 { a[5].split(',').map(|x|x.parse::<usize>().unwrap()-1).collect() } else { vec![0,m] };
 let mut req=(1u64<<n)-1; for f in &free { req&=!(1u64<<f); }
 let mut byrow=vec![vec![];n]; for (j,&(mk,_)) in cols.iter().enumerate() { for b in 0..n { if mk>>b&1==1 { byrow[b].push(j as u32);} } }
 eprintln!("cols {} tight {:?}",cols.len(),tight_rows.iter().map(|x|x+1).collect::<Vec<_>>());
 let mut s=S{cols,byrow,tight,req,nodes:0,cap,sol:vec![],found:false,t0:Instant::now(),capped:false,nfound:0};
 s.rec(0,0);
 if s.found { println!("FOUND after {} nodes",s.nodes); let mut sum=0u32; for &j in &s.sol { let (mk,c)=s.cols[j as usize]; sum+=c as u32; println!("{} {}",mk,c);} 
   // free singletons
   for f in &free { println!("{} 0",1u64<<f); } eprintln!("sum cost of parts {}",sum);
 } else if s.capped { println!("UNDECIDED: node cap {} hit ({:.0}s)",cap,s.t0.elapsed().as_secs_f64()); }
 else { println!("EXHAUSTED: no solution among zero-reduced-cost columns, nodes {} ({:.0}s)",s.nodes,s.t0.elapsed().as_secs_f64()); }
}
