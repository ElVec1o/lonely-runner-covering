// connected components of the minimal-edge hypergraph restricted to Low' u Y: xc comp m
#[path="../cg/edges.rs"] mod edges;
use edges::*;
fn main(){ let m:u32=std::env::args().nth(1).unwrap().parse().unwrap(); let ed=enumerate(m,8); let n=2*m as usize;
 let mut p:Vec<usize>=(0..n).collect(); fn f(p:&mut Vec<usize>,x:usize)->usize{ let mut r=x; while p[r]!=r {r=p[r];} let mut c=x; while p[c]!=r {let nx=p[c];p[c]=r;c=nx;} r }
 for &e in &ed.es { let v:Vec<usize>=(0..n).filter(|&b|e>>b&1==1).collect(); for w in v.windows(2){ let a=f(&mut p,w[0]); let b=f(&mut p,w[1]); p[a]=b; } }
 let mut comps:std::collections::BTreeMap<usize,Vec<usize>>=Default::default(); for x in 0..n { let r=f(&mut p,x); comps.entry(r).or_default().push(x+1); }
 let q=2*m as u64+1; println!("m={} q={} components {}",m,q,comps.len());
 for (_,v) in &comps { let lo=v.iter().filter(|&&x|x as u32<=m+1).count(); let hi=v.len()-lo; let g:Vec<u64>=v.iter().map(|&x|gcd(x as u64,q)).collect(); let mut gs=g.clone(); gs.sort(); gs.dedup();
   println!("  size {} low {} Y {} gcds {:?} first {:?}",v.len(),lo,hi,gs,&v[..v.len().min(8)]); } }
