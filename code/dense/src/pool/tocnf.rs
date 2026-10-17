// tocnf.rs -- exact-cover-with-optional-rows over zero-reduced-cost columns -> DIMACS (Sinz sequential AMO).
// usage: tocnf m kept.npy tightfile out.cnf out.map   ; map = one line per column var: "mask cost"
fn main(){
 let a:Vec<String>=std::env::args().collect(); let m:usize=a[1].parse().unwrap(); let n=2*m;
 let d=std::fs::read(&a[2]).unwrap(); let hl=u16::from_le_bytes([d[8],d[9]]) as usize; let body=&d[10+hl..];
 let mut cols=vec![]; for ch in body.chunks(9) { cols.push((u64::from_le_bytes(ch[..8].try_into().unwrap()),ch[8])); }
 let tr0:Vec<usize>=std::fs::read_to_string(&a[3]).unwrap().split_whitespace().map(|x|x.parse().unwrap()).collect();
 let mut tm=0u64; for r in &tr0 { tm|=1u64<<r; }
 { use std::collections::HashMap; let mut g:HashMap<u64,Vec<(u64,u8)>>=HashMap::new(); for &(mk,c) in &cols { g.entry(mk&tm).or_default().push((mk,c)); }
   let before=cols.len(); cols.clear();
   for (_,mut v) in g { v.sort_by_key(|x| std::cmp::Reverse(x.0.count_ones())); let mut keep:Vec<(u64,u8)>=vec![];
     for (mk,c) in v { if !keep.iter().any(|&(k,_)| mk&!k==0) { keep.push((mk,c)); } } cols.extend(keep); }
   cols.sort(); eprintln!("dominance: {} -> {} columns, distinct tight parts kept",before,cols.len()); }
 let tr:Vec<usize>=std::fs::read_to_string(&a[3]).unwrap().split_whitespace().map(|x|x.parse().unwrap()).collect();
 let mut tight=vec![false;n]; for r in &tr {tight[*r]=true;}
 let free=[0usize,m];
 let mut byrow=vec![vec![];n]; for (j,&(mk,_)) in cols.iter().enumerate(){ for b in 0..n { if mk>>b&1==1 { byrow[b].push(j as i64+1);} } }
 let mut nv=cols.len() as i64; let mut cl:Vec<Vec<i64>>=vec![];
 for r in 0..n { if free.contains(&r){continue;} let v=&byrow[r]; if v.is_empty(){ cl.push(vec![]); continue; }
   cl.push(v.clone()); // at least one
   if tight[r] { // at most one, sequential counter
     let k=v.len(); if k<2 {continue;} let s0=nv; nv+=(k as i64)-1;
     cl.push(vec![-v[0],s0+1]);
     for i in 1..k-1 { let si=s0+1+i as i64; let sp=s0+i as i64; cl.push(vec![-v[i],si]); cl.push(vec![-sp,si]); cl.push(vec![-v[i],-sp]); }
     cl.push(vec![-v[k-1],-(s0+(k as i64)-1)]);
   } }
 use std::io::Write; let mut f=std::io::BufWriter::new(std::fs::File::create(&a[4]).unwrap());
 writeln!(f,"p cnf {} {}",nv,cl.len()).unwrap();
 for c in &cl { for l in c { write!(f,"{} ",l).unwrap(); } writeln!(f,"0").unwrap(); }
 let mut g=std::io::BufWriter::new(std::fs::File::create(&a[5]).unwrap()); for &(mk,c) in &cols { writeln!(g,"{} {}",mk,c).unwrap(); }
 eprintln!("vars {} clauses {} cols {}",nv,cl.len(),cols.len());
}
