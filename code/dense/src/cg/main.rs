// cg: column generation / restricted-master search for cover-capacity certificates (see CG_DESIGN.md)
// usage:
//   cg edges m
//   cg run m seed smax total_s mip_s attempts [cap_gb]
//   cg check m parts.txt out.lean
mod edges; mod valid; mod gen; mod check;
use std::collections::HashSet; use std::time::Instant; use std::io::Write;
use edges::*; use valid::*; use gen::*;
const DIR:&str=".";
#[repr(C)] struct RU { ut:[i64;2], st:[i64;2], maxrss:i64, rest:[i64;13] }
extern "C" { fn getrusage(who:i32,u:*mut RU)->i32; }
fn rss()->f64{ let mut u=RU{ut:[0;2],st:[0;2],maxrss:0,rest:[0;13]}; unsafe{getrusage(0,&mut u);} u.maxrss as f64/1e9 }
fn watchdog(cap:f64){ std::thread::spawn(move||loop{ std::thread::sleep(std::time::Duration::from_secs(2));
    let r=rss(); if r>cap { eprintln!("WATCHDOG: peak RSS {:.2} GB > cap {:.2} GB, exiting",r,cap); std::process::exit(3);} }); }
fn write_cols(path:&str,pool:&[u128]){ let mut b=Vec::with_capacity(pool.len()*16); for &c in pool { b.extend_from_slice(&c.to_le_bytes()); }
    let tmp=format!("{}.tmp",path); std::fs::write(&tmp,b).unwrap(); std::fs::rename(&tmp,path).unwrap(); }
fn read_cols(path:&str)->Vec<u128>{ match std::fs::read(path){ Ok(b)=>b.chunks_exact(16).map(|c|u128::from_le_bytes(c.try_into().unwrap())).collect(), Err(_)=>vec![] } }
fn read_parts(path:&str)->Vec<(u128,u32)>{ std::fs::read_to_string(path).unwrap().lines().filter(|l|!l.trim().is_empty()).map(|l|{let mut s=l.split_whitespace(); (s.next().unwrap().parse().unwrap(), s.next().unwrap().parse().unwrap())}).collect() }
fn pyrun(args:&[String])->bool{ std::process::Command::new("python3").arg("-u").arg("../../code/dense/src/cg/lp.py".to_string()).args(args).status().map(|s|s.success()).unwrap_or(false) }
fn parse_out(path:&str)->std::collections::HashMap<String,String>{ let mut h=std::collections::HashMap::new();
    for l in std::fs::read_to_string(path).unwrap_or_default().lines(){ let mut it=l.splitn(2,' '); let k=it.next().unwrap_or("").to_string(); h.insert(k,it.next().unwrap_or("").to_string()); } h }
fn main(){
    let a:Vec<String>=std::env::args().collect();
    match a[1].as_str() {
        "edges"=>{ let m:u32=a[2].parse().unwrap(); let t=Instant::now(); let ed=enumerate(m,8);
            let ctx=Ctx::new(m,ed.es.clone()); let mut h=std::collections::BTreeMap::new(); for &e in &ed.es { *h.entry(e.count_ones()).or_insert(0)+=1; }
            println!("m={} distinct masks {} minimal edges {} sizes {:?} Y-independent {} time {:.1}s rss {:.2}GB",m,ed.distinct,ed.es.len(),h,ctx.y_independent(),t.elapsed().as_secs_f64(),rss()); }
        "check"=>{ let m:u32=a[2].parse().unwrap(); let ed=enumerate(m,8); let parts=read_parts(&a[3]);
            match check::check_emit(&ed,&parts,&a[4]){ Ok(s)=>println!("{}",s), Err(e)=>{println!("CHECK FAILED: {}",e); std::process::exit(1);} } }
        "run"=>run(&a),
        _=>eprintln!("unknown")
    }
}
fn run(a:&[String]){
    let m:u32=a[2].parse().unwrap(); let seed:u64=a[3].parse().unwrap(); let smax:u32=a[4].parse().unwrap();
    let total:f64=a[5].parse().unwrap(); let mip_s:f64=a[6].parse().unwrap(); let attempts:usize=a[7].parse().unwrap();
    let cap:f64=a.get(8).map(|s|s.parse().unwrap()).unwrap_or(6.0); watchdog(cap);
    let t0=Instant::now(); let n=2*m as usize;
    let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone());
    println!("m={} edges {} (distinct masks {}) enum {:.1}s rss {:.2}GB seed {} smax {} total {}s",m,ed.es.len(),ed.distinct,t0.elapsed().as_secs_f64(),rss(),seed,smax,total);
    if !ctx.y_independent(){ println!("Y NOT INDEPENDENT: method invalid for this m"); std::process::exit(2); }
    let colf=format!("{}/logs/cg/cols_m{}.bin",DIR,m); let outf=format!("{}/logs/cg/lp_m{}.out",DIR,m); let mipf=format!("{}/logs/cg/mip_m{}.out",DIR,m);
    let mut pool=read_cols(&colf); let mut seen:HashSet<u128>=pool.iter().cloned().collect();
    println!("resumed {} columns",pool.len());
    let nth=6usize;
    let mut w=vec![1.0f64;n]; let mut u=vec![0.8f64;n]; let mut have_dual=false; let mut unc:Vec<u32>=vec![];
    let mut last_mip_pool=0usize; let mut round=0u64; let mut lpobj=f64::NAN;
    let mut rng=Rng(seed.wrapping_mul(0x9E3779B97F4A7C15)|1);
    loop {
        round+=1; let el=t0.elapsed().as_secs_f64(); if el>total { println!("TIME LIMIT {}s reached: UNDECIDED (pool {}, last LP obj {})",total,pool.len(),lpobj); std::process::exit(4); }
        // scores
        let sigma= if round<=2 {0.0} else {0.15+0.1*((round%5) as f64)};
        let mut score=vec![0.0f64;n]; let mut startw=vec![0.0f64;(m+1) as usize];
        for x in 0..n { if x<=m as usize { score[x]=(w[x]+0.05)*(1.0+sigma*(rng.f()*2.0-1.0)); } else { score[x]=-(u[x].max(0.05))*(1.0+sigma*(rng.f()*2.0-1.0)); } }
        for l in 0..=m as usize { startw[l]=w[l]+0.05; if unc.contains(&(l as u32+1)) { startw[l]*=6.0; } }
        // generate
        let seeds:Vec<u64>=(0..nth).map(|_|rng.next()|1).collect();
        let per=attempts/nth; let mut news:Vec<u128>=vec![];
        std::thread::scope(|sc|{ let hs:Vec<_>=seeds.iter().map(|&sd|{ let (ctx,score,startw)=(&ctx,&score,&startw);
            sc.spawn(move||{ let mut r=Rng(sd); let mut buf=vec![]; let mut out=vec![]; for _ in 0..per { gen_block(ctx,score,smax,&mut r,&mut buf,&mut out,startw); } out }) }).collect();
            for h in hs { news.extend(h.join().unwrap()); } });
        let mut added=0usize; let mut improving=0usize;
        for c in news { if c==0 {continue;} if seen.insert(c) { if pool.len()<400000 { pool.push(c); added+=1; if have_dual { let g:f64=(0..n).map(|x| if c>>x&1==1 { if x<=m as usize {w[x]} else {-u[x]} } else {0.0}).sum(); if g>1e-9 {improving+=1;} } } } }
        write_cols(&colf,&pool);
        // LP
        let ok=pyrun(&["lp".into(),m.to_string(),colf.clone(),outf.clone(),"0".into(),"4".into()]);
        if !ok { println!("lp.py failed"); std::process::exit(5); }
        let o=parse_out(&outf); lpobj=o["obj"].trim().parse().unwrap();
        let d:Vec<f64>=o["dual"].split_whitespace().map(|x|x.parse().unwrap()).collect();
        for x in 0..n { if x<=m as usize { w[x]=d[x].max(0.0); } else { u[x]=(-d[x]).max(0.0); } } have_dual=true;
        let nlow_pos=w.iter().take(m as usize+1).filter(|&&x|x>1e-9).count();
        println!("round {} t={:.0}s pool {} (+{}) improving {} LP {:.6} (duals>0 on {} lows) rss {:.2}GB",round,t0.elapsed().as_secs_f64(),pool.len(),added,improving,lpobj,nlow_pos,rss());
        if lpobj<1e-7 && (pool.len() as f64>=last_mip_pool as f64*1.25+1.0) {
            last_mip_pool=pool.len();
            let ok=pyrun(&["mip".into(),m.to_string(),colf.clone(),mipf.clone(),format!("{}",mip_s),"4".into()]);
            if !ok { println!("mip failed"); std::process::exit(5); }
            let o=parse_out(&mipf); let st=o.get("status").cloned().unwrap_or_default();
            println!("  MIP status {} obj {} bound {} (pool {})",st,o.get("obj").cloned().unwrap_or_default().trim(),o.get("bound").cloned().unwrap_or_default().trim(),pool.len());
            if let Some(sel)=o.get("sel") {
                let uncs:Vec<u32>=o.get("unc").map(|s|s.split_whitespace().map(|x|x.parse().unwrap()).collect()).unwrap_or_default();
                unc=uncs.clone();
                if uncs.is_empty() {
                    // assemble certificate
                    let idx:Vec<usize>=sel.split_whitespace().map(|x|x.parse().unwrap()).collect();
                    let mut parts:Vec<(u128,u32)>=vec![]; let mut usedy=0u128; let mut ok=true;
                    for &i in &idx { let c=pool[i]; if c&usedy&ctx.high!=0 {ok=false;} usedy|=c&ctx.high; parts.push((c,(c&ctx.high).count_ones())); }
                    if !ok { println!("  selected blocks overlap in Y: bug"); std::process::exit(6); }
                    let mut left:Vec<u32>=(0..n as u32).filter(|&x| ctx.high>>x&1==1 && usedy>>x&1==0).collect();
                    while !left.is_empty() { let k=left.len().min(8); let mut c=0u128; for _ in 0..k { c|=1u128<<left.pop().unwrap(); } parts.push((c,c.count_ones())); }
                    let solf=format!("{}/certs/m{}.sol",DIR,m); let leanf=format!("{}/certs/m{}.lean",DIR,m);
                    let mut s=String::new(); for &(c,k) in &parts { s.push_str(&format!("{} {}\n",c,k)); } std::fs::write(&solf,s).unwrap();
                    match check::check_emit(&ed,&parts,&leanf){
                        Ok(msg)=>{ println!("CERTIFICATE m={} time {:.0}s peak RSS {:.2}GB rounds {} pool {} {}",m,t0.elapsed().as_secs_f64(),rss(),round,pool.len(),msg); std::io::stdout().flush().unwrap(); std::process::exit(0); }
                        Err(e)=>{ println!("CHECK FAILED {}",e); std::process::exit(7); } }
                }
                println!("  incumbent leaves {} lows uncovered: {:?}",uncs.len(),uncs);
            }
        }
    }
}
