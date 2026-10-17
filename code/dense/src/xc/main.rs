// xc: exact-cover search for cover-capacity certificates (queue item C). See XC_REPORT.md.
//  xc blocks m tmax [threads]             enumerate Pareto block family (checkpointed)
//  xc stats m tmax                        family histogram + profile of certs/m<m>.sol
//  xc dom m tmax                          every cert block dominated by a family block?
//  xc search m tmax mode maxpart seconds [seed] [maxsol] [cap_gb]   mode = complete | rand
//  xc check m parts.txt out.lean          independent brute-force check (same as cg check)
#[path="../cg/edges.rs"] mod edges; #[path="../cg/valid.rs"] mod valid; #[path="../cg/check.rs"] mod check;
mod common; mod blocks; mod search;
use common::*; use edges::*; use valid::*; use search::*; use std::time::Instant; use std::collections::BTreeMap;
fn read_parts(path:&str)->Vec<(u128,u32)>{ std::fs::read_to_string(path).unwrap().lines().filter(|l|!l.trim().is_empty()).map(|l|{let mut s=l.split_whitespace(); (s.next().unwrap().parse().unwrap(), s.next().unwrap().parse().unwrap())}).collect() }
fn factor(mut n:u64)->String{ let mut v=vec![]; let mut p=2; while p*p<=n { let mut e=0; while n%p==0 {n/=p;e+=1;} if e>0 { v.push(if e>1 {format!("{}^{}",p,e)} else {p.to_string()}); } p+=1; } if n>1 {v.push(n.to_string());} v.join("*") }
fn main(){
    let a:Vec<String>=std::env::args().collect(); let m:u32=a[2].parse().unwrap();
    match a[1].as_str(){
        "check"=>{ let ed=enumerate(m,8); let parts=read_parts(&a[3]);
            match check::check_emit(&ed,&parts,&a[4]){ Ok(s)=>println!("{}",s), Err(e)=>{println!("CHECK FAILED: {}",e); std::process::exit(1);} } }
        "blocks"=>{ watchdog(8.0); let tmax:u32=a[3].parse().unwrap(); let nth:usize=a.get(4).map(|s|s.parse().unwrap()).unwrap_or(6);
            let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); assert!(ctx.y_independent());
            let t0=Instant::now(); let persist=std::env::var("XC_PERSIST").is_ok(); let mut b=blocks::enumerate_blocks(&ctx,tmax,nth,persist); b.dedup();
            let mut bytes=vec![]; for &(t,l) in &b { bytes.extend_from_slice(&t.to_le_bytes()); bytes.extend_from_slice(&l.to_le_bytes()); }
            if persist { atomic_write(&blocks::blkfile(m,tmax),&bytes); }
            println!("BLOCKS m={} 2m+1={}={} tmax={} edges {} family {} time {:.0}s rss {:.2}GB",m,2*m+1,factor(2*m as u64+1),tmax,ed.es.len(),b.len(),t0.elapsed().as_secs_f64(),rss()); }
        "stats"|"dom"=>{ let tmax:u32=a[3].parse().unwrap(); let ed0=enumerate(m,8); let ctx0=Ctx::new(m,ed0.es.clone()); let b=blocks::get_blocks(&ctx0,tmax);
            let mut h:BTreeMap<(u32,u32),u64>=BTreeMap::new(); for &(t,l) in &b { *h.entry((l.count_ones(),t.count_ones())).or_insert(0)+=1; }
            if a[1]=="stats" { println!("m={} family {} by (|L|,|T|): {:?}",m,b.len(),h); }
            let low=(1u128<<(m+1))-1-(1|(1u128<<m)); let sol=format!("{}/certs/m{}.sol",DIR,m);
            if let Ok(_)=std::fs::read_to_string(&sol){ let parts=read_parts(&sol); let mut nb=0; let mut bad=0; let mut prof=vec![];
                for &(u,_) in &parts { if u&low==0 {continue;} nb+=1; let (t,l)=((u>>(m+1))<<(m+1),u&low); prof.push((l.count_ones(),t.count_ones()));
                    let dom=b.iter().any(|&(t2,l2)| t2&!t==0 && l&!l2==0);
                    if !dom { bad+=1; println!("  cert block NOT dominated: |T|={} |L|={}",t.count_ones(),l.count_ones()); } }
                prof.sort(); prof.reverse(); println!("m={} cert blocks {} undominated {} profile(|L|,|T|) {:?}",m,nb,bad,prof); } }
        "lp"=>{ // xc lp m tmax maxpart out.lp : CPLEX-LP of the master LP (for glpsol duals)
            let tmax:u32=a[3].parse().unwrap(); let maxpart:u32=a[4].parse().unwrap();
            let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let pr=blocks::build_priv(&ctx); let low=ctx.low&!pr.free_lows;
            let raw=blocks::get_blocks(&ctx,tmax); let fam=make_fam(&raw,low,maxpart,0); let nb=fam.t.len();
            use std::io::Write; let mut w=std::io::BufWriter::new(std::fs::File::create(&a[5]).unwrap());
            let lows=bits(low); let ys=bits(ctx.high);
            write!(w,"Minimize\n obj:").unwrap(); for &l in &lows { write!(w," + s{}",l+1).unwrap(); } writeln!(w,"\nSubject To").unwrap();
            let mut ylist:Vec<Vec<usize>>=vec![vec![];ctx.n as usize]; let mut llist:Vec<Vec<usize>>=vec![vec![];ctx.n as usize];
            for b in 0..nb { for y in bits(fam.t[b]) { ylist[y as usize].push(b); } for l in bits(fam.l[b]) { llist[l as usize].push(b); } }
            for &l in &lows { write!(w," L{}:",l+1).unwrap(); for &b in &llist[l as usize] { write!(w," + x{}",b).unwrap(); } writeln!(w," + s{} >= 1",l+1).unwrap(); }
            for &y in &ys { write!(w," Y{}:",y+1).unwrap(); let v=&ylist[y as usize]; if v.is_empty() { writeln!(w," 0 x0 <= 1").unwrap(); continue; } for &b in v { write!(w," + x{}",b).unwrap(); } writeln!(w," <= 1").unwrap(); }
            writeln!(w,"Bounds").unwrap(); for &l in &lows { writeln!(w," 0 <= s{} <= 1",l+1).unwrap(); } if std::env::var("XC_BIN").is_ok() { writeln!(w,"Binary").unwrap(); for b in 0..nb { writeln!(w," x{}",b).unwrap(); } } writeln!(w,"End").unwrap(); println!("LP written: {} cols",nb); }
        "fromglp"=>{ // xc fromglp m tmax maxpart glpsol.sol
            let tmax:u32=a[3].parse().unwrap(); let maxpart:u32=a[4].parse().unwrap();
            let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let pr=blocks::build_priv(&ctx); let free=pr.free_lows; let low=ctx.low&!free;
            let raw=blocks::get_blocks(&ctx,tmax); let fam=make_fam(&raw,low,maxpart,0);
            let txt=std::fs::read_to_string(&a[5]).unwrap(); let mut chosen:Vec<usize>=vec![]; let mut incol=false;
            for l in txt.lines(){ if l.contains("Column name") {incol=true;continue;} if !incol {continue;} let t:Vec<&str>=l.split_whitespace().collect();
                if t.len()>=3 && t[1].starts_with('x') { let off= if t[2]=="*" {3} else {2}; if let Some(v)=t.get(off){ if v.parse::<f64>().map(|x|x>0.5).unwrap_or(false) { chosen.push(t[1][1..].parse().unwrap()); } } } }
            let mut parts:Vec<(u128,u32)>=vec![]; let mut usedy=0u128; let mut cov=0u128;
            for &b in &chosen { if usedy&fam.t[b]!=0 { println!("overlap: bug"); std::process::exit(6);} usedy|=fam.t[b]; cov|=fam.l[b]; parts.push((fam.t[b]|fam.l[b],fam.t[b].count_ones())); }
            if cov&low!=low { println!("solution does not cover Low (not an optimal-0 solution)"); std::process::exit(6); }
            if free!=0 { parts.push((free,0)); }
            let mut left:Vec<u32>=(0..ctx.n).filter(|&x| ctx.high>>x&1==1 && usedy>>x&1==0).collect();
            while !left.is_empty() { let k=left.len().min(8); let mut c=0u128; for _ in 0..k { c|=1u128<<left.pop().unwrap(); } parts.push((c,c.count_ones())); }
            let out=format!("{}/logs/xc/m{}.sol",DIR,m); let mut s=String::new(); for &(c,k) in &parts { s.push_str(&format!("{} {}\n",c,k)); } std::fs::write(&out,s).unwrap();
            match check::check_emit(&ed,&parts,&format!("{}/logs/xc/m{}.lean",DIR,m)){ Ok(msg)=>println!("CERT {} {}",out,msg), Err(e)=>{println!("CHECK FAILED {}",e); std::process::exit(7);} } }
        "gstar"=>{ // xc gstar m tmax : exact max total profit of pairwise Y-disjoint positive-profit blocks (per distinct T), node-capped
            let tmax:u32=a[3].parse().unwrap(); let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let pr=blocks::build_priv(&ctx); let low=ctx.low&!pr.free_lows;
            let raw=blocks::get_blocks(&ctx,tmax); let mut best:std::collections::BTreeMap<u128,i32>=Default::default();
            for &(t,l) in &raw { let l=l&low; if l.count_ones()>t.count_ones() && t!=0 { let p=l.count_ones() as i32-t.count_ones() as i32; let e=best.entry(t).or_insert(0); if p>*e {*e=p;} } }
            let mut av:Vec<(u128,i32)>=best.into_iter().collect(); let np=av.len(); av.sort_by_key(|&(t,p)|(std::cmp::Reverse(p as i64*100/(t.count_ones() as i64)),t));
            // y-count of distinct y covered
            let yp=av.iter().fold(0u128,|x,&(t,_)|x|t);
            let mut rest=vec![0i32;av.len()+1]; for i in (0..av.len()).rev(){ rest[i]=rest[i+1]+av[i].1; }
            // bound: sum of profit over disjoint <= floor(|Y covered| * maxratio)
            let mx=av.iter().map(|&(t,p)|(p as f64)/(t.count_ones() as f64)).fold(0.0,f64::max);
            let crude=(yp.count_ones() as f64*mx).floor() as i32;
            let mut nodes=0u64; let cap=200_000_000u64; let mut bestv=0i32; let mut capped=false;
            fn dfs(av:&[(u128,i32)],i:usize,used:u128,acc:i32,best:&mut i32,nodes:&mut u64,cap:u64,capped:&mut bool,ub:i32){ *nodes+=1; if *nodes>cap {*capped=true;return;} if acc>*best {*best=acc;} if *best>=ub {return;}
                let mut j=i; while j<av.len() && av[j].0&used!=0 { j+=1; } if j>=av.len() {return;}
                // remaining bound: free y count * ratio
                dfs(av,j+1,used|av[j].0,acc+av[j].1,best,nodes,cap,capped,ub); if *capped {return;} dfs(av,j+1,used,acc,best,nodes,cap,capped,ub); }
            dfs(&av,0,0,0,&mut bestv,&mut nodes,cap,&mut capped,crude);
            println!("GSTAR m={} tmax={} distinct positive T {} Y covered by them {} crude_ub {} G*={} {} nodes {}",m,tmax,np,yp.count_ones(),crude,bestv,if capped {"(LOWER bound only, node cap)"} else {"(exact)"},nodes); }
        "reduce"=>{ let tmax:u32=a[3].parse().unwrap(); let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let raw=blocks::get_blocks(&ctx,tmax); let t0=Instant::now();
            let red=blocks::reduce(&ctx,&raw,6);
            let mut h:BTreeMap<(u32,u32),(u64,u64)>=BTreeMap::new(); for &(t,l) in &raw { h.entry((l.count_ones(),t.count_ones())).or_default().0+=1; } for &(t,l) in &red { h.entry((l.count_ones(),t.count_ones())).or_default().1+=1; }
            println!("REDUCE m={} tmax={} full {} irreducible {} time {:.0}s by (|L|,|T|):(full,irred) {:?}",m,tmax,raw.len(),red.len(),t0.elapsed().as_secs_f64(),h);
            let mut bytes=vec![]; for &(t,l) in &red { bytes.extend_from_slice(&t.to_le_bytes()); bytes.extend_from_slice(&l.to_le_bytes()); }
            atomic_write(&format!("{}/logs/xc/irred_m{}_t{}.bin",DIR,m,tmax),&bytes); }
        "matchdef"=>{ // xc matchdef m : max matching of the (1,1)-block graph (2-edges {l,y}, l in Low', y in Y); deficiency; nonunit counts
            let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let pr=blocks::build_priv(&ctx); let low=ctx.low&!pr.free_lows;
            let lows=bits(low); let mut adj:Vec<Vec<u32>>=vec![vec![];ctx.n as usize];
            for &e in &ed.es { if e.count_ones()==2 && (e&ctx.high).count_ones()==1 && (e&low).count_ones()==1 { adj[(e&low).trailing_zeros() as usize].push((e&ctx.high).trailing_zeros()); } }
            let mut mate=vec![u32::MAX;ctx.n as usize]; let mut size=0;
            fn aug(l:usize,adj:&Vec<Vec<u32>>,seen:&mut Vec<bool>,mate:&mut Vec<u32>)->bool{ for &y in &adj[l] { let y=y as usize; if seen[y] {continue;} seen[y]=true; if mate[y]==u32::MAX || aug(mate[y] as usize,adj,seen,mate) { mate[y]=l as u32; return true; } } false }
            for &l in &lows { let mut seen=vec![false;ctx.n as usize]; if aug(l as usize,&adj,&mut seen,&mut mate) {size+=1;} }
            let q=2*m as u64+1; let nonunit_low=lows.iter().filter(|&&l|gcd(l as u64+1,q)>1).count(); let deg0=lows.iter().filter(|&&l|adj[l as usize].is_empty()).count();
            println!("MATCHDEF m={} q={}={} lows {} twoedge-matching {} deficiency {} lows_without_2edge {} nonunit_lows {} m%2={} m%3={} m%5={} m%7={}",m,q,factor(q),lows.len(),size,lows.len()-size,deg0,nonunit_low,m%2,m%3,m%5,m%7); }
        "selftest"=>{ // xc selftest m tmax : brute force over ALL (T,L), |T|<=tmax, L subset Low' : every valid block must be dominated by a family block
            let tmax:u32=a[3].parse().unwrap(); let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); let pr=blocks::build_priv(&ctx); let low=ctx.low&!pr.free_lows;
            let fam=blocks::get_blocks(&ctx,tmax); let lb=bits(low); let hy=bits(ctx.high); let nl=lb.len();
            let mut by_t:std::collections::HashMap<u128,Vec<u128>>=Default::default(); for &(t,l) in &fam { by_t.entry(t).or_default().push(l); }
            let famset:Vec<(u128,u128)>=fam.clone();
            let mut checked=0u64; let mut valid_n=0u64; let mut bad=0u64; let mut buf=vec![];
            // enumerate T by size
            let mut ts:Vec<u128>=vec![0]; let mut frontier:Vec<(u128,usize)>=vec![(0,0)];
            for _ in 0..tmax { let mut nf=vec![]; for &(t,i) in &frontier { for j in i..hy.len() { let t2=t|1u128<<hy[j]; ts.push(t2); nf.push((t2,j+1)); } } frontier=nf; }
            for &t in &ts { if t==0 {continue;}
                for lm in 1u64..(1u64<<nl) { let mut l=0u128; for i in 0..nl { if lm>>i&1==1 { l|=1u128<<lb[i]; } }
                    checked+=1; if ctx.valid(t|l,&mut buf) { valid_n+=1; if !famset.iter().any(|&(t2,l2)| t2&!t==0 && l&!l2==0) { bad+=1; if bad<5 { println!("UNDOMINATED valid block T={:x} L={:x}",t,l); } } } } }
            println!("SELFTEST m={} tmax={} blocks (T,L) tested {} valid {} undominated {} (family size {})",m,tmax,checked,valid_n,bad,fam.len()); }
        "sat"=>{ // xc sat m tmax maxpart secs solver(kissat|cadical) seed
            let tmax:u32=a[3].parse().unwrap(); let maxpart:u32=a[4].parse().unwrap(); let secs:u64=a[5].parse().unwrap();
            let solver=a.get(6).cloned().unwrap_or("kissat".into()); let seed:u64=a.get(7).map(|s|s.parse().unwrap()).unwrap_or(1); watchdog(8.0);
            let t0=Instant::now(); let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); assert!(ctx.y_independent());
            let pr=blocks::build_priv(&ctx); let free=pr.free_lows; let low=ctx.low&!free;
            let raw=blocks::get_blocks(&ctx,tmax); assert!(!raw.is_empty());
            let fam=make_fam(&raw,low,maxpart,0); let nb=fam.t.len();
            // counts
            let ys:Vec<u32>=bits(ctx.high); let mut nclauses=0u64; let mut nvars=nb as u64;
            let mut ylist:Vec<Vec<u32>>=vec![vec![];ctx.n as usize]; for b in 0..nb { for y in bits(fam.t[b]) { ylist[y as usize].push(b as u32); } }
            for &y in &ys { let k=ylist[y as usize].len() as u64; if k>=2 { nvars+=k-1; nclauses+=3*k-4; } }
            let lows:Vec<u32>=bits(low); nclauses+=lows.len() as u64;
            println!("m={} 2m+1={} family {} (maxpart<={}) CNF vars {} clauses {} solver {} limit {}s",m,factor(2*m as u64+1),nb,maxpart,nvars,nclauses,solver,secs);
            let mut cmd=std::process::Command::new(format!("/opt/homebrew/bin/{}",solver));
            if solver=="kissat" { cmd.arg("-q").arg(format!("--time={}",secs)).arg(format!("--seed={}",seed)); } else { cmd.arg("-q").arg("-t").arg(secs.to_string()); }
            let mut ch=cmd.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
            let pid=ch.id(); let stdin=ch.stdin.take().unwrap(); let mut out=ch.stdout.take().unwrap();
            let rd=std::thread::spawn(move||{ use std::io::Read; let mut s=String::new(); out.read_to_string(&mut s).unwrap(); s });
            std::thread::spawn(move||loop{ std::thread::sleep(std::time::Duration::from_secs(5));
                if let Ok(o)=std::process::Command::new("ps").args(["-o","rss=","-p",&pid.to_string()]).output(){ if let Ok(k)=String::from_utf8_lossy(&o.stdout).trim().parse::<f64>(){ if k/1e6>8.0 { eprintln!("WATCHDOG: solver RSS {:.1} GB, killing",k/1e6); let _=std::process::Command::new("kill").arg("-9").arg(pid.to_string()).status(); std::process::exit(3);} } } });
            { use std::io::Write; let mut w=std::io::BufWriter::with_capacity(1<<20,stdin);
              writeln!(w,"p cnf {} {}",nvars,nclauses).unwrap();
              for &l in &lows { for b in 0..nb { if fam.l[b]>>l&1==1 { write!(w,"{} ",b+1).unwrap(); } } writeln!(w,"0").unwrap(); }
              let mut nv=nb as i64;
              for &y in &ys { let v=&ylist[y as usize]; let k=v.len(); if k<2 {continue;} let s0=nv; nv+=(k as i64)-1;
                  writeln!(w,"-{} {} 0",v[0]+1,s0+1).unwrap();
                  for i in 1..k-1 { let si=s0+1+i as i64; let sp=s0+i as i64; writeln!(w,"-{} {} 0\n-{} {} 0\n-{} -{} 0",v[i]+1,si,sp,si,v[i]+1,sp).unwrap(); }
                  writeln!(w,"-{} -{} 0",v[k-1]+1,s0+(k as i64)-1).unwrap(); }
              w.flush().unwrap(); }
            let res=rd.join().unwrap(); let _=ch.wait();
            let st= if res.contains("s SATISFIABLE") {"SAT"} else if res.contains("s UNSATISFIABLE") {"UNSAT"} else {"UNKNOWN"};
            println!("SATRESULT m={} tmax={} maxpart={} family={} solver={} seed={} time={:.1}s => {}",m,tmax,maxpart,nb,solver,seed,t0.elapsed().as_secs_f64(),st);
            if st=="SAT" { let mut chosen:Vec<usize>=vec![]; for l in res.lines() { if l.starts_with("v ") { for t in l[2..].split_whitespace() { let x:i64=t.parse().unwrap(); if x>0 && (x as usize)<=nb { chosen.push(x as usize-1); } } } }
                let mut parts:Vec<(u128,u32)>=vec![]; let mut usedy=0u128; for &b in &chosen { usedy|=fam.t[b]; parts.push((fam.t[b]|fam.l[b],fam.t[b].count_ones())); }
                let (mut cov,mut ok)=(0u128,true); for &b in &chosen { if fam.t[b]&(usedy&!fam.t[b])!=0 {ok=false;} cov|=fam.l[b]; } let _=ok;
                if cov&low!=low { println!("MODEL does not cover Low: bug"); std::process::exit(6); }
                if free!=0 { parts.push((free,0)); }
                let mut left:Vec<u32>=(0..ctx.n).filter(|&x| ctx.high>>x&1==1 && usedy>>x&1==0).collect();
                while !left.is_empty() { let k=left.len().min(8); let mut c=0u128; for _ in 0..k { c|=1u128<<left.pop().unwrap(); } parts.push((c,c.count_ones())); }
                let out=format!("{}/logs/xc/m{}.sol",DIR,m); let mut s=String::new(); for &(c,k) in &parts { s.push_str(&format!("{} {}\n",c,k)); } std::fs::write(&out,s).unwrap();
                match check::check_emit(&ed,&parts,&format!("{}/logs/xc/m{}.lean",DIR,m)){ Ok(msg)=>println!("CERT {} {}",out,msg), Err(e)=>println!("CHECK FAILED {}",e) } }
        }
        "search"=>{ let tmax:u32=a[3].parse().unwrap(); let mode=a[4].as_str(); let maxpart:u32=a[5].parse().unwrap(); let secs:f64=a[6].parse().unwrap();
            let seed:u64=a.get(7).map(|s|s.parse().unwrap()).unwrap_or(0); let maxsol:u64=a.get(8).map(|s|s.parse().unwrap()).unwrap_or(1);
            let cap:f64=a.get(9).map(|s|s.parse().unwrap()).unwrap_or(8.0); watchdog(cap);
            let t0=Instant::now(); let ed=enumerate(m,8); let ctx=Ctx::new(m,ed.es.clone()); assert!(ctx.y_independent());
            let pr=blocks::build_priv(&ctx); let free=pr.free_lows; let low=ctx.low&!free; let nlow=low.count_ones() as usize;
            let raw=blocks::get_blocks(&ctx,tmax); assert!(!raw.is_empty());
            let fam=make_fam(&raw,low,maxpart,if mode=="rand"{seed.max(1)}else{0});
            println!("m={} 2m+1={} family {} (after maxpart<={}: {}) free lows {:#x} tmax {} mode {} seed {} deadline {}s",m,factor(2*m as u64+1),raw.len(),maxpart,fam.t.len(),free,tmax,mode,seed,secs);
            let ckp=format!("{}/logs/xc/ck_search_m{}_t{}_p{}.txt",DIR,m,tmax,maxpart);
            let (mut resume,mut nodes0,mut found0)=(vec![],0u64,0u64);
            if mode=="complete" { if let Ok(s)=std::fs::read_to_string(&ckp){ for l in s.lines(){ let mut it=l.splitn(2,' '); match it.next(){ Some("path")=>{ resume=it.next().unwrap_or("").split_whitespace().map(|x|x.parse().unwrap()).collect(); } Some("nodes")=>{nodes0=it.next().unwrap().parse().unwrap();} Some("found")=>{found0=it.next().unwrap().parse().unwrap();} _=>{} } }
                println!("RESUME from checkpoint: path depth {} nodes {} found {}",resume.len(),nodes0,found0); } }
            let nb=fam.t.len();
            if mode=="cpar" {
                use std::sync::atomic::{AtomicBool,AtomicU64,AtomicUsize,Ordering}; use std::sync::Mutex;
                let nth:usize=std::env::var("XC_THREADS").ok().and_then(|x|x.parse().ok()).unwrap_or(6);
                let (pos0,ypos0)=make_pos(&fam);
                let mkp=|only:Option<usize>,dl:f64,st:Option<&'static AtomicBool>,gn:Option<&'static AtomicU64>|->Srch{ Srch{f:&fam,low,highcnt:ctx.high.count_ones(),excl:vec![false;nb],used:0,cov:0,chosen:vec![],nodes:0,nodecap:u64::MAX,found:0,maxsol,sols:vec![],
                    replay:false,resume:vec![],cur:vec![],t0:Instant::now(),last_rep:Instant::now(),last_ck:Instant::now(),ckpath:String::new(),capped:false,deadline:dl,frac0:0.0,start_el:0.0,m,rnd:Some(Rn(0)),bound_on:true,prunes:[0;3],pos:pos0.clone(),gcache:Default::default(),ypos:ypos0,use_rho:true,high:ctx.high,order:0,only_top:only,top_n:0,stop:st,gnodes:gn} };
                // rnd=Some(Rn(0)) would shuffle: cpar must be deterministic -> disable by using None
                let mut probe=mkp(Some(usize::MAX),1e9,None,None); probe.rnd=None; probe.rec(0); let ntop=probe.top_n;
                let tag=std::env::var("XC_TAG").unwrap_or_default();
                let ckf=format!("{}/logs/xc/ckpar_m{}_t{}_p{}{}.txt",DIR,m,tmax,maxpart,tag);
                let mut done:std::collections::BTreeSet<usize>=Default::default();
                if let Ok(s)=std::fs::read_to_string(&ckf){ let mut it=s.lines(); let hdr=it.next().unwrap_or(""); if hdr==format!("fam {} top {}",nb,ntop) { for l in it { if let Ok(x)=l.trim().parse(){ done.insert(x);} } println!("RESUME: {} of {} top branches already done",done.len(),ntop); } else { println!("checkpoint header mismatch ({}), ignoring",hdr); } }
                let st:&'static AtomicBool=Box::leak(Box::new(AtomicBool::new(false))); let gn:&'static AtomicU64=Box::leak(Box::new(AtomicU64::new(0))); let next=AtomicUsize::new(0); let nfound=AtomicUsize::new(0);
                let state=Mutex::new((done.clone(),vec![] as Vec<Vec<u32>>,[0u64;3],0u64)); let todo:Vec<usize>=(0..ntop).filter(|i|!done.contains(i)).collect(); let d0=done.len();
                println!("CPAR top branches {} (todo {}) threads {} family {}",ntop,todo.len(),nth,nb);
                let tstart=Instant::now();
                std::thread::scope(|sc|{
                    for _ in 0..nth { sc.spawn(||loop{ if st.load(Ordering::Relaxed) {break;} let k=next.fetch_add(1,Ordering::SeqCst); if k>=todo.len() {break;} let i=todo[k];
                        let mut s=mkp(Some(i),secs-t0.elapsed().as_secs_f64(),Some(st),Some(gn)); s.rnd=None; s.rec(0);
                        gn.fetch_add(s.nodes&0x3FFF,Ordering::Relaxed);
                        let mut g=state.lock().unwrap(); for q in 0..3 { g.2[q]+=s.prunes[q]; } g.3+=s.nodes;
                        if s.found>0 { g.1.extend(s.sols.clone()); nfound.fetch_add(s.found as usize,Ordering::SeqCst); st.store(true,Ordering::SeqCst); }
                        if !s.capped { g.0.insert(i); let mut txt=format!("fam {} top {}\n",nb,ntop); for x in g.0.iter(){ txt.push_str(&format!("{}\n",x)); } atomic_write(&ckf,txt.as_bytes()); } }); }
                    sc.spawn(||{ loop { for _ in 0..30 { std::thread::sleep(std::time::Duration::from_secs(1)); if st.load(Ordering::Relaxed) {break;} } if st.load(Ordering::Relaxed) {break;}
                        let g=state.lock().unwrap(); let d=g.0.len()-d0; let el=tstart.elapsed().as_secs_f64(); let tot=todo.len();
                        if d>=tot {break;} if g.0.len()>=ntop {break;} if t0.elapsed().as_secs_f64()>secs {break;}
                        let eta= if d>0 { el*(tot-d) as f64/d as f64 } else { f64::NAN };
                        println!("m={} top branches done {}/{} (this run {}), nodes {:.1}M, found {}, elapsed {:.0}s, ETA(by branch count, crude) {:.0}s, rss {:.2}GB",m,g.0.len(),ntop,d,gn.load(Ordering::Relaxed) as f64/1e6,nfound.load(Ordering::Relaxed),el,eta,rss()); } });
                });
                let g=state.lock().unwrap(); let complete=g.0.len()==ntop; let nf=nfound.load(Ordering::Relaxed);
                let status= if nf>0 {"COVER FOUND"} else if complete {"PROVED NONE (for this family)"} else {"UNDECIDED"};
                println!("RESULT m={} mode=cpar tmax={} maxpart={} family={} top_done={}/{} nodes~{} solutions_found={} prunes(nolow,share,rho)={:?} time={:.1}s rss={:.2}GB => {}",m,tmax,maxpart,nb,g.0.len(),ntop,g.3,nf,&g.2,t0.elapsed().as_secs_f64(),rss(),status);
                if nf>0 { let sol=&g.1[0]; let mut parts:Vec<(u128,u32)>=vec![]; let mut usedy=0u128;
                    for &bi in sol { let (t,l)=(fam.t[bi as usize],fam.l[bi as usize]); usedy|=t; parts.push((t|l,t.count_ones())); }
                    if free!=0 { parts.push((free,0)); }
                    let mut left:Vec<u32>=(0..ctx.n).filter(|&x| ctx.high>>x&1==1 && usedy>>x&1==0).collect();
                    while !left.is_empty() { let k=left.len().min(8); let mut c=0u128; for _ in 0..k { c|=1u128<<left.pop().unwrap(); } parts.push((c,c.count_ones())); }
                    let out=format!("{}/logs/xc/m{}.sol",DIR,m); let mut s=String::new(); for &(c,k) in &parts { s.push_str(&format!("{} {}\n",c,k)); } std::fs::write(&out,s).unwrap();
                    match check::check_emit(&ed,&parts,&format!("{}/logs/xc/m{}.lean",DIR,m)){ Ok(msg)=>println!("CERT {} {}",out,msg), Err(e)=>println!("CHECK FAILED {}",e) } }
                return;
            }
            let mut sols:Vec<Vec<u32>>=vec![]; let mut totnodes=nodes0; let mut capped=false; let mut found=found0; let mut prunes=[0u64;3];
            let mk=|rnd:Option<Rn>,deadline:f64,nodecap:u64,resume:Vec<usize>|->Srch{ Srch{f:&fam,low,highcnt:ctx.high.count_ones(),excl:vec![false;nb],used:0,cov:0,chosen:vec![],nodes:0,nodecap,found:0,maxsol,sols:vec![],
                replay:!resume.is_empty(),resume,cur:vec![],t0:Instant::now(),last_rep:Instant::now(),last_ck:Instant::now(),ckpath:ckp.clone(),capped:false,deadline,frac0:0.0,start_el:0.0,m,rnd,bound_on:true,prunes:[0;3],pos:make_pos(&fam).0,gcache:Default::default(),ypos:make_pos(&fam).1,use_rho:std::env::var("XC_NORHO").is_err(),high:ctx.high,order:std::env::var("XC_ORDER").ok().and_then(|x|x.parse().ok()).unwrap_or(0),only_top:None,top_n:0,stop:None,gnodes:None} };
            let _=nlow;
            if mode=="complete" {
                let mut s=mk(None,secs,u64::MAX,resume); s.rec(0); totnodes+=s.nodes; capped=s.capped; found+=s.found; sols=s.sols.clone(); prunes=s.prunes;
                if !capped { let _=std::fs::remove_file(&ckp); }
            } else {
                let mut r=Rn(seed.max(1)*0x9E3779B97F4A7C15|1); let mut restart=0u64;
                let (pos0,ypos0)=make_pos(&fam);
                while t0.elapsed().as_secs_f64()<secs { restart+=1;
                    let cap_nodes=5000u64*(1+(restart%16));
                    let mut s=Srch{f:&fam,low,highcnt:ctx.high.count_ones(),excl:vec![false;nb],used:0,cov:0,chosen:vec![],nodes:0,nodecap:cap_nodes,found:0,maxsol,sols:vec![],
                        replay:false,resume:vec![],cur:vec![],t0:Instant::now(),last_rep:Instant::now(),last_ck:Instant::now(),ckpath:ckp.clone(),capped:false,deadline:secs-t0.elapsed().as_secs_f64(),frac0:0.0,start_el:0.0,m,rnd:Some(Rn(r.next()|1)),bound_on:true,prunes:[0;3],pos:pos0.clone(),gcache:Default::default(),ypos:ypos0,use_rho:true,high:ctx.high,order:std::env::var("XC_ORDER").ok().and_then(|x|x.parse().ok()).unwrap_or(0),only_top:None,top_n:0,stop:None,gnodes:None};
                    s.rec(0); totnodes+=s.nodes; for i in 0..3 {prunes[i]+=s.prunes[i];}
                    if s.found>0 { found+=s.found; sols=s.sols.clone(); break; }
                    if restart%50==0 { println!("restart {} nodes {} t={:.0}s rss {:.2}GB",restart,totnodes,t0.elapsed().as_secs_f64(),rss()); } }
            }
            let status= if found>0 {"COVER FOUND"} else if capped||(mode=="rand") {"UNDECIDED"} else {"PROVED NONE (for this family)"};
            println!("RESULT m={} mode={} tmax={} maxpart={} family={} nodes={} solutions_found={} prunes(nolow,share,rho)={:?} time={:.1}s rss={:.2}GB => {}",m,mode,tmax,maxpart,nb,totnodes,found,&prunes[..3],t0.elapsed().as_secs_f64(),rss(),status);
            if found>0 && !sols.is_empty() {
                let sol=&sols[0]; let mut parts:Vec<(u128,u32)>=vec![]; let mut usedy=0u128;
                for &bi in sol { let (t,l)=(fam.t[bi as usize],fam.l[bi as usize]); usedy|=t; parts.push((t|l,t.count_ones())); }
                if free!=0 { parts.push((free,0)); }
                let mut left:Vec<u32>=(0..ctx.n).filter(|&x| ctx.high>>x&1==1 && usedy>>x&1==0).collect();
                while !left.is_empty() { let k=left.len().min(8); let mut c=0u128; for _ in 0..k { c|=1u128<<left.pop().unwrap(); } parts.push((c,c.count_ones())); }
                let out=format!("{}/logs/xc/m{}.sol",DIR,m); let mut s=String::new(); for &(c,k) in &parts { s.push_str(&format!("{} {}\n",c,k)); } std::fs::write(&out,s).unwrap();
                match check::check_emit(&ed,&parts,&format!("{}/logs/xc/m{}.lean",DIR,m)){ Ok(msg)=>println!("CERT {} {}",out,msg), Err(e)=>println!("CHECK FAILED {}",e) } }
        }
        _=>eprintln!("unknown")
    }
}
