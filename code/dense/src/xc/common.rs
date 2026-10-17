// shared helpers for xc: watchdog, atomic IO
#[repr(C)] struct RU { ut:[i64;2], st:[i64;2], maxrss:i64, rest:[i64;13] }
extern "C" { fn getrusage(who:i32,u:*mut RU)->i32; }
pub fn rss()->f64{ let mut u=RU{ut:[0;2],st:[0;2],maxrss:0,rest:[0;13]}; unsafe{getrusage(0,&mut u);} u.maxrss as f64/1e9 }
pub fn watchdog(cap:f64){ std::thread::spawn(move||loop{ std::thread::sleep(std::time::Duration::from_secs(2));
    let r=rss(); if r>cap { eprintln!("WATCHDOG: peak RSS {:.2} GB > cap {:.2} GB, exiting",r,cap); std::process::exit(3);} }); }
pub fn atomic_write(path:&str,b:&[u8]){ let tmp=format!("{}.tmp",path); std::fs::write(&tmp,b).unwrap(); std::fs::rename(&tmp,path).unwrap(); }
pub const DIR:&str=".";
pub fn bits(s:u128)->Vec<u32>{ let mut v=vec![]; let mut r=s; while r!=0 { v.push(r.trailing_zeros()); r&=r-1; } v }
