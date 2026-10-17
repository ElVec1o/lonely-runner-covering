// fcuspec: exhaustive map of the Lonely Runner spectrum below 1/m for m speeds, heights <= H.
// Exact integer arithmetic throughout. ML attained at t = a/(v_i+v_j), i <= j (local maxima of
// min_i ||v_i t|| are crossings of an increasing and a decreasing tent, or tent peaks).
use rayon::prelude::*;
use std::io::Write;

fn gcd(a: i64, b: i64) -> i64 { if b == 0 { a.abs() } else { gcd(b, a % b) } }

// gap at a/q as (num, q): min_i min(r, q-r)
fn gapnum(v: &[i64], a: i64, q: i64) -> i64 {
    let mut g = i64::MAX;
    for &x in v { let r = (x * a).rem_euclid(q); let d = r.min(q - r); if d < g { g = d; if g == 0 { break; } } }
    g
}

// exact ML as reduced (p, q); also list of distinct maximiser denominators (reduced)
fn ml(v: &[i64]) -> (i64, i64, Vec<i64>) {
    let (mut bp, mut bq) = (0i64, 1i64);
    let mut dens: Vec<i64> = vec![];
    let m = v.len();
    for i in 0..m { for j in i..m {
        let q = v[i] + v[j];
        for a in 1..=q / 2 {
            let p = gapnum(v, a, q);
            // compare p/q vs bp/bq
            let lhs = p as i128 * bq as i128; let rhs = bp as i128 * q as i128;
            let g = gcd(a, q); let dq = q / g;
            if lhs > rhs { bp = p; bq = q; dens.clear(); dens.push(dq); }
            else if lhs == rhs && p > 0 { if !dens.contains(&dq) { dens.push(dq); } }
        }
    }}
    let g = gcd(bp, bq); dens.sort();
    (bp / g, bq / g, dens)
}

fn flags(v: &[i64]) -> (bool, bool, bool) {
    let m = v.len() as i64; let n = m + 1;
    let ndiv = v.iter().any(|&x| x % n == 0);
    let dc = (2..=n).all(|j| v.iter().any(|&x| x % j == 0));
    let l1o = (0..v.len()).all(|l| { let mut g = 0; for (i, &x) in v.iter().enumerate() { if i != l { g = gcd(g, x); } } g == 1 });
    (ndiv, dc, l1o)
}

fn rec(v: &mut Vec<i64>, m: usize, h: i64, times: &[(i64, i64)], out: &mut Vec<Vec<i64>>, cnt: &mut u64) {
    if v.len() == m {
        let mut g = 0; for &x in v.iter() { g = gcd(g, x); }
        if g != 1 { return; }
        *cnt += 1;
        let mm = m as i64;
        // survive iff every cached time has gap < 1/m, i.e. m * gapnum < q
        for &(a, q) in times { if mm * gapnum(v, a, q) >= q { return; } }
        out.push(v.clone());
        return;
    }
    let lo = v.last().map_or(1, |&x| x + 1);
    let rem = (m - v.len()) as i64;
    for x in lo..=(h - rem + 1) { v.push(x); rec(v, m, h, times, out, cnt); v.pop(); }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args[0].as_str() {
        "eval" => for s in &args[1..] {
            let v: Vec<i64> = s.split(',').map(|x| x.trim().parse().unwrap()).collect();
            let (p, q, d) = ml(&v); let (nd, dc, l1o) = flags(&v); let m = v.len() as i64;
            println!("{:?} m={} ML={}/{} (m+1)ML={}/{} maximiser dens={:?} n|speed={} DC={} L1O={}", v, m, p, q, (m + 1) * p, q, d, nd, dc, l1o);
        },
        "sweep" => {
            let m: usize = args[1].parse().unwrap(); let h: i64 = args[2].parse().unwrap();
            let q0: i64 = args.get(3).map_or(60, |x| x.parse().unwrap());
            let thr: usize = args.get(4).map_or(4, |x| x.parse().unwrap());
            rayon::ThreadPoolBuilder::new().num_threads(thr).build_global().unwrap();
            let mut times = vec![];
            for q in 2..=q0 { for a in 1..=q / 2 { if gcd(a, q) == 1 { times.push((a, q)); } } }
            // sort times by how often they are good is unknown; smaller q first
            let pairs: Vec<(i64, i64)> = (1..=h).flat_map(|a| ((a + 1)..=h).map(move |b| (a, b))).filter(|&(_, b)| b <= h - (m as i64 - 2)).collect();
            let t0 = std::time::Instant::now();
            let res: Vec<(Vec<Vec<i64>>, u64)> = pairs.par_iter().map(|&(a, b)| {
                let mut v = vec![a, b]; let mut out = vec![]; let mut cnt = 0u64;
                rec(&mut v, m, h, &times, &mut out, &mut cnt); (out, cnt)
            }).collect();
            let total: u64 = res.iter().map(|r| r.1).sum();
            let surv: Vec<Vec<i64>> = res.into_iter().flat_map(|r| r.0).collect();
            eprintln!("m={} H={} primitive families={} prefilter survivors={} time={:.1}s", m, h, total, surv.len(), t0.elapsed().as_secs_f64());
            let mm = m as i64; let n = mm + 1;
            let rows: Vec<String> = surv.par_iter().filter_map(|v| {
                let (p, q, d) = ml(v);
                if mm * p >= q { return None; } // ML >= 1/m: not in the sub-1/m spectrum
                let (nd, dc, l1o) = flags(v);
                let cls = if n * p < q { "BELOW" } else if n * p == q { "TIGHT" } else { "above" };
                Some(format!("{} ML={}/{} (m+1)ML-1={}/{} dens={:?} n|speed={} DC={} L1O={} v={:?}", cls, p, q, n * p - q, q, d, nd, dc, l1o, v))
            }).collect();
            let mut o = std::io::stdout().lock();
            writeln!(o, "# m={} H={} primitive={} sub-1/m families={}", m, h, total, rows.len()).unwrap();
            for r in rows { writeln!(o, "{}", r).unwrap(); }
            eprintln!("total time {:.1}s", t0.elapsed().as_secs_f64());
        }
        _ => panic!("mode"),
    }
}
