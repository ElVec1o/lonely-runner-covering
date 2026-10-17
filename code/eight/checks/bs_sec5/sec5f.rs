// Farey carry model: q_j = j*a + c_j, c = (0, floor 2f, .., floor 5f), 10 patterns.
const C: [[u64;5];10] = [[0,0,0,0,0],[0,0,0,0,1],[0,0,0,1,1],[0,0,1,1,1],[0,0,1,1,2],[0,1,1,2,2],[0,1,1,2,3],[0,1,2,2,3],[0,1,2,3,3],[0,1,2,3,4]];
fn qj(a:u64,c:usize,j:usize)->u64{ ((j as u64)*a + C[c][j-1])%7 }
fn arc(vals: &[u64], len: u64) -> bool { (0..7).any(|t| vals.iter().all(|&v| (v+7-t)%7 < len)) }
fn main(){
  let js=|n:usize, len:u64, jmax:usize| { let mut bad=0u64; let mut tot=0u64;
    let total = 70usize.pow(n as u32);
    for code in 0..total { let mut cc=code; let mut el=vec![]; for _ in 0..n { el.push(((cc%70)/10, cc%10)); cc/=70; }
      tot+=1; if !(1..=jmax).any(|j| arc(&el.iter().map(|&(a,c)| qj(a as u64,c,j)).collect::<Vec<_>>(), len)) { bad+=1; } }
    (bad,tot) };
  println!("F1 Farey (4,len5,j<=5): {:?}", js(4,5,5));
  println!("F1 Farey (4,len5,j<=4): {:?}", js(4,5,4));
  println!("F2 Farey (3,len4,j<=5): {:?}", js(3,4,5));
  println!("F2 Farey (3,len4,j<=4): {:?}", js(3,4,4));
  println!("F3 Farey (2,len2,j<=5): {:?}", js(2,2,5));
  println!("NC F3 Farey (2,len2,j<=4): {:?}", js(2,2,4));
  println!("NC F3 Farey (2,len1,j<=5): {:?}", js(2,1,5));
}
