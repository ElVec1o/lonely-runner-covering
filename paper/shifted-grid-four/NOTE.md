# Four moving runners with phases in (1/5)Z: a hand proof and its Lean version

Vico Bonfioli. Version of 12 November 2026 (release 1.2.0 of this archive). Preprint note, not peer reviewed.

## Status

* **Statement.** Let v_1, ..., v_4 be pairwise distinct positive integers and s_1, ..., s_4 integers. Then there is a real t with dist(v_i t + s_i/5, Z) >= 1/5 for i = 1, ..., 4.
* **Lean entry point.** `LRSpectrumFull.TPp_four : TPp 4`, module `LRSpectrumFull.TPFourFinal` (`lean/LRSpectrumFull/TPFourFinal.lean`). Built on 2026-11-12 in the development repository, one module at a time. Axioms observed for `TPp_four` and for `five_runners` by a fresh review session: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`. The builds are carried over to this archive and were not repeated for it.
* **Text of the release (base wording of the review).** We formalize in Lean 4 (Mathlib; axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide) a short proof that for any four distinct positive integer speeds v_i and any integers s_i there is a real t with dist(v_i t + s_i/5, Z) >= 1/5 for every i. This is a special case (phases restricted to the grid (1/5)Z) of the shifted Lonely Runner Conjecture for four moving runners, already proved with computer assistance by Alcantara, Criado and Santos (arXiv:2506.13379); our contribution is a hand proof not using their enumeration of 2,133,561 velocity vectors, and its machine-checked version, which relies on a previously formalized Lean proof of the unshifted case. The distinctness of the speeds is necessary (v = (1,1,1,5), s = (0,1,3,0) has no solution), and nothing here covers arbitrary real phases or more than four moving runners.

### Caveats that bind every use of this note

1. **Not a new theorem.** The statement is a special case of the shifted lonely runner conjecture for four moving runners, proved with computer assistance by Alcantara, Criado and Santos, arXiv:2506.13379 (Corollary 1.4, as read locally by a review session; the journal status of that paper was not checked). What this note offers is a hand proof that does not use their enumeration of 2,133,561 velocity vectors, and its Lean version.
2. **Grid phases only.** The phases are s_i/5 with s_i an integer, a finite grid of 625 phase classes modulo 1. Arbitrary real phases are not covered. (Integer phases proper would be trivial: they are invisible modulo 1.)
3. **Dependency.** The Lean proof rests on the previously formalized unshifted five-runner theorem `five_runners` (module `Delta2FiveRunners`, already in this archive), which is the all-phases-zero slice of the statement and is used once, in step 5b below. The proof of `five_runners` (about 1,000 lines, with kernel `decide`) was not re-derived end to end in this release; its statement and axioms were checked by the review session.
4. **Distinctness is necessary.** For v = (1,1,1,5) and s = (0,1,3,0) there is no t with all four distances at least 1/5 (check at the end of this note). The best value is 1/6 (exact scan by the review session; the program is not archived).
5. **Build scope.** No whole-library `lake build` was run. The modules were built one at a time and the axioms were observed per module.

Other scope limits: repeated speeds, thresholds other than 1/5, and more than four moving runners are not covered.

### Labels and provenance

The statement in Lean is VERIFIED in the sense of the other manuscripts of this archive (carried over, not rebuilt). The written proof below is the argument that the Lean modules formalize (the module headers cite its lemmas). Its first version was checked step by step by two fresh AI sessions, which found no gap and proposed corrections and wording changes (six in all); these are incorporated in the text below. The corrected text as such was not read again by a fresh session as a text, and no blind read of the Part H kind has been run; the Lean statement and kernel check are the authority. The proof does not use Alcantara, Criado and Santos.

Comments in the Lean modules of this release cite development files by their development names. `HANDPROOF_v2.md` (also written `HANDPROOF_v2`) is the hand proof published here as `NOTE.md`, with the same lemma numbering; its "v2 fix" tags refer to the corrections mentioned above, which are incorporated in this text. The other cited files (`REVIEW2`, `LEAN_PORT_PLAN.md`, `TP4_REPORT.md`, `TP3_REPORT.md`, `CASEA_REPORT.md`, `tp3/gen_f.c`) are development files that are not archived.

The results were obtained with the assistance of an AI system (Claude, Anthropic). The questions and research directions came from the author. The written proof and the Lean sources were produced by the AI system; the Lean theorem is checked by the Lean kernel, and the written argument, the Lean statement and the sources were read or re-run by further sessions of the same system. The author is responsible for all claims.

## Conceptual abstract

Write the time as a whole number of fifths plus a small real offset. Runners whose speed is a multiple of five see only the offset. Every other runner, once the offset is fixed, forbids at most two of the five residue classes of the whole number. Easy cases follow from pigeonhole or from a smaller instance of the same statement. The one hard case has three free runners and one runner pinned at zero. Put the three free runners in a common coordinate on the five residues, where each forbidden set is a short arc. Either two arcs can be forced to meet, so some residue stays free, or the arcs cluster, or the shifts vanish and the unshifted four-runner theorem applies. A tiny adjustment of the offset keeps the pinned runner away from zero.

## Outline

* Rescale and decompose t = (j+x)/5 (Lemma 0, Lemma 1).
* Pigeonhole when nobody is pinned (Lemma 2, which is `TP_prime_free` in `TPPrime.lean`).
* Every case with at most two free runners reduces to fewer runners (Lemma 3, induction). Only the hard case H is left.
* Case H with residue classes 2+1: one pair has to intersect (Lemmas 4, 5).
* Case H with all three free runners in one class: coincidence, or the unshifted conjecture, or clustering (Lemmas 6, 7).

## Statement

v_1..v_4 are distinct positive integers and s_1..s_4 are integers. Then some real t satisfies ||v_i t + s_i/5|| >= 1/5 for every i.

## 1. Set-up

||y|| is the distance from y to Z. G := [1,4] + 5Z is the set of "good" residues on R/5Z.

**Lemma 0 (rescale).** If g = gcd(v), replacing v_i by v_i/g and t by g t changes nothing. So assume gcd(v_1..v_4) = 1.

**Lemma 1 (decomposition).** Put t = (j+x)/5 with j in Z and x in R. Then:
(a) if 5 | v_i, say v_i = 5w_i, runner i is good iff ||w_i x + s_i/5|| >= 1/5. This does not depend on j.
(b) if 5 does not divide v_i, runner i is good iff v_i j + s_i + v_i x is in G (mod 5). For fixed x this fails for at most 2 residues j mod 5. It fails for exactly one residue if v_i x is in Z.

Proof. (a) v_i t + s_i/5 = w_i j + w_i x + s_i/5. (b) 5(v_i t + s_i/5) = v_i j + s_i + v_i x, and ||y|| >= 1/5 iff 5y is in G.
The map j -> v_i j is a bijection of Z/5. Runner i is bad iff v_i j is congruent to an integer in the open interval
(-1-beta, 1-beta) (mod 5), where beta = s_i + v_i x. An open interval of length 2 contains at most 2 integers, and it contains
exactly 1 when beta is in Z. QED

Classes: A = {i : 5 does not divide v_i} (free), B = {5 | v_i, 5 does not divide s_i}, Z = {5 | v_i, 5 | s_i} (pinned).

## 2. Easy cases

**Lemma 2 (Z empty).** Take t = j/5 (x = 0). Runners in B are always good. Each runner in A excludes one j. Four
runners exclude at most 4 of the 5 residues. This is exactly `TP_prime_free` at p = 5. QED

**Lemma 3 (statement S(k) for k <= 3).** S(k) states: for k <= 3 distinct positive speeds and phases in
(1/5)Z there is a good t. The induction is over k <= 3 only. The k = 4 clause is a separate statement, Lemma 3', not
used inductively.
Proof of S(k), by induction on k <= 3. Rescale (Lemma 0). If Z is empty, use Lemma 2. Otherwise A is nonempty because gcd = 1, and
|A| <= 2 (this is automatic, since |A| <= k-1 <= 2). The runners in Z u B (k' = k - |A| < k of them, with speeds
w_i = v_i/5 distinct and positive and the same phases) form an instance of S(k'). By induction it has a solution x.
By Lemma 1(a) this x makes all of Z u B good, for every j. By Lemma 1(b) the runners in A exclude at most 2|A| <= 4
residues j. Pick any remaining j. (S(0) is vacuous.) QED

**Lemma 3' (k = 4, Z nonempty, |A| <= 2).** If k = 4, Z is nonempty and |A| <= 2, there is a good t.
Proof. Same argument as for S(k): rescale, A is nonempty because gcd = 1, the runners in Z u B (k' = 4 - |A| <= 3 of them)
form an instance of S(k'), which holds by Lemma 3 (the case k' <= 3 only). Then Lemma 1(a), 1(b) and the choice of j
are as above. QED

So, by Lemmas 0-3, the statement is reduced to:

**Case H.** A = {a,b,c} (speeds not divisible by 5, arbitrary phases), and one pinned runner of speed 5w with phase congruent to 0.
By Lemma 1 it suffices to find x with ||wx|| >= 1/5 such that the bad sets J_a, J_b, J_c in Z/5 (for this x) do not cover Z/5.

## 3. Common coordinate (used by Cases 2+1 and 3)

Fix runner a and put z = v_a j (mod 5), a bijection of Z/5. If v_i is congruent to lambda_i v_a (mod 5), then by Lemma 1(b) the bad set
of runner i in z-coordinates is lambda_i^{-1} times {integers in (c'-1, c'+1)}, where c' = -(s_i + v_i x). Hence:
* if lambda_i = eps_i = +-1: J_i = {integers z in (c_i - 1, c_i + 1)}, with centre c_i = -eps_i(s_i + v_i x) (mod 5). This is
  an "arc set": one integer, or two consecutive integers.
* if lambda_i = +-2: J_i is one integer or two integers that differ by 2 (a "pentagram edge").

For two runners i, k with lambda = +-1, write V_i = eps_i v_i and S_i = eps_i s_i. Then
  c_k - c_i = sigma_ik + 5 D_ik x (mod 5),   sigma_ik := S_i - S_k,   D_ik := (V_i - V_k)/5, an integer different from 0.
(D_ik is not 0 because the speeds are distinct and positive.) Write R_ik(x) := sigma_ik/5 + D_ik x (mod 1), so
c_k - c_i = 5 R_ik.

**Lemma 4 (two-runner window).** Let D != 0 and w >= 1 be integers and sigma an integer. Then there is x with
||Dx + sigma/5|| <= 1/5 and ||wx|| >= 1/5.

Proof. Put x_k = (k - sigma/5)/D, so D x_k + sigma/5 = k.
* If |D| does not divide w, the numbers w x_k (k in Z) form a coset of (1/n)Z with n = |D|/gcd(D,w) >= 2. The spacing 1/n <= 1/2
  is less than 3/5, the length of [1/5, 4/5], so some w x_k is far from Z.
* If w = |D| w', set c_0 = w x_0 (mod 1), taking the representative c_0 in (-1/2, 1/2],
  and take x = x_0 + eta. Then ||Dx + sigma/5|| = |D eta|, and w x = c_0 + w eta (mod 1).
  If ||c_0|| >= 1/5, take eta = 0. Otherwise c_0 is in (-1/5, 1/5) and we take w eta = sign(c_0)/5 - c_0
  (with sign(0) = +). Then |w eta| <= 1/5, so
  |D eta| <= 1/(5w') <= 1/5, and ||wx|| = 1/5. QED

**Lemma 5 (Case 2+1).** Suppose a, b are in the same class (v_a congruent to +-v_b mod 5) and c is in the other class.
Then Case H holds.

Proof. Take x from Lemma 4 with D = D_ab and sigma = sigma_ab. Then |c_b - c_a| <= 1 on R/5Z. Two arc sets whose centres are
within distance 1 of each other either intersect or are both singletons. To check this: if c_a is not in Z and
0 <= c_b - c_a <= 1, then ceil(c_a) lies in both open intervals (the case of the opposite sign is symmetric, with floor(c_a));
if c_a is in Z and the distance is < 1, then c_a is in J_b; if the distance is exactly 1 and c_a is in Z, both sets are singletons.
* If both are singletons, |J_a| + |J_b| + |J_c| <= 4.
* If J_a and J_b intersect, then their union is at most 3 consecutive z's. For J_c to cover the other two, which are consecutive,
  it would have to contain two consecutive z's, which a pentagram edge does not.

So the union of J_a, J_b, J_c is not Z/5. QED

(The window slack is needed. With exact coincidence only, a checker written during the development failed on 19,600 instances at N = 20; that program is not archived.)

## 4. Case 3: v_a, v_b, v_c all in one class

Choose eps_i so that V_i is congruent to a common r (mod 5). All three J_i are arc sets with centres c_i. The three pairs ik have
sigma_ab + sigma_bc + sigma_ca congruent to 0.

**Lemma 6 (coincidence).** If for some pair ik we do NOT have [D_ik | w and 5 | (w/D_ik) sigma_ik], then Case H holds.

Proof. At x_k = (k - sigma_ik/5)/D_ik the two centres coincide, so J_i = J_k and the union of the J's has at most 4 elements. The pinned values w x_k form a
coset of (1/n)Z with n = |D_ik|/gcd(D_ik, w). If n >= 2, some value is far from Z (as in Lemma 4). If n = 1, the single
value is -(w/D_ik) sigma_ik/5 (mod 1), and it is far from Z iff 5 does not divide (w/D_ik) sigma_ik. QED

Now assume Lemma 6 fails for all three pairs. Below, "sigma = 0" and "sigma != 0" mean congruence and non-congruence mod 5.

**5b (all sigma congruent to 0 mod 5).** Then S_a, S_b, S_c are congruent to a common S. Choose an integer tau with r tau congruent to -S (mod 5). Then V_i tau + S_i is congruent to 0, so
v_i tau + s_i is congruent to 0 (mod 5) for i in A. Write T = 5t = T_0 + tau. Runner i in A is good iff ||v_i T_0/5|| >= 1/5, and the
pinned runner is good iff ||5w (T_0/5)|| >= 1/5 (w tau is an integer). This is the unshifted lonely runner statement for the four speeds
a, b, c, 5w at u = T_0/5, which `five_runners` gives. Then t = u + tau/5. QED

**Lemma 7 (cluster).** Suppose sigma_ab != 0 and sigma_ac != 0 (mod 5) (hub a). Under the standing assumption (Lemma 6 fails), this
gives D_ab | w and 5 | w/D_ab, so |D_ab| <= w/5, and likewise |D_ac| <= w/5. Then Case H holds.

Proof. Write D_b = D_ab, D_c = D_ac (distinct, nonzero), R_b = R_ab, R_c = R_ac.
(i) There is x_0 such that {0, R_b(x_0), R_c(x_0)} lies in an arc of length <= 8/25 of R/Z:
* At the zeros x_k = (k - sigma_b/5)/D_b of R_b, the values R_c(x_k) form a coset of (1/|p|)Z, where g = gcd(D_b, D_c) > 0,
  D_b = gp, D_c = gq (so p, q carry the signs of D_b, D_c) and gcd(p,q) = 1. If |p| >= 2, the closed arc [-8/25, 8/25] (length 16/25 >= 1/2) contains one of them.
* Otherwise, if |q| >= 2, the same argument works at the zeros of R_c.
* Otherwise D_c = -D_b (D_c = D_b is impossible). With u = D_b x, choose u = (sigma_c - sigma_b)/10 + k/2. Then
  R_b = R_c is in {tau/10, tau/10 + 1/2} with tau = sigma_b + sigma_c, and one of these two values has ||.|| <= 1/4.

(ii) Perturb: choose eta with |w eta| <= 1/5 and ||w(x_0 + eta)|| >= 1/5 (as in Lemma 4, with c_0 = w x_0 taken in
(-1/2, 1/2] and, in the perturbed branch, c_0 in (-1/5, 1/5)). This moves R_b and R_c by at most
|D|/(5w) <= 1/25 each, so the spread becomes <= 8/25 + 2/25 = 2/5.

(iii) The spread of the centres in R/5Z is then <= 2. Every J_i lies in the integers of one open interval of length 4,
so the union of the J's has at most 4 elements. QED

**Closing Case 3.** If Lemma 6 fails for all pairs and not all sigma are 0 (mod 5), then at least two of the sigma's are nonzero
(they sum to 0). Any two pairs of a triangle share a vertex; call it the hub, and Lemma 7 applies. Otherwise 5b applies.
This completes Case H, and with it the statement. QED

## 5. Remark on scope

This reduction is not available for general N = m+1. It uses that the three free runners fall into the two classes
+-1, +-2 mod 5, and that a pentagram edge is never an arc.

## 6. Distinctness is necessary

Take v = (1,1,1,5) and s = (0,1,3,0). The three runners of speed 1 are bad (distance below 1/5) exactly when t lies in the open arcs of half-width 1/5 centred at 0, 4/5 and 2/5 modulo 1, that is in (-1/5, 1/5), (3/5, 1) and (1/5, 3/5). Their union is the circle minus the two points 1/5 and 3/5. At t = 1/5 and t = 3/5 the runner of speed 5 and phase 0 is at 5t = 1 and 5t = 3, an integer, so its distance is 0. Hence no t makes all four distances at least 1/5. QED

(The value 1/6 for the best achievable minimum comes from an exact integer scan by the review session and is not proved here.)

## Lean correspondence (approximate)

Assembled from the module headers and declaration names; not checked line by line against the proof text. The full module list is in `LEAN_MAP.md`.

| Part of the proof | Lean declaration (module) |
|---|---|
| Statement | `TPp_four` (`TPFourFinal`), `TPp` and `tpDist` (`TPSmall`) |
| Lemma 0 to 3, 3' (rescale, easy cases, reduction to Case H) | `TPp_four_of_caseH`, `lemS`, `lemT` (`TPFourReduce`); Lemma 2 is `TP_prime_free` (`TPPrime`) |
| Lemma 1 | `good_mul5` (`TPFourBridge`), `badImg`, `card_badImg_le_two` (`TPFourLocal`) |
| Section 3, arcs, Lemma 5 | `arc`, `core5`, `exists_good_21` (`TPFourArcs`), `case21` (`TPFourCase21`) |
| Lemma 4 | `lemma4`, `coset_branch` (`TPFourCoset`), `exists_perturb` (`TPFourWindow`) |
| Lemma 6 | `case6`, `exists_exact` (`TPFourCoincide`) |
| Lemma 7 | `lemma7` (`TPFourLemma7`), `tight_window`, `cluster_real` (`TPFourTight`), `exists_window`, `three_arcs` (`TPFourWindow`), `hub` (`TPFourHub`) |
| Step 5b | `five_runners_tp`, `shift_five` (`TPFourFive`); `five_runners` (`Delta2FiveRunners`) |
| Case split of Case H and closing Case 3 | `caseH_of_case3` (`TPFourGlue`), `case3` (`TPFourCase3`) |
