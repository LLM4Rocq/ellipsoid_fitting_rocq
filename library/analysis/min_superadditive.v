From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean.
From mathcomp Require Import boolp classical_sets reals topology normedtype.
From mathcomp Require Import sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.

(**md**************************************************************************)
(* # Convergence from approximate minimum inequalities                        *)
(*                                                                            *)
(* A real sequence u whose value at the sum of two comparable sizes is at     *)
(* least the smaller of their two values minus A min(r, s)^(-beta), and which *)
(* loses at most A s^(-beta) from s to s + 1, satisfies                       *)
(* u n >= u s - A (1 + E) s^(-beta) for every n >= s^2, with                  *)
(* E = 3^beta / ((3/2)^beta - 1); if it is bounded, it converges, and its     *)
(* limit satisfies the same bound. Here A >= 0 and beta > 0, the sizes r and  *)
(* s are comparable when r <= 3 s and s <= 3 r, and both inequalities are     *)
(* assumed only for sizes at least some N. The exponent only needs to be      *)
(* positive: the errors are summed along geometrically increasing sizes.      *)
(*                                                                            *)
(* - min_superadditive_blocks: the value at q blocks of size s and r <= q     *)
(*   blocks of size s + 1 is at least                                         *)
(*   u s - A s^(-beta) - A E s^(-beta) (1 - q^(-beta));                       *)
(*   min_superadditive_tail, the bound for n >= s^2.                          *)
(* - min_superadditive_liminf, min_superadditive_cvgn and                     *)
(*   min_superadditive_lim_ge: for a bounded sequence, the lower limit        *)
(*   satisfies the bound, the sequence converges, and its limit satisfies the *)
(*   bound.                                                                   *)
(* - limn_inf_sup_cvg: a bounded real sequence whose upper limit is at most   *)
(*   its lower limit converges, the converse of cvg_limn_inf_sup of           *)
(*   MathComp-Analysis.                                                       *)
(* - balance_potential: the power potential of the balanced decomposition,    *)
(*   a^(-beta) <= E (b^(-beta) - q^(-beta)) for q/3 <= a and                  *)
(*   0 < b <= 2 q / 3.                                                        *)
(* - The example alternating_cvgn: (-1)^n / (n + 1) satisfies both            *)
(*   inequalities with A = 2, beta = 1 and N = 1, and converges.              *)
(*                                                                            *)
(* Target T12 of phase 13 (AGENTS.md, section Phase 13): a Rocq formalization *)
(* of the credited argument of the lemma 'Balanced comparisons' of 'A         *)
(* Limiting Satisfiability Threshold for Every Fixed Clause Size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/convergence.tex), where it turns the comparisons between   *)
(* the centers of the satisfiability threshold at different sizes into their  *)
(* convergence. It follows the strong induction with a power potential of the *)
(* Lean development of the collection, in lean/OAI/Probability/RandomSAT:     *)
(* Lean: summable_min_convergence (Convergence.lean, line 141)                *)
(*                                                                            *)
(* Two departures, decided by the user on 14 October 2026. The sum comparison *)
(* is assumed only for comparable sizes, as in the manuscript; the Lean lemma *)
(* assumes it for all sizes, and its induction uses it only for comparable    *)
(* ones. The constant E is the one of the Lean development: (4/3)^beta times  *)
(* the constant (3/2)^beta / (1 - (2/3)^beta) of the manuscript, so larger,   *)
(* and enough for the satisfiability threshold.                               *)
(*                                                                            *)
(* ```                                                                        *)
(*   balance_const beta == 3^beta / ((3/2)^beta - 1), the constant E          *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section powR_neg.
Variable R : realType.
Implicit Types x y r : R.

Lemma powR_invl x r : 0 < x -> x^-1 `^ r = (x `^ r)^-1.
Proof.
move=> x0; rewrite /powR !gt_eqF ?invr_gt0 //.
by rewrite lnV ?posrE // mulrN expRN.
Qed.

(* x |-> x^(-r) is nonincreasing on the positive reals for r >= 0. *)
Lemma powRN_le x y r : 0 < x -> x <= y -> 0 <= r -> y `^ (- r) <= x `^ (- r).
Proof.
move=> x0 xy r0; have y0 := lt_le_trans x0 xy.
rewrite !powRN lef_pV2 ?posrE ?powR_gt0 //.
by rewrite ge0_ler_powR // nnegrE ltW.
Qed.

Lemma powRN_inv x r : 0 < x -> x^-1 `^ (- r) = x `^ r.
Proof. by move=> x0; rewrite powRN powR_invl // invrK. Qed.

End powR_neg.

Section balance_const.
Variable R : realType.
Implicit Types (beta a b q : R).

Definition balance_const beta : R := 3 `^ beta / ((3 / 2) `^ beta - 1).

Lemma three_halves_powR_gt1 beta : 0 < beta -> 1 < (3 / 2 : R) `^ beta.
Proof.
move=> b0; have := @gt0_ltr_powR R beta b0 1 (3 / 2).
rewrite powR1 /= => -> //; rewrite ?nnegrE //; lra.
Qed.

Lemma balance_const_gt0 beta : 0 < beta -> 0 < balance_const beta.
Proof.
move=> b0; rewrite /balance_const divr_gt0 ?powR_gt0 //.
by rewrite subr_gt0 three_halves_powR_gt1.
Qed.

Lemma balance_constE beta : 0 < beta ->
  balance_const beta * ((3 / 2) `^ beta - 1) = 3 `^ beta.
Proof.
move=> b0; rewrite /balance_const mulfVK // subr_eq0 gt_eqF //.
exact: three_halves_powR_gt1.
Qed.

(* The power potential of the balanced decomposition. *)
Lemma balance_potential beta a b q : 0 < beta -> 0 < b -> 0 < q ->
  q / 3 <= a -> b <= q / (3 / 2) ->
  a `^ (- beta) <= balance_const beta * (b `^ (- beta) - q `^ (- beta)).
Proof.
move=> b0 bpos q0 qa bq.
have q3 : 0 < q / 3 by rewrite divr_gt0.
have qp := powR_gt0 (- beta) q0.
have h3 : (0 : R) <= 3^-1 by rewrite invr_ge0 ler0n.
have h32 : (0 : R) <= (3 / 2)^-1 by rewrite invr_ge0; lra.
have ha : a `^ (- beta) <= q `^ (- beta) * 3 `^ beta.
  apply: le_trans (powRN_le q3 qa (ltW b0)) _.
  by rewrite (powRM (- beta) (ltW q0) h3) powRN_inv ?ltr0n.
have hb : q `^ (- beta) * (3 / 2) `^ beta <= b `^ (- beta).
  apply: le_trans _ (powRN_le bpos bq (ltW b0)).
  rewrite (powRM (- beta) (ltW q0) h32) powRN_inv //; lra.
apply: le_trans ha _.
rewrite -(balance_constE b0) mulrCA ler_pM2l ?balance_const_gt0 //.
by rewrite mulrBr mulr1 lerD2r.
Qed.

End balance_const.

Section limn_inf_sup.
Variable R : realType.
Implicit Types u : nat -> R.

Lemma infs_le_term u n : bounded_fun u -> infs u n <= u n.
Proof.
move=> bu; apply: ge_inf; last by exists n => //=.
exact: (has_lbound_sdrop (bounded_fun_has_lbound bu)).
Qed.

Lemma term_le_sups u n : bounded_fun u -> u n <= sups u n.
Proof.
move=> bu; apply: ub_le_sup; last by exists n => //=.
exact: (has_ubound_sdrop (bounded_fun_has_ubound bu)).
Qed.

(* The converse of cvg_limn_inf_sup: a bounded sequence whose upper limit
   is at most its lower limit converges. *)
Lemma limn_inf_sup_cvg u : bounded_fun u -> limn_sup u <= limn_inf u -> cvgn u.
Proof.
move=> bu le_si.
have ub := bounded_fun_has_ubound bu; have lb := bounded_fun_has_lbound bu.
have ci : infs u @ \oo --> limn_inf u.
  by rewrite limn_infE //; exact: cvg_infs_sup.
have cs : sups u @ \oo --> limn_sup u.
  by rewrite limn_supE //; exact: cvg_sups_inf.
have ge_is : limn_inf u <= limn_sup u.
  apply: (ler_cvg_to ci cs); apply: nearW => n.
  exact: le_trans (infs_le_term n bu) (term_le_sups n bu).
have e : limn_sup u = limn_inf u by apply/le_anti; rewrite le_si ge_is.
apply/cvg_ex; exists (limn_inf u).
apply: (@squeeze_cvgr _ _ _ _ (infs u) (sups u)); [|exact: ci|by rewrite -e].
by apply: nearW => n; rewrite infs_le_term ?term_le_sups.
Qed.

End limn_inf_sup.

Section min_superadditive.
Variable R : realType.
Variables (u : nat -> R) (A beta : R) (N : nat).
Hypotheses (A_ge0 : 0 <= A) (beta_gt0 : 0 < beta).
Hypothesis u_sum : forall r s, (N <= r)%N -> (N <= s)%N ->
  (r <= 3 * s)%N -> (s <= 3 * r)%N ->
  Num.min (u r) (u s) - A * (minn r s)%:R `^ (- beta) <= u (r + s)%N.
Hypothesis u_next : forall s, (N <= s)%N ->
  u s - A * s%:R `^ (- beta) <= u s.+1.

Local Notation E := (balance_const beta).

Lemma blocks_arith (us Ac P B Q m mm : R) :
  us - Ac - P * (1 - B) <= m -> mm <= P * (B - Q) ->
  us - Ac - P * (1 - Q) <= m - mm.
Proof. by move=> h1 h2; lra. Qed.

(* The value at q blocks of size s and r <= q blocks of size s + 1. *)
Lemma min_superadditive_blocks s q r : (N <= s)%N -> (2 <= s)%N ->
  (1 <= q)%N -> (r <= q)%N ->
  u s - A * s%:R `^ (- beta)
      - A * E * s%:R `^ (- beta) * (1 - q%:R `^ (- beta))
    <= u (q * s + r)%N.
Proof.
move=> Ns s2; have s0 : (0 < s)%N by apply: leq_trans s2.
have c0 : 0 <= s%:R `^ (- beta) :> R by exact: powR_ge0.
have E0 := balance_const_gt0 beta_gt0.
have P0 : 0 <= A * E * s%:R `^ (- beta).
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: ltW.
elim/ltn_ind: q r => q IH r q1 rq.
have [q2|] := leqP 2 q; last first.
  rewrite ltnS => q1'; have /eqP q_1 : q == 1%N by rewrite eqn_leq q1' q1.
  have -> : q%:R `^ (- beta) = 1 :> R by rewrite q_1 powR1.
  rewrite q_1 mul1n subrr mulr0 subr0.
  have : (r == 0)%N || (r == 1)%N by move: rq; rewrite q_1; case: r => [|[]].
  case/orP=> /eqP ->; last by rewrite addn1; exact: u_next.
  by rewrite addn0 lerBlDr lerDl mulr_ge0.
set a := (q %/ 2)%N; set b := (q - a)%N.
have qE : q = (a * 2 + q %% 2)%N := divn_eq q 2.
have e1 : (q %% 2 <= 1)%N by rewrite -ltnS ltn_pmod.
have a1 : (1 <= a)%N by rewrite /a divn_gt0.
have ea : (q %% 2 <= a)%N := leq_trans e1 a1.
have bE : b = (a + q %% 2)%N.
  by rewrite /b {1}qE muln2 -addnn -addnA addKn.
have ab : (a <= b)%N by rewrite bE leq_addr.
have aq : (a < q)%N by rewrite /a ltn_Pdiv // (leq_trans _ q2).
have bq : (b < q)%N by rewrite /b ltn_subrL a1 q1.
have b1 : (1 <= b)%N := leq_trans a1 ab.
have qa3 : (q <= a * 3)%N by rewrite {1}qE (mulnSr a 2) leq_add2l.
have b2a : (b <= a * 2)%N by rewrite bE muln2 -addnn leq_add2l.
have b3q : (b * 3 <= q * 2)%N.
  rewrite -(ler_nat R) !natrM; move: ea; rewrite -(ler_nat R) => ea'.
  by rewrite bE {2}qE !natrD !natrM; lra.
set r1 := minn r a; set r2 := (r - r1)%N.
have r1a : (r1 <= a)%N by rewrite geq_minr.
have rr : (r1 + r2 = r)%N by rewrite subnKC // geq_minl.
have r2b : (r2 <= b)%N.
  rewrite /r2 /r1; case: (leqP r a) => [ra|ar]; first by rewrite subnn.
  by rewrite leq_subLR /b subnKC ?(ltnW aq).
have IHa := IH a aq r1 a1 r1a.
have IHb := IH b bq r2 b1 r2b.
set X := (a * s + r1)%N; set Y := (b * s + r2)%N.
have XY : (X + Y = q * s + r)%N.
  by rewrite /X /Y addnACA -mulnDl rr /b subnKC ?(ltnW aq).
have asX : (a * s <= X)%N by rewrite /X leq_addr.
have bsY : (b * s <= Y)%N by rewrite /Y leq_addr.
have asbs : (a * s <= b * s)%N by rewrite leq_mul2r ab orbT.
have h3s : (s < 3 * s)%N by rewrite ltn_Pmull.
have Ns_as : (N <= a * s)%N by apply: leq_trans Ns (leq_pmull _ a1).
have NX : (N <= X)%N := leq_trans Ns_as asX.
have NY : (N <= Y)%N := leq_trans Ns_as (leq_trans asbs bsY).
have X3Y : (X <= 3 * Y)%N.
  apply: (@leq_trans (a * s.+1)); first by rewrite /X mulnS addnC leq_add2r.
  apply: (@leq_trans (b * s.+1)); first by rewrite leq_mul2r ab orbT.
  apply: (@leq_trans (3 * (b * s))); last by rewrite leq_mul2l bsY orbT.
  by rewrite [(3 * _)%N]mulnCA leq_mul2l h3s orbT.
have Y3X : (Y <= 3 * X)%N.
  apply: (@leq_trans (b * s.+1)); first by rewrite /Y mulnS addnC leq_add2r.
  apply: (@leq_trans (a * 2 * s.+1)); first by rewrite leq_mul2r b2a orbT.
  apply: (@leq_trans (3 * (a * s))); last by rewrite leq_mul2l asX orbT.
  by rewrite -mulnA [(3 * _)%N]mulnCA leq_mul2l mulnSr (mulSnr 2) leq_add2l
    s2 orbT.
have := u_sum NX NY X3Y Y3X; rewrite XY => hsum; apply: le_trans hsum.
have hB : b%:R `^ (- beta) <= a%:R `^ (- beta) :> R.
  by apply: powRN_le; rewrite ?ltr0n ?ler_nat ?ltW.
have hmin : u s - A * s%:R `^ (- beta)
    - A * E * s%:R `^ (- beta) * (1 - b%:R `^ (- beta))
    <= Num.min (u X) (u Y).
  rewrite le_min IHb andbT; apply: le_trans IHa.
  by apply: lerB => //; apply: ler_wpM2l => //; apply: lerB.
have hm : (minn X Y)%:R `^ (- beta)
    <= a%:R `^ (- beta) * s%:R `^ (- beta) :> R.
  rewrite -powRM ?ler0n // -natrM.
  apply: powRN_le; last exact: ltW.
    by rewrite ltr0n muln_gt0 a1 s0.
  by rewrite ler_nat leq_min asX (leq_trans asbs bsY).
have hp : a%:R `^ (- beta)
    <= E * (b%:R `^ (- beta) - q%:R `^ (- beta)) :> R.
  apply: balance_potential; rewrite ?ltr0n //.
    by rewrite ler_pdivrMr ?ltr0n // -natrM ler_nat.
  have : (b * 3)%:R <= (q * 2)%:R :> R by rewrite ler_nat.
  by rewrite !natrM => h; rewrite ler_pdivlMr; lra.
apply: blocks_arith hmin _.
have -> : A * E * s%:R `^ (- beta) * (b%:R `^ (- beta) - q%:R `^ (- beta))
    = A * (E * (b%:R `^ (- beta) - q%:R `^ (- beta)) * s%:R `^ (- beta)).
  by ring.
apply: le_trans (ler_wpM2l A_ge0 hm) _.
by rewrite ler_wpM2l // ler_wpM2r.
Qed.

(* The finite-size bound: n >= s^2 is a sum of blocks of sizes s and s + 1. *)
Lemma min_superadditive_tail s n : (N <= s)%N -> (2 <= s)%N ->
  (s * s <= n)%N ->
  u s - A * (1 + E) * s%:R `^ (- beta) <= u n.
Proof.
move=> Ns s2 ssn; have s0 : (0 < s)%N by apply: leq_trans s2.
have qs : (s <= n %/ s)%N by rewrite leq_divRL.
have rq : (n %% s <= n %/ s)%N by apply: leq_trans (ltnW (ltn_pmod n s0)) qs.
have := min_superadditive_blocks Ns s2 (leq_trans s0 qs) rq.
rewrite -divn_eq; apply: le_trans.
have E0 := balance_const_gt0 beta_gt0.
have c0 : 0 <= s%:R `^ (- beta) :> R by exact: powR_ge0.
have Q0 : 0 <= (n %/ s)%:R `^ (- beta) :> R by exact: powR_ge0.
have P0 : 0 <= A * E * s%:R `^ (- beta) * (n %/ s)%:R `^ (- beta).
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; apply: mulr_ge0 => //;
    exact: ltW.
have -> : u s - A * s%:R `^ (- beta)
    - A * E * s%:R `^ (- beta) * (1 - (n %/ s)%:R `^ (- beta))
    = u s - A * (1 + E) * s%:R `^ (- beta)
      + A * E * s%:R `^ (- beta) * (n %/ s)%:R `^ (- beta) by ring.
by rewrite lerDl.
Qed.

(* The same bound for the lower limit of a bounded sequence. *)
Lemma min_superadditive_liminf s : bounded_fun u -> (N <= s)%N ->
  (2 <= s)%N -> u s - A * (1 + E) * s%:R `^ (- beta) <= limn_inf u.
Proof.
move=> bu Ns s2; rewrite limn_infE //.
have hi : u s - A * (1 + E) * s%:R `^ (- beta) <= infs u (s * s).
  apply: lb_le_inf; first by exists (u (s * s)%N), (s * s)%N => /=.
  by move=> _ [n /= ssn <-]; exact: min_superadditive_tail.
apply: le_trans hi _; apply: ub_le_sup; last by exists (s * s)%N.
exact: bounded_fun_has_ubound_infs.
Qed.

Lemma powRN_small (e : R) : 0 < e ->
  exists k : nat, forall s, (k <= s)%N -> s%:R `^ (- beta) <= e.
Proof.
move=> e0; set y := e^-1 `^ beta^-1.
exists (Num.truncn y).+1 => s ks.
have y0 : 0 <= y by exact: powR_ge0.
have ys : y < s%:R.
  by apply: lt_le_trans (truncnS_gt y) _; rewrite ler_nat.
have s0 : 0 < s%:R :> R by apply: le_lt_trans ys.
rewrite powRN -[e]invrK lef_pV2 ?posrE ?invr_gt0 ?powR_gt0 //.
have -> : e^-1 = y `^ beta.
  rewrite /y -powRrM mulVf ?gt_eqF // powRr1 // invr_ge0 ltW //.
by apply: (ge0_ler_powR (ltW beta_gt0)); rewrite ?nnegrE // ltW.
Qed.

Theorem min_superadditive_cvgn : bounded_fun u -> cvgn u.
Proof.
move=> bu; apply: limn_inf_sup_cvg => //.
have E0 := balance_const_gt0 beta_gt0.
have C0 : 0 < A * (1 + E) + 1.
  by rewrite ltr_pwDr // mulr_ge0 // addr_ge0 // ltW.
apply/ler_addgt0Pr => e e0.
have [k hk] := powRN_small (divr_gt0 e0 C0).
set K := maxn k (maxn N 2).
have kK : (k <= K)%N by rewrite leq_maxl.
have NK : (N <= K)%N by rewrite leq_max leq_maxl orbT.
have K2 : (2 <= K)%N by rewrite leq_max leq_maxr orbT.
rewrite limn_supE //.
have hK : inf (range (sups u)) <= sups u K.
  by apply: ge_inf; [exact: bounded_fun_has_lbound_sups | by exists K].
apply: le_trans hK _; apply: ge_sup; first by exists (u K), K => /=.
move=> _ [s /= Ks <-].
have Ns := leq_trans NK Ks; have s2 := leq_trans K2 Ks.
have := min_superadditive_liminf bu Ns s2.
have hs := hk s (leq_trans kK Ks).
have hd : A * (1 + E) * s%:R `^ (- beta) <= e.
  apply: le_trans (ler_wpM2l _ hs) _.
    by rewrite mulr_ge0 // addr_ge0 // ltW.
  have C1 : 0 <= A * (1 + E) by rewrite mulr_ge0 // addr_ge0 // ltW.
  by rewrite mulrA ler_pdivrMr //; nra.
by move=> h; lra.
Qed.

(* The limit satisfies the finite-size bound. *)
Lemma min_superadditive_lim_ge s : bounded_fun u -> (N <= s)%N ->
  (2 <= s)%N -> u s - A * (1 + E) * s%:R `^ (- beta) <= limn u.
Proof.
move=> bu Ns s2; apply: limr_ge; first exact: min_superadditive_cvgn.
by exists (s * s)%N => // n /= ssn; exact: min_superadditive_tail.
Qed.

End min_superadditive.

Section alternating_example.
Variable R : realType.

(* An example independent of any application: u n = (-1)^n / (n + 1) is not
   monotone, satisfies the two inequalities with A = 2, beta = 1 and N = 1,
   and is bounded, so it converges. *)
Let alt (n : nat) : R := (-1) ^+ n / n.+1%:R.

Let alt_norm n : `|alt n| = n.+1%:R^-1.
Proof.
by rewrite /alt normrM normrX normrN1 expr1n mul1r normfV ger0_norm.
Qed.

Let alt_le n : alt n <= n.+1%:R^-1.
Proof. by rewrite -alt_norm ler_norm. Qed.

Let alt_ge n : - n.+1%:R^-1 <= alt n.
Proof. by rewrite -alt_norm lerNnormlW. Qed.

Let powN1 (n : nat) : n%:R `^ (- 1) = n%:R^-1 :> R.
Proof. by rewrite powR_inv1. Qed.

(* 1/(m + 1) - 2/m <= - 1/m for m >= 1. *)
Let alt_arith (m : nat) : (1 <= m)%N ->
  m.+1%:R^-1 - 2 * m%:R^-1 <= - m%:R^-1 :> R.
Proof.
move=> m1; have m0 : 0 < m%:R :> R by rewrite ltr0n.
have : m.+1%:R^-1 <= m%:R^-1 :> R.
  by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
set x := m.+1%:R^-1; set y := m%:R^-1; clearbody x y => h; lra.
Qed.

Lemma alternating_cvgn : cvgn alt.
Proof.
have bu : bounded_fun alt.
  exists 1; split; first by rewrite num_real.
  move=> M M1 n _ /=; rewrite alt_norm (le_trans _ (ltW M1)) //.
  by rewrite invf_le1 ?ler1n ?ltr0n.
apply: (@min_superadditive_cvgn R alt 2 1 1) => //.
- move=> r s r1 s1 _ _; rewrite powN1.
  set m := minn r s; have m1 : (1 <= m)%N by rewrite leq_min r1 s1.
  have hmin : Num.min (alt r) (alt s) <= m.+1%:R^-1.
    rewrite /m; case: (leqP r s) => rs; first by rewrite ge_min alt_le.
    by rewrite ge_min alt_le orbT.
  apply: le_trans _ (alt_ge (r + s)).
  have h1 : - m%:R^-1 <= - (r + s).+1%:R^-1 :> R.
    rewrite lerN2 lef_pV2 ?posrE ?ltr0n // ler_nat.
    by apply: leq_trans (geq_minl r s) _; rewrite leqW // leq_addr.
  have h2 := alt_arith m1.
  move: hmin h1 h2; set x := Num.min _ _; set y := m%:R^-1.
  set z := m.+1%:R^-1; set w := (r + s).+1%:R^-1.
  by clearbody x y z w => h0 h1 h2; lra.
- move=> s s1; rewrite powN1.
  apply: le_trans _ (alt_ge s.+1).
  have h1 : - s%:R^-1 <= - s.+2%:R^-1 :> R.
    by rewrite lerN2 lef_pV2 ?posrE ?ltr0n // ler_nat leqW.
  have h2 := alt_arith s1; have h3 := alt_le s.
  move: h1 h2 h3; set x := alt s; set y := s%:R^-1; set z := s.+1%:R^-1.
  set w := s.+2%:R^-1.
  by clearbody x y z w => h1 h2 h3; lra.
Qed.

End alternating_example.
