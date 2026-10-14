From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.
From GaussianAnalysis.probability Require Import commuting_operators.
From GaussianApplications.RandomSAT Require Import Model Pivotal Replacement.
From GaussianApplications.RandomSAT Require Import Survival Tails Interpolation.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: from auxiliary to proper clauses                           *)
(*                                                                            *)
(* Part of target T9 of phase 13. A Rocq formalization of the credited        *)
(* argument of the lemma 'Proper-clause transfer' (lem:proper-transfer) of 'A *)
(* Limiting Satisfiability Threshold for Every Fixed Clause Size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/convergence.tex), in the fixed-count form of the Lean      *)
(* development of the collection (lean/OAI/Probability/RandomSAT):            *)
(* Lean: properFraction (Transfer.lean, line 18)                              *)
(* Lean: auxiliaryProbability_le_proper (Transfer.lean, line 143)             *)
(* Lean: proper_scaled_le_auxiliaryProbability (Transfer.lean, line 150)      *)
(* Lean: properFraction_lower (Transfer.lean, line 201)                       *)
(* Lean: properFraction_pow_lower (Transfer.lean, line 279)                   *)
(* Lean: auxiliaryProbability_center_lower (Transfer.lean, line 297)          *)
(* Lean: auxiliaryProbability_center_upper (Transfer.lean, line 318)          *)
(*                                                                            *)
(* - prop_avg and sat_prob_iter: P_n(m) is the m-th iterate of the average    *)
(*   over one proper clause, at alive, started at the set of all assignments. *)
(* - distinct_frac n k = n^_k / n^k, the manuscript's theta, is the           *)
(*   probability that k independent uniform variables of 'I_n are distinct;   *)
(*   distinct_frac_lower: theta >= 1 - C(k, 2) / n.                           *)
(* - aux_le_prop and scaled_prop_le_aux: one auxiliary clause empties a set   *)
(*   at least as often as a proper clause, and theta times the proper average *)
(*   is at most the auxiliary one (aux_kill_le, from rep_count_mono, which    *)
(*   counts the tuples with a repetition).                                    *)
(* - aux_prob_le_sat_prob and scaled_sat_prob_le_aux: theta^m P_n(m) <=       *)
(*   aux_prob n k m <= P_n(m) for 0 < n and k <= n, by monotone_iter_le and   *)
(*   iter_scale of commuting_operators.v.                                     *)
(* - distinct_frac_pow_cap: theta^m >= sat_tfactor k = exp(-2 2^(k+1) C(k,    *)
(*   2)) for m <= sat_cap k n and 2 C(k, 2) <= n.                             *)
(* - aux_prob_center_lower and aux_prob_center_upper: the two tails of        *)
(*   Tails.v in the auxiliary model, with the lower bound sat_tfactor k / 2.  *)
(*                                                                            *)
(* Departure: the manuscript thins a Poisson family of auxiliary clauses into *)
(* the clauses with distinct variables and the others, which gives e^(-R) E   *)
(* P_n(J) <= s_n(c) <= E P_n(J); the Lean development and this file use the   *)
(* sandwich theta^m P_n(m) <= aux_prob n k m <= P_n(m) for a fixed number m   *)
(* of clauses.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section transfer.
Context {R : realType}.

(* The average over one uniform proper clause, as an average over random
   intersections. *)
Definition prop_avg n k :
    ({set {ffun 'I_n -> bool}} -> R) -> {set {ffun 'I_n -> bool}} -> R :=
  meet_avg (fun c : clause n k =>
    [set s : {ffun 'I_n -> bool} | clause_sat s c]).

Lemma prop_avgE n k (f : {set {ffun 'I_n -> bool}} -> R) S :
  @prop_avg n k f S = clause_avg k f S.
Proof.
apply: eq_unif_mean => c; congr f.
by apply/setP => s; rewrite !inE.
Qed.

Lemma restrict_bigcap n k (S : {set {ffun 'I_n -> bool}})
    (t : seq (clause n k)) :
  restrict S t =
    S :&: \bigcap_(c <- t) [set s : {ffun 'I_n -> bool} | clause_sat s c].
Proof.
elim: t S => [|c t IH] S /=; first by rewrite big_nil setIT.
by rewrite IH big_cons setIA; congr (_ :&: _); apply/setP => s; rewrite !inE.
Qed.

(* P_n(m) is the m-th iterate of the proper-clause average at the full
   solution set. *)
Lemma sat_prob_iter n k m :
  sat_prob R n k m = iter m (@prop_avg n k) alive [set: {ffun 'I_n -> bool}].
Proof.
rewrite sat_probE /survival /tuple_avg iter_meet_avg.
by apply: eq_unif_mean => t; rewrite restrict_bigcap.
Qed.

Lemma prop_avg_alive n k (S : {set {ffun 'I_n -> bool}}) : (k <= n)%N ->
  @prop_avg n k alive S = alive S * (1 - kfrac #|forced S| n k) :> R.
Proof.
move=> kn; have C0 := card_clause_gt0 kn.
case: (set_0Vmem S) => [->|[s0 s0S]].
  rewrite alive0 mul0r /prop_avg /meet_avg (eq_unif_mean (g := fun=> 0)).
    by move=> c; rewrite set0I alive0.
  by rewrite unif_mean_cst.
have S0 : S != set0 by apply/set0Pn; exists s0.
have aS : alive S = 1 :> R by rewrite /alive S0.
rewrite aS mul1r -(killE_forced R k S0) /kill unif_meanB unif_mean_cst //.
by rewrite aS opprB addrC subrK prop_avgE.
Qed.

(* One step: an auxiliary clause kills at least as often as a proper one. *)
Lemma aux_le_prop n k (S : {set {ffun 'I_n -> bool}}) :
  (0 < n)%N -> (k <= n)%N ->
  @aux_avg R n k alive S <= @prop_avg n k alive S :> R.
Proof.
move=> n0 kn; rewrite /aux_avg emb_avg_alive // prop_avg_alive //.
have -> : emb_forced S id = forced S by apply/setP => i; rewrite [in LHS]inE.
apply: ler_wpM2l; first exact: alive_ge0.
rewrite lerB //; apply: kfrac_le_pow => //.
by rewrite -[n in (_ <= n)%N]card_ord max_card.
Qed.

(* The probability that k independent uniform variables of 'I_n are
   distinct. *)
Definition distinct_frac n k : R := (n ^_ k)%:R / n%:R ^+ k.

Lemma distinct_frac_ge0 n k : 0 <= distinct_frac n k.
Proof. by rewrite /distinct_frac divr_ge0 ?exprn_ge0 ?ler0n. Qed.

(* The number of k-tuples of 'I_b with a repetition is nondecreasing in b. *)
Lemma rep_count_mono b n k : (b <= n)%N -> (b ^ k - b ^_ k <= n ^ k - n ^_ k)%N.
Proof.
move=> bn.
have cnt (T : finType) :
    #|[set t : k.-tuple T | ~~ uniq t]| = (#|T| ^ k - #|T| ^_ k)%N.
  have h := cardsC [set t : k.-tuple T | uniq t].
  have hu : #|[set t : k.-tuple T | uniq t]| = (#|T| ^_ k)%N.
    transitivity #|[set t : k.-tuple T | all predT t & uniq t]|.
      by apply: eq_card => t; rewrite !inE all_predT.
    exact: card_uniq_tuples.
  rewrite hu card_tuple in h.
  by rewrite -h addKn; apply: eq_card => t; rewrite !inE.
have := cnt 'I_b; have := cnt 'I_n; rewrite !card_ord => <- <-.
pose f (t : k.-tuple 'I_b) : k.-tuple 'I_n := map_tuple (widen_ord bn) t.
have winj : injective (widen_ord bn) by move=> x y /(congr1 val) /= /val_inj.
have finj : injective f.
  by move=> t1 t2 /(congr1 val) /= /(inj_map winj) /val_inj.
rewrite -(card_imset _ finj); apply: subset_leq_card.
apply/subsetP => _ /imsetP [t ht ->].
by rewrite !inE (map_inj_uniq winj) in ht *.
Qed.

Lemma distinct_frac_kfrac n b k : (k <= n)%N ->
  distinct_frac n k * kfrac b n k = (b ^_ k)%:R / (2 ^+ k * n%:R ^+ k) :> R.
Proof.
move=> kn; rewrite /distinct_frac /kfrac -!bin_ffact !natrM.
have c0 : ('C(n, k)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n bin_gt0.
have f0 : (k`!%:R : R) != 0 by rewrite pnatr_eq0 -lt0n fact_gt0.
have t0 : (2 ^+ k : R) != 0 by rewrite expf_neq0 // pnatr_eq0.
have nk0 : (n%:R ^+ k : R) != 0.
  case: n kn c0 => [|n] kn c0; last by rewrite expf_neq0 // pnatr_eq0.
  by move: kn; rewrite leqn0 => /eqP ->; rewrite expr0 oner_eq0.
by field.
Qed.

Lemma ffact_le_expn n k : (n ^_ k <= n ^ k)%N.
Proof.
elim: k => [|k IH]; first by rewrite ffactn0 expn0.
by rewrite ffactnSr expnSr leq_mul // leq_subr.
Qed.

(* An auxiliary clause kills less often than a proper clause scaled by the
   probability theta that its variables are distinct. *)
Lemma aux_kill_le n b k : (b <= n)%N -> (k <= n)%N -> (0 < n)%N ->
  (b%:R / (2 * n%:R)) ^+ k <=
    1 - distinct_frac n k + distinct_frac n k * kfrac b n k :> R.
Proof.
move=> bn kn n0; rewrite distinct_frac_kfrac //.
have rep := rep_count_mono k bn.
have hb := ffact_le_expn b k; have hn := ffact_le_expn n k.
have rep' : (b%:R ^+ k - (b ^_ k)%:R <= n%:R ^+ k - (n ^_ k)%:R :> R).
  by rewrite -!natrX -!natrB // ler_nat.
have t1 : (1 <= 2 ^+ k :> R) by rewrite exprn_ege1 // ler1n.
have nk0 : (0 < n%:R ^+ k :> R) by rewrite exprn_gt0 // ltr0n.
have d0 : 0 <= n%:R ^+ k - (n ^_ k)%:R :> R.
  by rewrite -natrX -natrB // ler0n.
rewrite /distinct_frac expr_div_n exprMn.
set N := n%:R ^+ k : R; set F := (n ^_ k)%:R : R.
set B := b%:R ^+ k : R; set G := (b ^_ k)%:R : R; set T := 2 ^+ k : R.
have key : B - G <= T * (N - F) by apply: le_trans rep' _; rewrite ler_peMl.
have T0 : 0 < T by apply: lt_le_trans ltr01 t1.
have e : 1 - F / N + G / (T * N) - B / (T * N) =
    (T * (N - F) - (B - G)) / (T * N).
  have Tn : T != 0 by rewrite gt_eqF.
  have Nn : N != 0 by rewrite gt_eqF.
  by field.
by rewrite -subr_ge0 e divr_ge0 ?subr_ge0 // mulr_ge0 // ltW.
Qed.

(* One step the other way: theta times a proper clause average is below the
   auxiliary one. *)
Lemma scaled_prop_le_aux n k (S : {set {ffun 'I_n -> bool}}) :
  (0 < n)%N -> (k <= n)%N ->
  distinct_frac n k * @prop_avg n k alive S <= @aux_avg R n k alive S.
Proof.
move=> n0 kn; rewrite /aux_avg emb_avg_alive // prop_avg_alive //.
have -> : emb_forced S id = forced S by apply/setP => i; rewrite [in LHS]inE.
have bn : (#|forced S| <= n)%N by rewrite -[n in (_ <= n)%N]card_ord max_card.
have h := aux_kill_le bn kn n0.
rewrite mulrCA; apply: ler_wpM2l; first exact: alive_ge0.
by move: h; lra.
Qed.

(* m auxiliary clauses are satisfiable less often than m proper ones. *)
Lemma aux_prob_le_sat_prob n k m : (0 < n)%N -> (k <= n)%N ->
  aux_prob n k m <= sat_prob R n k m.
Proof.
move=> n0 kn; rewrite sat_prob_iter /aux_prob.
apply: (monotone_iter_le (meet_avg_monotone _) (meet_avg_monotone _)).
  by move=> g x; rewrite /aux_avg /emb_avg /prop_avg meet_avgC.
by move=> S; exact: aux_le_prop.
Qed.

(* ... and more often than theta^m times m proper ones. *)
Lemma scaled_sat_prob_le_aux n k m : (0 < n)%N -> (k <= n)%N ->
  distinct_frac n k ^+ m * sat_prob R n k m <= aux_prob n k m.
Proof.
move=> n0 kn; rewrite sat_prob_iter /aux_prob.
have hl := meet_avg_linear (R := R)
  (fun c : clause n k => [set s : {ffun 'I_n -> bool} | clause_sat s c]).
rewrite -(iter_scale (distinct_frac n k) hl).
apply: (monotone_iter_le (meet_avg_monotone _)).
- move=> f g fg x; apply: ler_wpM2l; first exact: distinct_frac_ge0.
  by apply: meet_avg_monotone.
- move=> g x; have [_ hZ] := meet_avg_linear (R := R)
    (fun C : aux_clause n k => aux_sat id C).
  rewrite (hZ (distinct_frac n k)
    (meet_avg (fun c : clause n k => [set s | clause_sat s c]) g)).
  by rewrite meet_avgC.
- by move=> S; exact: scaled_prop_le_aux.
Qed.

Lemma distinct_frac_le1 n k : (0 < n)%N -> distinct_frac n k <= 1.
Proof.
move=> n0; rewrite /distinct_frac ler_pdivrMr ?exprn_gt0 ?ltr0n // mul1r.
by rewrite -natrX ler_nat ffact_le_expn.
Qed.

(* The birthday bound: k uniform variables are distinct with probability at
   least 1 - C(k, 2) / n. *)
Lemma distinct_frac_lower n k : (0 < n)%N -> (k <= n)%N ->
  1 - 'C(k, 2)%:R / n%:R <= distinct_frac n k.
Proof.
move=> n0; have n0' : 0 < n%:R :> R by rewrite ltr0n.
elim: k => [|k IH] kn.
  by rewrite bin0n /distinct_frac ffactn0 expr0 divr1 mul0r subr0.
have kn' : (k <= n)%N := ltnW kn.
have hS : distinct_frac n k.+1 = distinct_frac n k * (1 - k%:R / n%:R).
  rewrite /distinct_frac ffactnSr natrM natrB // exprSr.
  have nn : n%:R != 0 :> R by rewrite gt_eqF.
  have nk : n%:R ^+ k != 0 :> R by rewrite expf_neq0.
  by field.
rewrite hS binS bin1 natrD mulrDl.
have h1 := distinct_frac_le1 k n0.
have hk : 0 <= k%:R / n%:R :> R by rewrite divr_ge0 ?ler0n.
by have := IH kn'; nra.
Qed.

Lemma expR_neg2_le (x : R) : 0 <= x -> x <= 2^-1 -> expR (- (2 * x)) <= 1 - x.
Proof.
move=> x0 x1; rewrite expRN; have e0 := expR_gt0 (2 * x).
rewrite -[X in X <= _]mul1r ler_pdivrMr //.
apply: le_trans (_ : 1 <= (1 - x) * (1 + 2 * x)) _; first by nra.
by rewrite ler_wpM2l ?subr_ge0 ?expR_ge1Dx //; apply: le_trans x1 _; lra.
Qed.

(* theta^m is bounded below uniformly for m <= L n. *)
Lemma distinct_frac_pow_lower n k m (L : R) : (0 < n)%N -> (k <= n)%N ->
  2 * 'C(k, 2)%:R <= n%:R :> R -> m%:R <= L * n%:R ->
  expR (- (2 * L * 'C(k, 2)%:R)) <= distinct_frac n k ^+ m.
Proof.
move=> n0 kn hk hm; have n0' : 0 < n%:R :> R by rewrite ltr0n.
set x : R := 'C(k, 2)%:R / n%:R.
have x0 : 0 <= x by rewrite divr_ge0 ?ler0n.
have x1 : x <= 2^-1 by rewrite /x ler_pdivrMr //; move: hk; lra.
have hb : expR (- (2 * x)) <= distinct_frac n k :=
  le_trans (expR_neg2_le x0 x1) (distinct_frac_lower n0 kn).
apply: le_trans (lerXn2r _ _ _ hb);
  rewrite ?nnegrE ?expR_ge0 ?distinct_frac_ge0 //.
rewrite -expRM_natr ler_expR.
rewrite mulNr lerN2 /x -!mulrA ler_pM2l // [L * _]mulrC.
apply: ler_wpM2l; first by rewrite ler0n.
by rewrite mulrC ler_pdivrMr.
Qed.

End transfer.

Section transfer_center.
Context {R : realType}.

(* The transfer factor exp(-2 2^(k+1) C(k, 2)), a lower bound for theta^m
   below the cap. *)
Definition sat_tfactor (k : nat) : R :=
  expR (- (2 * 2 ^+ k.+1 * 'C(k, 2)%:R)).

Lemma sat_tfactor_gt0 k : 0 < sat_tfactor k.
Proof. exact: expR_gt0. Qed.

Lemma distinct_frac_pow_cap n k m : (0 < n)%N -> (k <= n)%N ->
  2 * 'C(k, 2)%:R <= n%:R :> R -> (m <= sat_cap k n)%N ->
  sat_tfactor k <= distinct_frac n k ^+ m.
Proof.
move=> n0 kn hk hm; apply: distinct_frac_pow_lower => //.
by rewrite -(ler_nat R) /sat_cap natrM natrX in hm.
Qed.

(* The lower tail in the auxiliary model: at least the window below n times
   the center, aux_n(m) is at least half the transfer factor. *)
Lemma aux_prob_center_lower n k m : (3 <= k)%N -> (k.+1 <= n)%N ->
  2 * 'C(k, 2)%:R <= n%:R :> R -> sat_err n k <= 2^-1 :> R ->
  m%:R + sat_window n k <= n%:R * sat_center n k :> R ->
  sat_tfactor k / 2 <= aux_prob n k m :> R.
Proof.
move=> k3 kn hk he hm; have kn' : (k <= n)%N := ltnW kn.
have n0 : (0 < n)%N by apply: leq_trans kn.
have mM : (m <= sat_cap k n)%N.
  rewrite -(ler_nat R); apply: le_trans (sat_mean_le_cap n k).
  rewrite -sat_center_mul //; apply: le_trans hm.
  by rewrite lerDl ltW // sat_window_gt0.
have hp := sat_prob_center_lower k3 kn hm.
have ht := distinct_frac_pow_cap n0 kn' hk mM.
apply: le_trans (scaled_sat_prob_le_aux m n0 kn').
apply: ler_pM; first exact: ltW (sat_tfactor_gt0 k).
- by rewrite invr_ge0 ler0n.
- exact: ht.
- by move: hp he; lra.
Qed.

(* The upper tail in the auxiliary model. *)
Lemma aux_prob_center_upper n k m : (3 <= k)%N -> (k.+1 <= n)%N ->
  (m <= sat_cap k n)%N ->
  n%:R * sat_center n k + sat_window n k <= m%:R :> R ->
  aux_prob n k m <= sat_err n k :> R.
Proof.
move=> k3 kn mM hm; have n0 : (0 < n)%N by apply: leq_trans kn.
apply: le_trans (aux_prob_le_sat_prob m n0 (ltnW kn)) _.
exact: sat_prob_center_upper.
Qed.

End transfer_center.
