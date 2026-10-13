From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import functions interval reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.random_matrix Require Import goe goe_rotation goe_edge.
From GaussianAnalysis.random_matrix Require Import goe_entries.
From GaussianApplications Require Import SKGapDefinitions.

(**md**************************************************************************)
(* # The good disorder of the SK model                                        *)
(*                                                                            *)
(* Part of target T4 of phase 12 (AGENTS.md, section Phase 12), the spectral  *)
(* gap of the heat-bath dynamics of the Sherrington-Kirkpatrick model for     *)
(* beta < 1/2. A Rocq formalization of the credited argument of the           *)
(* proposition 'Good disorder' (rcut:prop:good-disorder) of 'Cutoff           *)
(* throughout the high-temperature Sherrington-Kirkpatrick phase' (family 227 *)
(* of the OpenAI math collection, revision 1581d4cbd, file                    *)
(* appendices/entropy.tex). It follows the TeX, not a Lean module of the      *)
(* collection.                                                                *)
(*                                                                            *)
(* For beta >= 0, delta > 0 and the coupling J = sk_coupling beta a of        *)
(* SKGapDefinitions.v, sk_good_disorder n beta delta is the set of the a of   *)
(* 'rV[R]_(n * n) such that                                                   *)
(*   opnorm J <= 2 beta + delta,                                              *)
(*   sum_j J_ij^2 <= beta^2 + delta for every i,                              *)
(*   |J_ij| <= delta for every i and j.                                       *)
(* It is measurable (sk_good_disorder_measurable), and its probability under  *)
(* gauss (n * n) tends to one (sk_good_disorder_prob). R is implicit in the   *)
(* three; their other arguments are explicit.                                 *)
(*                                                                            *)
(* The proof is the manuscript's. If beta = 0, then J = 0 and the event is    *)
(* the whole space. If beta > 0, then J = beta (W - Diag W) with              *)
(* W = goe_mx a, and the event holds outside four failure events of           *)
(* random_matrix/goe_entries.v and random_matrix/goe_edge.v, where            *)
(* t = delta / (2 beta), u = delta / beta^2 and s = delta / beta:             *)
(* - opnorm W >= 2 + t, of probability at most 2 exp (- n t^2 / 4) by the     *)
(*   sharp edge goe_opnorm_edge_tail. Outside it, and when the diagonal of W  *)
(*   is at most t, opnorm J <= beta (opnorm W + t) <= 2 beta + delta          *)
(*   (sk_coupling_opnorm_le);                                                 *)
(* - |W_ii| >= t for some i, of probability at most 2 n exp (- n t^2 / 4), by *)
(*   Gaussian tails and a union bound;                                        *)
(* - sum_(j != i) W_ij^2 >= 1 + u for some i, of probability at most          *)
(*   n exp (- n u^2 / (4 (1 + u))), by the tail of a chi-square with n - 1    *)
(*   degrees of freedom and a union bound;                                    *)
(* - |W_ij| >= s for some i != j, of probability at most                      *)
(*   2 n^2 exp (- n s^2 / 2), by Gaussian tails and a union bound.            *)
(*                                                                            *)
(* As n^k exp (- n c) <= 6 / (c^3 n) for c > 0, k <= 2 and n >= 1             *)
(* (exprn_expRN_le of random_matrix/goe_entries.v), the four probabilities    *)
(* sum to at most K / n, with K depending only on beta and delta.             *)
(*                                                                            *)
(* The manuscript lets delta = n^(-1/4) tend to zero. Here delta > 0 is       *)
(* fixed, which is what the assembly of T4 uses, and no rate is needed. The   *)
(* manuscript's consequence for the cubic row sums is not part of this file.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sk_good_disorder.
Context {R : realType}.

(* The good-disorder event, for a fixed delta. *)
Definition sk_good_disorder n (beta delta : R) : set 'rV[R]_(n * n) :=
  [set a | [/\ opnorm (sk_coupling beta a) <= 2 * beta + delta,
     forall i, \sum_j sk_coupling beta a i j ^+ 2 <= beta ^+ 2 + delta &
     forall i j, `|sk_coupling beta a i j| <= delta]].
Arguments sk_good_disorder : clear implicits.

(* The coupling is zero on the diagonal and beta W_ij outside. *)
Lemma sk_couplingE n (beta : R) (a : 'rV[R]_(n * n)) i j :
  sk_coupling beta a i j = if i == j then 0 else beta * goe_mx a i j.
Proof.
rewrite /sk_coupling; move: (goe_mx a) => W.
rewrite !mxE; case: eqP => [->|_]; first by rewrite mulr1n subrr mulr0.
by rewrite mulr0n subr0.
Qed.

(* Removing the diagonal of W costs at most a bound of its entries. *)
Lemma sk_coupling_opnorm_le n (beta : R) (a : 'rV[R]_(n * n)) (s : R) :
  0 <= beta -> 0 <= s -> (forall i, `|goe_mx a i i| <= s) ->
  opnorm (sk_coupling beta a) <= beta * (opnorm (goe_mx a) + s).
Proof.
move=> b0 s0 hs; rewrite /sk_coupling opnormZ ger0_norm //.
by apply: ler_wpM2l => //; exact: opnorm_sub_diag_le.
Qed.

(* The row sums of squares of J are beta^2 times those of W outside the
   diagonal. *)
Lemma sk_coupling_row n (beta : R) (a : 'rV[R]_(n * n)) i :
  \sum_j sk_coupling beta a i j ^+ 2 =
  beta ^+ 2 * \sum_(j | j != i) goe_mx a i j ^+ 2.
Proof.
rewrite (bigID (fun j => j == i)) /= big1 => [j /eqP ->|].
  by rewrite sk_couplingE eqxx expr0n.
rewrite add0r mulr_sumr; apply: eq_bigr => j ji.
by rewrite sk_couplingE eq_sym (negbTE ji) exprMn.
Qed.

Lemma sk_couplingB n (beta : R) (a b : 'rV[R]_(n * n)) :
  sk_coupling beta (a - b) = sk_coupling beta a - sk_coupling beta b.
Proof.
rewrite /sk_coupling goe_mxB; move: (goe_mx a) (goe_mx b) => A B.
apply/matrixP => i j; rewrite !mxE.
by case: eqP => _; rewrite ?mulr1n ?mulr0n; ring.
Qed.

Lemma frobenius_sk_coupling_le n (beta : R) (a : 'rV[R]_(n * n)) :
  frobenius (sk_coupling beta a) <= `|beta| * frobenius (goe_mx a).
Proof.
rewrite -ler_sqr ?nnegrE ?frobenius_ge0 ?mulr_ge0 ?frobenius_ge0 //.
rewrite exprMn real_normK ?num_real // !frobenius_sqr /mxdot mulr_sumr.
apply: ler_sum => i _; rewrite mulr_sumr; apply: ler_sum => j _.
rewrite sk_couplingE; case: eqP => _.
  by rewrite mul0r mulr_ge0 ?sqr_ge0 // -expr2 sqr_ge0.
by rewrite -!expr2 exprMn.
Qed.

(* a |-> opnorm J is Lipschitz, hence measurable. *)
Lemma measurable_sk_coupling_opnorm n (beta : R) :
  measurable_fun [set: 'rV[R]_(n * n)] (fun a => opnorm (sk_coupling beta a)).
Proof.
have L (a b : 'rV[R]_(n * n)) :
    `|opnorm (sk_coupling beta a) - opnorm (sk_coupling beta b)| <=
    `|beta| * Num.sqrt (2 / n%:R) * frobenius (a - b).
  have h1 : `|opnorm (sk_coupling beta a) - opnorm (sk_coupling beta b)| <=
      opnorm (sk_coupling beta (a - b)).
    rewrite sk_couplingB.
    move: (sk_coupling beta a) (sk_coupling beta b) => A B.
    have hA := opnormD B (A - B); rewrite addrC subrK in hA.
    have hB := opnormD A (B - A); rewrite addrC subrK -opprB opnormN in hB.
    by rewrite ler_norml; apply/andP; split; lra.
  apply: le_trans h1 _; apply: le_trans (opnorm_le_frobenius _) _.
  apply: le_trans (frobenius_sk_coupling_le _ _) _.
  by rewrite -mulrA; apply: ler_wpM2l => //; exact: frobenius_goe_mx.
exact: continuous_measurable_mx (lipschitz_frobenius_continuous L).
Qed.

Lemma sk_good_disorder_measurable n (beta delta : R) :
  measurable (sk_good_disorder n beta delta).
Proof.
have mI (F : 'rV[R]_(n * n) -> R) (c : R) : measurable_fun setT F ->
    measurable [set a | F a <= c].
  move=> mF; have -> : [set a | F a <= c] = F @^-1` `]-oo, c]%classic.
    by apply/seteqP; split => a; rewrite /= in_itv.
  by rewrite -[X in measurable X]setTI; exact: mF.
have mJ i j :
    measurable_fun setT (fun a : 'rV[R]_(n * n) => sk_coupling beta a i j).
  under eq_fun do rewrite sk_couplingE.
  case: eqP => _; first exact: measurable_cst.
  apply: measurable_funM => //.
  apply: measurableT_comp (measurable_mxentry i j) _.
  exact: measurable_goe_mx.
have -> : sk_good_disorder n beta delta =
    [set a | opnorm (sk_coupling beta a) <= 2 * beta + delta] `&`
    (\bigcap_i
       [set a | \sum_j sk_coupling beta a i j ^+ 2 <= beta ^+ 2 + delta]) `&`
    (\bigcap_i \bigcap_j [set a | `|sk_coupling beta a i j| <= delta]).
  apply/seteqP; split => a.
    move=> [h1 h2 h3]; split; first split => //.
      by move=> i _; exact: h2.
    by move=> i _ j _; exact: h3.
  case=> [[h1 h2] h3]; split => // [i|i j].
    by apply: h2.
  by apply: (h3 i) => //.
apply: measurableI; first apply: measurableI.
- by apply: mI; exact: measurable_sk_coupling_opnorm.
- apply: fin_bigcap_measurable => [|i _].
    exact: cardinality.finite_finset.
  apply: mI; apply: measurable_sum => j; apply: measurable_funX; exact: mJ.
- apply: fin_bigcap_measurable => [|i _].
    exact: cardinality.finite_finset.
  apply: fin_bigcap_measurable => [|j _].
    exact: cardinality.finite_finset.
  by apply: mI; apply: measurableT_comp (mJ i j); exact: normr_measurable.
Qed.

(* The probability of the good disorder tends to one: the four failure
   events of the header have probabilities summing to at most K / n. *)
Lemma sk_good_disorder_prob (beta delta : R) : 0 <= beta -> 0 < delta ->
  forall eps : R, 0 < eps -> exists N : nat, forall n, (N <= n)%N ->
  ((1 - eps)%:E <= gauss (n * n) (sk_good_disorder n beta delta))%E.
Proof.
move=> b0 d0 eps e0.
have [beta0|bn0] := eqVneq beta 0.
  exists 0%N => n _.
  have -> : sk_good_disorder n beta delta = setT.
    apply/seteqP; split; first exact: subsetT.
    move=> a _; split.
    - by rewrite /sk_coupling beta0 scale0r opnorm0 mulr0 add0r ltW.
    - by move=> i; rewrite sk_coupling_row beta0 expr2 !mul0r add0r ltW.
    - by move=> i j; rewrite sk_couplingE beta0 mul0r if_same normr0 ltW.
  by rewrite probability_setT lee_fin lerBlDr lerDl ltW.
have bp : 0 < beta by rewrite lt_def bn0 b0.
have [t t0 bt] : exists2 t : R, 0 < t & 2 * beta * t = delta.
  by exists (delta / (2 * beta)); [rewrite divr_gt0 // mulr_gt0 | field].
have [u u0 bu] : exists2 u : R, 0 < u & beta ^+ 2 * u = delta.
  by exists (delta / beta ^+ 2); [rewrite divr_gt0 // exprn_gt0 | field].
have [s s0 bs] : exists2 s : R, 0 < s & beta * s = delta.
  by exists (delta / beta); [rewrite divr_gt0 | field].
have c10 : 0 < t ^+ 2 / 4 by rewrite divr_gt0 // exprn_gt0.
have c20 : 0 < u ^+ 2 / (4 * (1 + u)).
  by rewrite divr_gt0 ?exprn_gt0 // mulr_gt0 // addr_gt0.
have c30 : 0 < s ^+ 2 / 2 by rewrite divr_gt0 // exprn_gt0.
have [K K0 hK] : exists2 K : R, 0 <= K & forall n : nat, (0 < n)%N ->
    2 * expR (- (n%:R * t ^+ 2 / 4)) +
    2 * n%:R * expR (- (n%:R * t ^+ 2 / 4)) +
    n%:R * expR (- (n%:R * u ^+ 2 / (4 * (1 + u)))) +
    2 * n%:R ^+ 2 * expR (- (n%:R * s ^+ 2 / 2)) <= K / n%:R.
  exists (12 / (t ^+ 2 / 4) ^+ 3 + 12 / (t ^+ 2 / 4) ^+ 3 +
    6 / (u ^+ 2 / (4 * (1 + u))) ^+ 3 + 12 / (s ^+ 2 / 2) ^+ 3).
    by rewrite !addr_ge0 // divr_ge0 // exprn_ge0 // ltW.
  move=> n n0; have n1 : 1 <= n%:R :> R by rewrite ler1n.
  have A0 : expR (- (n%:R * t ^+ 2 / 4)) <= 6 / (t ^+ 2 / 4) ^+ 3 / n%:R.
    rewrite -[n%:R * t ^+ 2 / 4]mulrA.
    by have := exprn_expRN_le (k := 0) c10 n1 isT; rewrite expr0 mul1r.
  have A1 : n%:R * expR (- (n%:R * t ^+ 2 / 4)) <=
      6 / (t ^+ 2 / 4) ^+ 3 / n%:R.
    rewrite -[n%:R * t ^+ 2 / 4]mulrA.
    by have := exprn_expRN_le (k := 1) c10 n1 isT; rewrite expr1.
  have A2 : n%:R * expR (- (n%:R * u ^+ 2 / (4 * (1 + u)))) <=
      6 / (u ^+ 2 / (4 * (1 + u))) ^+ 3 / n%:R.
    rewrite -[n%:R * u ^+ 2 / _]mulrA.
    by have := exprn_expRN_le (k := 1) c20 n1 isT; rewrite expr1.
  have A3 : n%:R ^+ 2 * expR (- (n%:R * s ^+ 2 / 2)) <=
      6 / (s ^+ 2 / 2) ^+ 3 / n%:R.
    rewrite -[n%:R * s ^+ 2 / 2]mulrA.
    exact: (exprn_expRN_le (k := 2) c30 n1 isT).
  lra.
have [N NK] : exists N : nat, forall n : nat, (N <= n)%N ->
    (0 < n)%N /\ K / n%:R <= eps.
  exists (truncn (K / eps)).+1 => n Nn.
  have n0 : (0 < n)%N := leq_trans (ltn0Sn _) Nn.
  split => //.
  have h1 : K / eps < n%:R.
    by apply: lt_le_trans (truncnS_gt _) _; rewrite ler_nat.
  have n0' : 0 < n%:R :> R by rewrite ltr0n.
  move: h1; rewrite ltr_pdivrMr // ler_pdivrMr // => h1.
  lra.
exists N => n /NK [n0 nK].
have e1 : beta * (2 + t + t) = 2 * beta + delta by rewrite -bt; ring.
have sub : ~` sk_good_disorder n beta delta `<=`
    [set a : 'rV[R]_(n * n) | 2 + t <= opnorm (goe_mx a)]%R `|`
    [set a | exists i, t <= `|goe_mx a i i|]%R `|`
    [set a | exists i, 1 + u <= \sum_(j | j != i) goe_mx a i j ^+ 2]%R `|`
    [set a | exists i j, i != j /\ s <= `|goe_mx a i j|]%R.
  move=> a Ea; apply: contrapT => nF; apply: Ea.
  move/not_orP: nF => [/not_orP[/not_orP[h1 h2] h3] h4].
  have o1 : opnorm (goe_mx a) <= 2 + t.
    by apply/ltW; rewrite ltNge; apply/negP.
  have o2 i : `|goe_mx a i i| <= t.
    by apply/ltW; rewrite ltNge; apply/negP => h; apply: h2; exists i.
  have o3 i : \sum_(j | j != i) goe_mx a i j ^+ 2 <= 1 + u.
    by apply/ltW; rewrite ltNge; apply/negP => h; apply: h3; exists i.
  have o4 i j : i != j -> `|goe_mx a i j| <= s.
    move=> ij; apply/ltW; rewrite ltNge; apply/negP => h.
    by apply: h4; exists i, j.
  split.
  - apply: le_trans (sk_coupling_opnorm_le b0 (ltW t0) o2) _.
    rewrite -e1; apply: ler_wpM2l => //.
    by rewrite lerD2r.
  - move=> i; rewrite sk_coupling_row.
    apply: le_trans (ler_wpM2l (sqr_ge0 beta) (o3 i)) _.
    by rewrite -bu mulrDr mulr1.
  - move=> i j; rewrite sk_couplingE; case: eqP => [_|/eqP ij].
      by rewrite normr0 ltW.
    rewrite normrM ger0_norm // -bs.
    by apply: ler_wpM2l => //; exact: o4.
have mE : measurable (sk_good_disorder n beta delta).
  exact: sk_good_disorder_measurable.
have mF1 := measurable_goe_opnorm_ge (d := n) (2 + t).
have mF2 := measurable_goe_diag_max (d := n) t.
have mF3 := measurable_goe_row_max (d := n) (1 + u).
have mF4 := measurable_goe_offdiag_max (d := n) s.
have := probability_setC (gauss (n * n)) (measurableC mE).
rewrite setCK => ->.
rewrite EFinB; apply: leeB => //.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE.
- exact: measurableC.
- by apply: measurableU => //; apply: measurableU => //; exact: measurableU.
apply: le_trans (measureU2 _ _ mF4) _.
  by apply: measurableU => //; exact: measurableU.
have mF12 := measurableU _ _ mF1 mF2.
apply: le_trans (leeD (measureU2 _ mF12 mF3) (lexx _)) _.
apply: le_trans (leeD (leeD (measureU2 _ mF1 mF2) (lexx _)) (lexx _)) _.
have T1 := goe_opnorm_edge_tail n0 (ltW t0).
have T2 := goe_mx_diag_max_tail n (ltW t0).
have T3 := goe_mx_row_max_tail n u0.
have T4 := goe_mx_offdiag_max_tail n (ltW s0).
apply: le_trans (leeD (leeD (leeD T1 T2) T3) T4) _.
rewrite -!EFinD lee_fin.
exact: le_trans (hK n n0) nK.
Qed.

End sk_good_disorder.

Arguments sk_good_disorder {R} n beta delta.
Arguments sk_good_disorder_measurable {R} n beta delta.
Arguments sk_good_disorder_prob {R} beta delta _ _ eps _.
