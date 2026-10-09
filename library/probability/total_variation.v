From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # The total variation distance                                             *)
(*                                                                            *)
(* The total variation distance of two probabilities on a measurable type is  *)
(* the supremum of |P A - Q A| over the measurable sets A. It is a real       *)
(* number in [0, 1], since probabilities are finite.                          *)
(*                                                                            *)
(* ```                                                                        *)
(*   tv_dist P Q == sup {|P A - Q A| : A measurable}, a real number           *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - tv_dist_ge, tv_dist_geE, tv_dist_le: |P A - Q A| <= tv_dist P Q for     *)
(*   every measurable A (as reals and as extended reals), and tv_dist P Q is  *)
(*   the least such bound; tv_distE: as an extended real it is the            *)
(*   ereal_sup of the |P A - Q A|;                                            *)
(* - tv_dist_ge0, tv_dist_le1, tv_distC, tv_dist_triangle, tv_dist_eq0,      *)
(*   tv_distxx: a pseudometric with values in [0, 1], zero for laws that      *)
(*   agree on the measurable sets;                                            *)
(* - tuple_prod_tv: for laws mu i and nu i on T and every measurable set A of *)
(*   n-tuples, |tuple_prod mu n A - tuple_prod nu n A| is at most the sum of  *)
(*   the tv_dist (mu i) (nu i), i < n (the hybrid argument of                 *)
(*   lindeberg_replacement with the indicator of A);                          *)
(* - one_sub_le_expR, expR_le_one_sub, pow_one_sub_bounds: for 0 <= x < n,    *)
(*   exp (- x n / (n - x)) <= (1 - x / n)^n <= exp (- x);                    *)
(*   pow_one_sub_dist: |(1 - x / n)^n - exp (- x)| <= x^2 / (n - x);          *)
(*   pow_one_sub_cvg: (1 - x / n)^n tends to exp (- x) for every x >= 0.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section total_variation.
Context d (T : measurableType d) (R : realType).
Implicit Types P Q S : probability T R.

Definition tv_dist P Q : R :=
  sup [set `|fine (P A) - fine (Q A)| | A in measurable].

Lemma prob_fine_itv P (A : set T) : measurable A -> 0 <= fine (P A) <= 1.
Proof.
move=> mA; rewrite fine_ge0 ?measure_ge0 //=.
have : (P A <= 1)%E by exact: probability_le1.
have fA : P A \is a fin_num by exact: fin_num_measure.
by rewrite -(fineK fA) lee_fin.
Qed.

Lemma prob_fineB_le1 P Q (A : set T) : measurable A ->
  `|fine (P A) - fine (Q A)| <= 1.
Proof.
move=> mA; have /andP[p0 p1] := prob_fine_itv P mA.
have /andP[q0 q1] := prob_fine_itv Q mA.
by rewrite ler_norml; apply/andP; split; lra.
Qed.

Let tv_ub P Q :
  has_ubound [set `|fine (P A) - fine (Q A)| | A in measurable].
Proof. by exists 1 => _ [A mA <-]; exact: prob_fineB_le1. Qed.

Let tv_ne P Q :
  [set `|fine (P A) - fine (Q A)| | A in measurable] !=set0.
Proof. by exists `|fine (P set0) - fine (Q set0)|, set0. Qed.

Lemma tv_dist_ge P Q (A : set T) : measurable A ->
  `|fine (P A) - fine (Q A)| <= tv_dist P Q.
Proof. by move=> mA; apply: sup_ubound; [exact: tv_ub | exists A]. Qed.

Lemma tv_dist_geE P Q (A : set T) : measurable A ->
  (`|P A - Q A| <= (tv_dist P Q)%:E)%E.
Proof.
move=> mA.
have fP : P A \is a fin_num by exact: fin_num_measure.
have fQ : Q A \is a fin_num by exact: fin_num_measure.
by rewrite -(fineK fP) -(fineK fQ) -EFinB abse_EFin lee_fin tv_dist_ge.
Qed.

Lemma tv_dist_le P Q (c : R) :
  (forall A, measurable A -> `|fine (P A) - fine (Q A)| <= c) ->
  tv_dist P Q <= c.
Proof. by move=> h; apply: sup_le_ub; [exact: tv_ne | move=> _ [A mA <-]; exact: h]. Qed.

Lemma tv_dist_ge0 P Q : 0 <= tv_dist P Q.
Proof. by apply: le_trans (tv_dist_ge P Q measurable0); exact: normr_ge0. Qed.

Lemma tv_dist_le1 P Q : tv_dist P Q <= 1.
Proof. by apply: tv_dist_le => A mA; exact: prob_fineB_le1. Qed.

Lemma tv_distC P Q : tv_dist P Q = tv_dist Q P.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; apply: tv_dist_le => A mA;
  by rewrite distrC; exact: tv_dist_ge.
Qed.

Lemma tv_dist_triangle P Q S : tv_dist P S <= tv_dist P Q + tv_dist Q S.
Proof.
apply: tv_dist_le => A mA.
apply: le_trans (ler_distD (fine (Q A)) _ _) _.
by apply: lerD; exact: tv_dist_ge.
Qed.

Lemma tv_dist_eq0 P Q : (forall A, measurable A -> P A = Q A) ->
  tv_dist P Q = 0.
Proof.
move=> h; apply/eqP; rewrite eq_le tv_dist_ge0 andbT.
by apply: tv_dist_le => A mA; rewrite h // subrr normr0.
Qed.

Lemma tv_distxx P : tv_dist P P = 0.
Proof. exact: tv_dist_eq0. Qed.

Lemma tv_distE P Q :
  (tv_dist P Q)%:E = ereal_sup [set (`|P A - Q A|)%E | A in measurable].
Proof.
have -> : [set (`|P A - Q A|)%E | A in measurable] =
    EFin @` [set `|fine (P A) - fine (Q A)| | A in measurable].
  apply/seteqP; split => y.
    move=> [A mA <-]; exists `|fine (P A) - fine (Q A)|; first by exists A.
    have fP : P A \is a fin_num by exact: fin_num_measure.
    have fQ : Q A \is a fin_num by exact: fin_num_measure.
    by rewrite -(fineK fP) -(fineK fQ) -EFinB abse_EFin.
  move=> [_ [A mA <-] <-]; exists A => //.
  have fP : P A \is a fin_num by exact: fin_num_measure.
  have fQ : Q A \is a fin_num by exact: fin_num_measure.
  by rewrite -(fineK fP) -(fineK fQ) -EFinB abse_EFin.
by rewrite ereal_sup_EFin.
Qed.

End total_variation.

(* The product bound: replace the coordinates one at a time. *)
Section product_bound.
Context d (T : measurableType d) (R : realType).

Theorem tuple_prod_tv (mu nu : nat -> probability T R) n
    (A : set (n.-tuple T)) : measurable A ->
  (`|tuple_prod mu n A - tuple_prod nu n A| <=
    (\sum_(i < n) tv_dist (mu i) (nu i))%:E)%E.
Proof.
move=> mA.
have mF : measurable_fun setT (\1_A : n.-tuple T -> R).
  exact: measurable_indic.
have FC x : `|(\1_A : n.-tuple T -> R) x| <= 1.
  by rewrite /indic; case: (x \in A); rewrite ?normr1 ?normr0.
have hB (i : 'I_n) (x : n.-tuple T) :
    `|\int[mu i]_t (\1_A : n.-tuple T -> R) (tuple_set x i t) -
      \int[nu i]_t (\1_A : n.-tuple T -> R) (tuple_set x i t)| <=
    tv_dist (mu i) (nu i).
  pose B := tuple_set x i @^-1` A.
  have mB : measurable B.
    by rewrite -[B]setTI; exact: measurable_tuple_set.
  have E t : (\1_A : n.-tuple T -> R) (tuple_set x i t) = \1_B t.
    by rewrite /indic /B /preimage; congr (_%:R); apply/idP/idP;
      rewrite !inE.
  under eq_Rintegral do rewrite E.
  under [X in _ - X]eq_Rintegral do rewrite E.
  rewrite /Rintegral !integral_indic // !setIT.
  exact: tv_dist_ge.
have := @lindeberg_replacement _ _ _ n mu nu (\1_A) 1
  (fun i => tv_dist (mu i) (nu i)) mF FC hB.
rewrite /Rintegral !integral_indic // !setIT.
have fM : tuple_prod mu n A \is a fin_num by exact: fin_num_measure.
have fN : tuple_prod nu n A \is a fin_num by exact: fin_num_measure.
by rewrite -(fineK fM) -(fineK fN) -EFinB abse_EFin lee_fin.
Qed.

End product_bound.

(* (1 - x / n)^n tends to exp (- x). *)
Section exp_limit.
Variable R : realType.

Lemma one_sub_le_expR (y : R) : 1 - y <= expR (- y).
Proof. exact: expR_ge1Dx. Qed.

Lemma expR_le_one_sub (y : R) : 0 <= y < 1 ->
  expR (- (y / (1 - y))) <= 1 - y.
Proof.
move=> /andP[y0 y1].
have p : 0 < 1 - y by rewrite subr_gt0.
have h := expR_ge1Dx (y / (1 - y)).
have pn : 1 - y != 0 by rewrite gt_eqF.
rewrite (_ : 1 + y / (1 - y) = (1 - y)^-1) in h; first by field.
rewrite expRN -[X in _ <= X]invrK lef_pV2 ?posrE ?expR_gt0 ?invr_gt0 //.
Qed.

Lemma pow_one_sub_bounds (x : R) n : 0 <= x -> x < n%:R ->
  expR (- (x * n%:R / (n%:R - x))) <= (1 - x / n%:R) ^+ n <= expR (- x).
Proof.
move=> x0 xn.
have n0 : 0 < n%:R :> R by apply: le_lt_trans xn.
have nn : n%:R != 0 :> R by rewrite gt_eqF.
have y0 : 0 <= x / n%:R by rewrite divr_ge0 // ltW.
have y1 : x / n%:R < 1 by rewrite ltr_pdivrMr // mul1r.
have q0 : 0 <= 1 - x / n%:R by rewrite subr_ge0 ltW.
apply/andP; split.
  have h := @expR_le_one_sub (x / n%:R) (introT andP (conj y0 y1)).
  have := lerXn2r n (expR_ge0 _) q0 h.
  rewrite -expRM_natr.
  have nx : n%:R - x != 0 by rewrite subr_eq0 gt_eqF.
  have -> : - (x / n%:R / (1 - x / n%:R)) * n%:R =
      - (x * n%:R / (n%:R - x)).
    by field; rewrite subr_eq0 eq_sym gt_eqF.
  by [].
have h := lerXn2r n q0 (expR_ge0 _) (@one_sub_le_expR (x / n%:R)).
apply: le_trans h _; rewrite -expRM_natr.
by rewrite mulNr divfK.
Qed.

Lemma pow_one_sub_dist (x : R) n : 0 <= x -> x < n%:R ->
  `|(1 - x / n%:R) ^+ n - expR (- x)| <= x ^+ 2 / (n%:R - x).
Proof.
move=> x0 xn.
have nx : 0 < n%:R - x by rewrite subr_gt0.
have /andP[lo hi] := pow_one_sub_bounds x0 xn.
set p := (1 - x / n%:R) ^+ n in lo hi *.
set z := x ^+ 2 / (n%:R - x).
have z0 : 0 <= z by rewrite divr_ge0 ?sqr_ge0 // ltW.
have nxn : n%:R - x != 0 by rewrite gt_eqF.
have E : x * n%:R / (n%:R - x) = x + z by rewrite /z; field.
rewrite E opprD expRD in lo.
have e1 : expR (- x) <= 1 by rewrite expR_le1 oppr_le0.
have e0 := expR_ge0 (- x).
have hz : 1 - z <= expR (- z) by exact: (@one_sub_le_expR z).
rewrite distrC ger0_norm ?subr_ge0 //.
have : expR (- x) * (1 - z) <= expR (- x) * expR (- z) by rewrite ler_pM2l ?expR_gt0.
by nra.
Qed.

Lemma pow_one_sub_cvg (x : R) : 0 <= x ->
  (fun n : nat => (1 - x / n%:R) ^+ n) @ \oo --> expR (- x).
Proof.
move=> x0; apply/cvgrPdist_lt => e e0.
pose N := (archimedean.Num.truncn (x + x ^+ 2 / e)).+1.
exists N => // n /= Nn.
have hN : x + x ^+ 2 / e < n%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have xn : x < n%:R.
  apply: le_lt_trans hN; rewrite lerDl.
  by apply: divr_ge0; [exact: sqr_ge0 | exact: ltW].
have h := pow_one_sub_dist x0 xn.
have nx : 0 < n%:R - x by rewrite subr_gt0.
rewrite -normrN opprB; apply: le_lt_trans h _.
rewrite ltr_pdivrMr //.
by move: hN; rewrite -ltrBrDl ltr_pdivrMr // mulrC.
Qed.

End exp_limit.
