(* Exact row-law bridges for admissible product mixtures. Component product
   structure is used before mixing; the mixture rows need not have independent
   coordinates. These estimates do not use fourth moments or symmetry. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import esum sequences ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows subgaussian mixture.
From GaussianAnalysis.probability Require Import isotropic_mixtures countable_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component Flat.
From EllipsoidUniversality.Sat Require Import AprioriSparse.
From EllipsoidUniversality.Shifted Require Import GaussianRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma coordinate_row_standard d (t : d.-tuple (measurableTypeR R)) :
  coordinate_row t = row_of_tuple d t.
Proof. by apply/matrixP => i j; rewrite (ord1 i) /coordinate_row row_of_tupleE. Qed.

Lemma component_row_law_identity d nu (A : set 'rV[RR]_d) :
  measurable A -> point_law d nu A = tuple_prod nu d (coordinate_row @^-1` A).
Proof.
move=> mA; rewrite /point_law /distribution /pushforward /=.
congr (tuple_prod _ _ _); apply/seteqP; split=> t /=;
  by rewrite coordinate_row_standard.
Qed.

Section component_rows.
Variables (K : R) (d : nat) (nu : nat -> probability (measurableTypeR R) R).
Hypothesis hnu : forall j, (j<d)%N -> mixture_component_law K (nu j).

Lemma component_row_subgaussian (y : 'rV[RR]_d) : 0 < K -> frobenius y <= 1 ->
  subgaussian (point_law d nu) (fun x => mxdot x y) (4*K).
Proof.
move=> K0 y1.
apply: (@product_row_subgaussian RR d nu (point_law d nu)
  (@component_row_law_identity d nu) K K0 _ _ y y1).
- by move=> j jd; exact: @component_law_subgaussian K (nu j) (@hnu j jd).
- move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_mean K (nu j) (@hnu j jd)).
Qed.

Lemma component_row_mean (y : 'rV[RR]_d) :
  \int[point_law d nu]_x mxdot x y = 0.
Proof. by rewrite /Rintegral (@point_lin_mean K d nu hnu). Qed.

Lemma component_row_second (y : 'rV[RR]_d) :
  \int[point_law d nu]_x mxdot x y ^+2 = frobenius y ^+2.
Proof.
apply: (@product_row_second RR d nu (point_law d nu)
  (@component_row_law_identity d nu) K _ _ _ y).
- by move=> j jd; exact: @component_law_subgaussian K (nu j) (@hnu j jd).
- move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_mean K (nu j) (@hnu j jd)).
- move=> j jd; rewrite /Rintegral.
  by rewrite (@component_law_second K (nu j) (@hnu j jd)).
Qed.

End component_rows.

Section finite_rows.
Variables (K : R) (N : nat -> nat) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : mixture_family K N w mu.

Lemma finite_row_weights d : mixture_weights (fun s : 'I_(N d) => w d s).
Proof. by have [w0 [w1 _]] := hfam d; split => // s; exact: w0. Qed.

Definition finite_row_law d : probability 'rV[RR]_d RR :=
  mixture (fun s : 'I_(N d) => point_law d (mu d s)) (finite_row_weights d).

Lemma finite_row_component d (s : 'I_(N d)) j : (j<d)%N ->
  mixture_component_law K (mu d s j).
Proof. by have [_ [_ h]] := hfam d; exact: h (ltn_ord s). Qed.

Theorem finite_row_subgaussian d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 ->
  subgaussian (finite_row_law d) (fun x => mxdot x y) (4*K).
Proof.
move=> K0 y1.
apply: (@finite_mixture_row_subgaussian RR d _
  _ _ (finite_row_weights d) (4*K) _ y y1) => s z z1.
exact: @component_row_subgaussian K d (mu d s) (@finite_row_component d s) z K0 z1.
Qed.

Theorem finite_row_mean d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 -> \int[finite_row_law d]_x mxdot x y = 0.
Proof.
move=> K0 y1.
apply: (@finite_mixture_row_mean RR d _
  _ _ (finite_row_weights d) (4*K) _ _ y y1).
- by move=> s z z1; exact: @component_row_subgaussian K d (mu d s) (@finite_row_component d s) z K0 z1.
- by move=> s z z1; exact: @component_row_mean K d (mu d s) (@finite_row_component d s) z.
Qed.

Theorem finite_row_second d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 ->
  \int[finite_row_law d]_x mxdot x y ^+2 = frobenius y ^+2.
Proof.
move=> K0 y1.
apply: (@finite_mixture_row_second RR d _
  _ _ (finite_row_weights d) (4*K) _ _ y y1).
- by move=> s z z1; exact: @component_row_subgaussian K d (mu d s) (@finite_row_component d s) z K0 z1.
- by move=> s z z1; exact: @component_row_second K d (mu d s) (@finite_row_component d s) z.
Qed.

Theorem finite_sample_row_tuple_law n d (A : set (n.-tuple 'rV[RR]_d)) :
  measurable A ->
  mixture_probability (N d) (w d) (mu d) n d (sample_row_tuple @^-1` A) =
  tuple_prod (fun=> finite_row_law d) n A.
Proof.
move=> mA.
have [s0 _] := mixture_weights_inhabited (finite_row_weights d).
rewrite /finite_row_law (tuple_prod_mixture _ (finite_row_weights d) s0 mA).
rewrite /mixture_probability; apply: eq_bigr => s _; congr (_ * _)%E.
rewrite /mixture_labelled_law.
have E : sample_row_tuple = (fun x : paper_main_sample n d =>
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x)).
  by apply/funext => x; exact: sample_row_tupleE.
rewrite E.
rewrite (@flat_map_law _ n d _ _ (fun i => point_law d
  (flat_row (fun k => mu d (mixture_label s (k %/ d)) (k %% d)) d i))
  (row_of_tuple d) A).
- exact: measurable_row_of_tuple.
- by move=> i B mB; rewrite /point_law /distribution /pushforward.
- exact: mA.
- refine (f_equal (fun Q : probability (n.-tuple 'rV[RR]_d) RR => Q A) _).
  apply: eq_tuple_prod => i hi.
  pose ii : 'I_n := Ordinal hi.
  have es : nth s0 s i = tnth s ii by rewrite (tnth_nth s0) /ii.
  rewrite es /point_law (@flat_row_label_prod (N d) (mu d) n d s ii).
  by [].
Qed.

End finite_rows.

Section countable_rows.
Variables (K : R) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : countable_mixture_family K w mu.

Lemma countable_row_weights d : cmixture_weights (w d).
Proof. by have [w0 [w1 _]] := hfam d; split. Qed.

Definition countable_row_law d : probability 'rV[RR]_d RR :=
  cmixture (fun s => point_law d (mu d s)) (countable_row_weights d).

Lemma countable_row_component d s j : (j<d)%N ->
  mixture_component_law K (mu d s j).
Proof. by have [_ [_ h]] := hfam d; exact: h. Qed.

Theorem countable_row_subgaussian d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 ->
  subgaussian (countable_row_law d) (fun x => mxdot x y) (4*K).
Proof.
move=> K0 y1.
apply: (@countable_mixture_row_subgaussian RR d
  _ _ (countable_row_weights d) (4*K) _ y y1) => s z z1.
exact: @component_row_subgaussian K d (mu d s) (@countable_row_component d s) z K0 z1.
Qed.

Theorem countable_row_mean d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 -> \int[countable_row_law d]_x mxdot x y = 0.
Proof.
move=> K0 y1.
apply: (@countable_mixture_row_mean RR d
  _ _ (countable_row_weights d) (4*K) _ _ _ y y1).
- by move=> s z z1; exact: @component_row_subgaussian K d (mu d s) (@countable_row_component d s) z K0 z1.
- by move=> s z z1; exact: @component_row_mean K d (mu d s) (@countable_row_component d s) z.
- by move=> s z z1; exact: @component_row_second K d (mu d s) (@countable_row_component d s) z.
Qed.

Theorem countable_row_second d (y : 'rV[RR]_d) :
  0 < K -> frobenius y <= 1 ->
  \int[countable_row_law d]_x mxdot x y ^+2 = frobenius y ^+2.
Proof.
move=> K0 y1.
apply: (@countable_mixture_row_second RR d
  _ _ (countable_row_weights d) (4*K) _ _ y y1).
- by move=> s z z1; exact: @component_row_subgaussian K d (mu d s) (@countable_row_component d s) z K0 z1.
- by move=> s z z1; exact: @component_row_second K d (mu d s) (@countable_row_component d s) z.
Qed.

Theorem countable_sample_row_tuple_law n d (A : set (n.-tuple 'rV[RR]_d)) :
  measurable A ->
  countable_mixture_probability (w d) (mu d) n d (sample_row_tuple @^-1` A) =
  tuple_prod (fun=> countable_row_law d) n A.
Proof.
move=> mA.
rewrite /countable_row_law (tuple_prod_cmixture _ (countable_row_weights d) mA).
rewrite /countable_mixture_probability; apply: eq_esum => s _; congr (_ * _)%E.
rewrite /countable_labelled_law.
have E : sample_row_tuple = (fun x : paper_main_sample n d =>
  tuple_map (fun=> row_of_tuple d) (tuple_rows n d x)).
  by apply/funext => x; exact: sample_row_tupleE.
rewrite E.
rewrite (@flat_map_law _ n d _ _ (fun i => point_law d
  (flat_row (fun k => mu d (nth 0%N s (k %/ d)) (k %% d)) d i))
  (row_of_tuple d) A).
- exact: measurable_row_of_tuple.
- by move=> i B mB; rewrite /point_law /distribution /pushforward.
- exact: mA.
- refine (f_equal (fun Q : probability (n.-tuple 'rV[RR]_d) RR => Q A) _).
  apply: eq_tuple_prod => i hi; rewrite /point_law.
  have Ep : tuple_prod (flat_row
      (fun k => mu d (nth 0%N s (k %/ d)) (k %% d)) d i) d =
      tuple_prod (mu d (nth 0%N s i)) d.
    apply: eq_tuple_prod => j hj.
    have d0 : (0<d)%N := leq_ltn_trans (leq0n j) hj.
    by rewrite /flat_row divnMDl // divn_small // addn0 modnMDl modn_small.
  by rewrite Ep.
Qed.

End countable_rows.
