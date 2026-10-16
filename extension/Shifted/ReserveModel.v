(* Independent reserve corrections for actual iid row samples.
   The main-sample moment uses data-dependent projection weights. Its
   independence from the reserve follows from the exact joint block law,
   not from an independence assertion about those weights. The bad event
   explicitly includes a singular centered Gram matrix. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import subgaussian symmetric_shift.
From GaussianAnalysis.probability Require Import independent_row_signs independent_matrix_blocks.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve reserve_convergence.
From GaussianAnalysis.random_matrix Require Import reserve_row_conditions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Shifted Require Import MainMoment MixtureAdjoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition reserve_model_bad n k d (delta : R) : set 'M[RR]_(n+k,d) :=
  (fun H : 'M[RR]_(n+k,d) =>
    (dsubmx H,matrix_residual_moment_map n d (usubmx H))) @^-1`
    reserve_failure delta (delta * Num.sqrt d%:R).

Lemma measurable_reserve_model_bad n k d delta :
  measurable (@reserve_model_bad n k d delta).
Proof.
rewrite /reserve_model_bad -[X in measurable X]setTI.
exact: (@measurable_independent_matrix_statistic RR d n k _ _
  (matrix_residual_moment_map n d)) measurableT _ (reserve_failure_measurable _ _).
Qed.

Lemma reserve_model_bad_law n k d (P : probability 'rV[RR]_d RR) delta :
  independent_row_matrix_law (fun=>P) (n+k) (@reserve_model_bad n k d delta) =
  (independent_row_matrix_law (fun=>P) k \x
    main_moment_law (independent_row_matrix_law (fun=>P) n))%E
    (reserve_failure delta (delta * Num.sqrt d%:R)).
Proof.
exact: (@independent_row_matrix_statistic_law RR d (fun=>P) n k _ _
  (matrix_residual_moment_map n d) _ (reserve_failure_measurable _ _)).
Qed.

Section iid_model.
Variables N k : nat -> nat.
Variable P : forall d, probability 'rV[RR]_d RR.
Variables K beta gamma L : R.
Hypotheses (K0 : 0 < K) (beta0 : 0 < beta) (gamma0 : 0 < gamma) (L0 : 0 <= L).
Hypothesis symmetric : forall d, row_symmetric_law (P d).
Hypothesis subgaussian_rows : forall d (y : 'rV[RR]_d), frobenius y <= 1 ->
  subgaussian (P d) (fun x => mxdot x y) K.
Hypothesis centered_rows : forall d (y : 'rV[RR]_d), frobenius y <= 1 ->
  \int[P d]_x mxdot x y = 0.
Hypothesis isotropic_rows : forall d (y : 'rV[RR]_d), frobenius y <= 1 ->
  \int[P d]_x mxdot x y ^+2 = frobenius y ^+2.
Hypotheses (main_density : universality_density_tends_to N beta)
  (reserve_density : universality_density_tends_to k gamma).
Let Qmain d := independent_row_matrix_law (fun=>P d) (N d).
Let Qreserve d := independent_row_matrix_law (fun=>P d) (k d).
Hypothesis raw_adjoint_probability : forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
    (Qreserve d (~` @raw_adjoint_matrix_event (k d) d (L*d%:R)) <= eps%:E)%E.

Lemma reserve_model_sign d : reserve_sign_invariant (Qreserve d).
Proof. by apply: independent_row_sign_invariant=> i hi; exact: symmetric. Qed.

Lemma reserve_model_main_sign d : reserve_sign_invariant (Qmain d).
Proof. by apply: independent_row_sign_invariant=> i hi; exact: symmetric. Qed.

Lemma reserve_model_main_tight : forall eps : R, 0 < eps ->
  exists B : R, 0 < B /\ exists D : nat, forall d, (D <= d)%N ->
    (main_moment_law (Qmain d)
      [set b | (B*Num.sqrt d%:R < frobenius b)%R] <= eps%:E)%E.
Proof.
have [M0 rows] := @reserve_independent_rows_max RR N (fun d _=>P d) K beta
  K0 beta0 (fun d i y _ hy => @subgaussian_rows d y hy)
  (fun d i y _ hy => @centered_rows d y hy) main_density.
apply: (@main_moment_tight_of_rows N Qmain (reserve_row_max_scale K beta)
  (ltW M0) reserve_model_main_sign).
exact: rows.
Qed.

Lemma reserve_model_intrinsic_probability : forall eps : R, 0 < eps ->
  exists D : nat, forall d, (D <= d)%N ->
    (Qreserve d (~` reserve_intrinsic (L*d%:R)
      (reserve_row_max_scale K gamma*d%:R)) <= eps%:E)%E.
Proof.
move=> eps eps0.
have e20 : 0 < eps/2 by rewrite divr_gt0.
have [D1 h1] := raw_adjoint_probability e20.
have [_ rows] := @reserve_independent_rows_max RR k (fun d _=>P d) K gamma
  K0 gamma0 (fun d i y _ hy => @subgaussian_rows d y hy)
  (fun d i y _ hy => @centered_rows d y hy) reserve_density.
have [D2 h2] := rows (eps/2) e20.
exists (maxn D1 D2)=>d; rewrite geq_max=>/andP[d1 d2].
pose A := @raw_adjoint_matrix_event (k d) d (L*d%:R).
pose B := @reserve_max_rows RR (k d) d (reserve_row_max_scale K gamma*d%:R).
have mA : measurable A := @raw_adjoint_matrix_measurable (k d) d (L*d%:R).
have mB : measurable B := reserve_max_rows_measurable _.
have inc : ~` reserve_intrinsic (L*d%:R) (reserve_row_max_scale K gamma*d%:R)
    `<=` (~` A) `|` (~` B).
  move=> H h; have [ha|ha] := pselect (A H); last by left.
  have [hb|hb] := pselect (B H); last by right.
  exfalso; exact: h (conj ha hb).
apply: le_trans (le_measure (Qreserve d)
  (mem_set (measurableC (reserve_intrinsic_measurable _ _)))
  (mem_set (measurableU _ _ (measurableC mA) (measurableC mB))) inc) _.
apply: le_trans (measureU2 (Qreserve d) (measurableC mA) (measurableC mB)) _.
apply: le_trans (leeD (h1 d d1) (h2 d d2)) _.
rewrite -EFinD lee_fin; lra.
Qed.

Lemma reserve_model_covariance_tight : forall eps : R, 0 < eps ->
  exists A : R, 0 < A /\ exists D : nat, forall d, (D <= d)%N ->
    (Qreserve d (~` reserve_covariance_event
      (A/Num.sqrt d%:R) (A*d%:R) (A/Num.sqrt d%:R)
      (A*d%:R*Num.sqrt d%:R)) <= eps%:E)%E.
Proof.
exact: (@reserve_independent_rows_covariance RR k (fun d _=>P d) K gamma
  K0 gamma0 (fun d i y _ hy => @subgaussian_rows d y hy)
  (fun d i y _ hy => @isotropic_rows d y hy)
  (fun d i y _ hy => @centered_rows d y hy) reserve_density).
Qed.

Theorem reserve_model_product_converges : forall eps delta : R,
  0 < eps -> 0 < delta -> exists D : nat, forall d, (D <= d)%N ->
    ((Qreserve d \x main_moment_law (Qmain d))
      (reserve_failure delta (delta*Num.sqrt d%:R)) <= eps%:E)%E.
Proof.
have [M0 _] := @reserve_independent_rows_max RR k (fun d _=>P d) K gamma
  K0 gamma0 (fun d i y _ hy => @subgaussian_rows d y hy)
  (fun d i y _ hy => @centered_rows d y hy) reserve_density.
exact: (@reserve_correction_converges RR k Qreserve
  (fun d=>main_moment_law (Qmain d)) L (reserve_row_max_scale K gamma)
  L0 (ltW M0) reserve_model_sign reserve_model_intrinsic_probability
  reserve_model_covariance_tight reserve_model_main_tight gamma gamma0 reserve_density).
Qed.

Theorem reserve_model_full_converges : forall eps delta : R,
  0 < eps -> 0 < delta -> exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>P d) (N d+k d)
      (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Proof.
move=> eps delta eps0 delta0.
have [D hD] := reserve_model_product_converges eps0 delta0.
exists D=>d dD; rewrite reserve_model_bad_law.
exact: hD.
Qed.

End iid_model.
