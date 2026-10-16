(* Reserve corrections for actual iid Gaussian and mixture samples.
   The mixture hypotheses concern the law of a whole row: central
   symmetry, centered isotropic product components, and a common
   subgaussian bound. No fourth-moment condition is needed here.
   The sample-to-matrix laws are exact. The adjoint scale is enlarged
   to its positive part before applying the generic reserve theorem.
   Source: doc/shifted-gaussian.tex, the independent reserve argument. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean nuclear centered_quadratic_correction.
From GaussianAnalysis.probability Require Import symmetric_shift independent_row_signs.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve gaussian_rows_bounds.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori.
From EllipsoidUniversality.Shifted Require Import MainMoment MixtureRows MixtureAdjoint.
From EllipsoidUniversality.Shifted Require Import ConditionTranslation ReserveModel ResidualLaws.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma raw_matrix_sample_adjoint n d (H : 'M[RR]_(n,d)) z :
  raw_sample_adj (matrix_sample H) z = coef_adj (reserve_feature H) z.
Proof.
change (coef_adj (reserve_feature (sample_point_matrix (matrix_sample H))) z =
  coef_adj (reserve_feature H) z).
by rewrite matrix_sample_matrixK.
Qed.

Definition reserve_adjoint_scale (K gamma : R) : R :=
  maxr 0 (adj_const K 252%:R (gamma+1)).

Lemma reserve_adjoint_scale_ge0 K gamma : 0 <= reserve_adjoint_scale K gamma.
Proof. by rewrite /reserve_adjoint_scale le_max lexx. Qed.

Lemma reserve_adjoint_scale_ge K gamma :
  adj_const K 252%:R (gamma+1) <= reserve_adjoint_scale K gamma.
Proof. by rewrite /reserve_adjoint_scale le_max lexx orbT. Qed.

Lemma raw_matrix_adjoint_exception n d (P : probability 'rV[RR]_d RR)
    (pi : set (paper_main_sample n d) -> \bar R) (C : R)
    (E : set (paper_main_sample n d)) :
  (forall A, measurable A ->
    independent_row_matrix_law (fun=>P) n ((@matrix_sample n d) @^-1` A) = pi A) ->
  measurable E ->
  (forall x, ~ E x -> forall z : 'rV[RR]_n,
    frobenius (raw_sample_adj x z) <= C*d%:R*frobenius z) ->
  (independent_row_matrix_law (fun=>P) n
    (~` @raw_adjoint_matrix_event n d (maxr 0 C*d%:R)%R) <= pi E)%E.
Proof.
move=> law mE bound.
have mpre : measurable ((@matrix_sample n d) @^-1` E).
  by rewrite -[X in measurable X]setTI; exact: measurable_matrix_sample.
have inc : ~` @raw_adjoint_matrix_event n d (maxr 0 C*d%:R)%R
    `<=` (@matrix_sample n d) @^-1` E.
  move=> H hH.
  have [hE|nE] := pselect (E (matrix_sample H)); first exact: hE.
  exfalso; apply: hH=>z.
  have h := bound (matrix_sample H) nE z.
  rewrite raw_matrix_sample_adjoint in h.
  apply: le_trans h _.
  apply: ler_wpM2r; first exact: frobenius_ge0.
  apply: ler_wpM2r; first exact: ler0n.
  by rewrite le_max lexx orbT.
rewrite -(law E mE).
exact (le_measure (independent_row_matrix_law (fun=>P) n)
  (mem_set (measurableC (@raw_adjoint_matrix_measurable n d (maxr 0 C*d%:R))))
  (mem_set mpre) inc).
Qed.

Lemma gaussian_reserve_adjoint_probability (k : nat -> nat) (gamma : R) :
  0 < gamma -> universality_density_tends_to k gamma ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>gauss d) (k d)
      (~` @raw_adjoint_matrix_event (k d) d
        (reserve_adjoint_scale 2 gamma*d%:R)%R) <= eps%:E)%E.
Proof.
move=> gamma0 hk eps eps0.
have [D hD] := @gaussian_raw_adjoint_bound gamma gamma0 k hk eps eps0.
exists D=>d dD; have [E [mE PE hE]] := hD d dD.
apply: le_trans _ PE.
exact: raw_matrix_adjoint_exception (@gaussian_matrix_sample_law (k d) d) mE hE.
Qed.

Theorem gaussian_reserve_model_converges (N k : nat -> nat) (beta gamma : R) :
  0 < beta -> 0 < gamma ->
  universality_density_tends_to N beta -> universality_density_tends_to k gamma ->
  forall eps delta : R, 0 < eps -> 0 < delta ->
  exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>gauss d) (N d+k d)
      (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Proof.
move=> beta0 gamma0 hN hk.
have two0 : (0:RR) < 2 by [].
exact (@reserve_model_full_converges N k (fun d=>gauss d) 2 beta gamma
  (reserve_adjoint_scale 2 gamma) two0 beta0 gamma0
  (reserve_adjoint_scale_ge0 _ _) (fun d=>@gauss_row_symmetric RR d)
  (fun d y y1=>@gauss_direction_subgaussian RR d y y1)
  (fun d y _=>@gauss_direction_mean RR d y)
  (fun d y _=>@gauss_direction_second RR d y) hN hk
  (@gaussian_reserve_adjoint_probability k gamma gamma0 hk)).
Qed.

Section finite_reserve.
Variables (K : R) (components : nat -> nat) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : mixture_family K components w mu.

Lemma finite_reserve_adjoint_probability (k : nat -> nat) (gamma : R) :
  0 < gamma -> universality_density_tends_to k gamma ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>finite_row_law hfam d) (k d)
      (~` @raw_adjoint_matrix_event (k d) d
        (reserve_adjoint_scale K gamma*d%:R)%R) <= eps%:E)%E.
Proof.
move=> gamma0 hk eps eps0.
have [D hD] := @finite_raw_adjoint_bound K gamma components w mu hfam gamma0 k hk eps eps0.
exists D=>d dD; have [E [mE PE hE]] := hD d dD.
apply: le_trans _ PE.
exact: raw_matrix_adjoint_exception
  (@finite_matrix_sample_law K components w mu hfam (k d) d) mE hE.
Qed.

Theorem finite_reserve_model_converges (N k : nat -> nat) (beta gamma : R) :
  0 < K -> 0 < beta -> 0 < gamma ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  universality_density_tends_to N beta -> universality_density_tends_to k gamma ->
  forall eps delta : R, 0 < eps -> 0 < delta ->
  exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>finite_row_law hfam d) (N d+k d)
      (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Proof.
move=> K0 beta0 gamma0 symmetric hN hk.
have fourK0 : 0 < 4*K by rewrite mulr_gt0.
exact (@reserve_model_full_converges N k (finite_row_law hfam) (4%:R*K) beta gamma
  (reserve_adjoint_scale K gamma) fourK0 beta0 gamma0
  (reserve_adjoint_scale_ge0 _ _) symmetric
  (fun d y y1=>@finite_row_subgaussian K components w mu hfam d y K0 y1)
  (fun d y y1=>@finite_row_mean K components w mu hfam d y K0 y1)
  (fun d y y1=>@finite_row_second K components w mu hfam d y K0 y1) hN hk
  (@finite_reserve_adjoint_probability k gamma gamma0 hk)).
Qed.

End finite_reserve.

Section countable_reserve.
Variables (K : R) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis hfam : countable_mixture_family K w mu.

Lemma countable_reserve_adjoint_probability (k : nat -> nat) (gamma : R) :
  0 < gamma -> universality_density_tends_to k gamma ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>countable_row_law hfam d) (k d)
      (~` @raw_adjoint_matrix_event (k d) d
        (reserve_adjoint_scale K gamma*d%:R)%R) <= eps%:E)%E.
Proof.
move=> gamma0 hk eps eps0.
have [D hD] := @countable_raw_adjoint_bound K gamma w mu hfam gamma0 k hk eps eps0.
exists D=>d dD; have [E [mE PE hE]] := hD d dD.
apply: le_trans _ PE.
exact: raw_matrix_adjoint_exception
  (@countable_matrix_sample_law K w mu hfam (k d) d) mE hE.
Qed.

Theorem countable_reserve_model_converges (N k : nat -> nat) (beta gamma : R) :
  0 < K -> 0 < beta -> 0 < gamma ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  universality_density_tends_to N beta -> universality_density_tends_to k gamma ->
  forall eps delta : R, 0 < eps -> 0 < delta ->
  exists D : nat, forall d, (D <= d)%N ->
    (independent_row_matrix_law (fun=>countable_row_law hfam d) (N d+k d)
      (@reserve_model_bad (N d) (k d) d delta) <= eps%:E)%E.
Proof.
move=> K0 beta0 gamma0 symmetric hN hk.
have fourK0 : 0 < 4*K by rewrite mulr_gt0.
exact (@reserve_model_full_converges N k (countable_row_law hfam) (4%:R*K) beta gamma
  (reserve_adjoint_scale K gamma) fourK0 beta0 gamma0
  (reserve_adjoint_scale_ge0 _ _) symmetric
  (fun d y y1=>@countable_row_subgaussian K w mu hfam d y K0 y1)
  (fun d y y1=>@countable_row_mean K w mu hfam d y K0 y1)
  (fun d y y1=>@countable_row_second K w mu hfam d y K0 y1) hN hk
  (@countable_reserve_adjoint_probability k gamma gamma0 hk)).
Qed.

End countable_reserve.
