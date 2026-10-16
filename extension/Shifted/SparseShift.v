(* Positive definite fitting for deterministic shifts supported on o(d)
   arbitrary coordinates. Coordinate permutation is exact, and the local
   selected laws retain the original weights, sub-Gaussian constant and
   averaged fourth moment. The cofinal application uses the original family
   and sample counts as its baseline; no symmetry or norm bound on the shift
   is assumed.
   Source: doc/shifted-gaussian.tex, sparse non-Gaussian shifts. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import sequences esum ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral coordinate_blocks.
From GaussianAnalysis.convex Require Import logdet_barrier.
From GaussianAnalysis.analysis Require Import family_reindexing.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Gaussian Require Import Limit.
From EllipsoidUniversality.Shifted Require Import GaussianRows SparseRows Translations.
From EllipsoidUniversality.Shifted Require Import SparseCoordinates SparseDimensions SparseInputs.
From EllipsoidUniversality.Shifted Require Import ReserveDensity SparseBlockSamples SparseExistence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma measurable_sparse_translated_pd_fit n d (m : 'cV[RR]_d) :
  measurable (sample_translate m @^-1` universality_pd_fit_event n d).
Proof.
rewrite -[X in measurable X]setTI.
exact: measurable_sample_translate (measurable_pd_fit_event _ _).
Qed.

Lemma sparse_pd_fit_coordinateE n d e (f : 'I_e -> 'I_d)
    (x : paper_main_sample n d) : bijective f ->
  universality_pd_fit_event n e (sparse_sample_pick f x) =
    universality_pd_fit_event n d x.
Proof.
move=> hf; apply/propext; split; first exact: sparse_pd_fit_pullback.
move=> [Q [Qpd hfit]]; exists (mxsub f f Q); split.
- apply: (sparse_paper_pd_posdef _).2.
  apply: coordinate_posdef_forward hf _.
  exact: (sparse_paper_pd_posdef _).1 Qpd.
- move=> i; rewrite sparse_sample_pick_pointE paper_quadratic_mxdot.
  by rewrite coordinate_quadratic_form // -paper_quadratic_mxdot; exact: hfit.
Qed.

Lemma sparse_shifted_fit_preimage n d e (f : 'I_e -> 'I_d)
    (m : 'cV[RR]_d) : bijective f ->
  (@sparse_sample_pick n d e f) @^-1`
    (sample_translate (rowsub f m) @^-1` universality_pd_fit_event n e) =
  sample_translate m @^-1` universality_pd_fit_event n d.
Proof.
move=> hf; apply/funext => x /=.
by rewrite -sparse_sample_pick_translate sparse_pd_fit_coordinateE.
Qed.

Lemma finite_sparse_shifted_fit_law n d e (f : 'I_e -> 'I_d)
    (N : nat) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (m : 'cV[RR]_d) : bijective f ->
  mixture_probability N w mu n d
    (sample_translate m @^-1` universality_pd_fit_event n d) =
  mixture_probability N w (sparse_selected_law f mu) n e
    (sample_translate (rowsub f m) @^-1` universality_pd_fit_event n e).
Proof.
move=> hf; have [g hfg hgf] := hf.
have fi : injective f := can_inj hfg.
rewrite -(finite_sparse_selected_law N w mu fi
  (@measurable_sparse_translated_pd_fit n e (rowsub f m))).
by rewrite sparse_shifted_fit_preimage.
Qed.

Lemma countable_sparse_shifted_fit_law n d e (f : 'I_e -> 'I_d)
    (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (m : 'cV[RR]_d) : bijective f ->
  countable_mixture_probability w mu n d
    (sample_translate m @^-1` universality_pd_fit_event n d) =
  countable_mixture_probability w (sparse_selected_law f mu) n e
    (sample_translate (rowsub f m) @^-1` universality_pd_fit_event n e).
Proof.
move=> hf; have [g hfg hgf] := hf.
have fi : injective f := can_inj hfg.
rewrite -(countable_sparse_selected_law w mu fi
  (@measurable_sparse_translated_pd_fit n e (rowsub f m))).
by rewrite sparse_shifted_fit_preimage.
Qed.

Definition sparse_finite_select d e (f : 'I_e -> 'I_d)
    (t : sparse_finite_parameters) : sparse_finite_parameters :=
  SparseFiniteParameters (sparse_finite_n t) (sparse_finite_components t)
    (sparse_finite_weights t) (sparse_selected_law f (sparse_finite_laws t)).

Definition sparse_countable_select d e (f : 'I_e -> 'I_d)
    (t : sparse_countable_parameters) : sparse_countable_parameters :=
  SparseCountableParameters (sparse_countable_n t)
    (sparse_countable_weights t) (sparse_selected_law f (sparse_countable_laws t)).

Lemma sparse_finite_select_admissible d e (f : 'I_e -> 'I_d)
    (t : sparse_finite_parameters) (K kappa : R) :
  sparse_finite_admissible K kappa d t ->
  sparse_finite_admissible K kappa e (sparse_finite_select f t).
Proof.
move=> [[w0 [w1 hm]] hk]; split; last exact: sparse_selected_finite_fourth hk.
split => //; split => // s j sN je.
apply: sparse_selected_component je => k kd.
exact: hm sN kd.
Qed.

Lemma sparse_countable_select_admissible d e (f : 'I_e -> 'I_d)
    (t : sparse_countable_parameters) (K kappa : R) :
  sparse_countable_admissible K kappa d t ->
  sparse_countable_admissible K kappa e (sparse_countable_select f t).
Proof.
move=> [[w0 [w1 hm]] hk]; split; last exact: sparse_selected_countable_fourth hk.
split => //; split => // s j je.
apply: sparse_selected_component je => k kd.
exact: hm kd.
Qed.

Lemma sparse_support_dimension_limits (m : forall d, 'cV[RR]_d) :
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  family_cofinal (fun d => #|~: coordinate_support (m d)|) /\
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/
      (#|~: coordinate_support (m d)|)%:R : RR) 0 /\
  forall (n : nat -> nat) (alpha : RR), universality_density_tends_to n alpha ->
    family_sequence_limit
      (fun d => (n d)%:R/(#|~: coordinate_support (m d)|)%:R^+2 : RR) alpha.
Proof.
move=> hs.
pose h d := #|coordinate_support (m d)|.
pose p d := #|~: coordinate_support (m d)|.
have hb d : (h d <= d)%N.
  have hh := max_card (coordinate_support (m d)).
  by rewrite card_ord in hh.
have pe : p = (fun d => (d-h d)%N).
  by apply/funext=>d; exact: coordinate_partition_complement.
change (family_cofinal p /\
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 /\
  forall (n : nat -> nat) (alpha : RR), universality_density_tends_to n alpha ->
    family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha).
rewrite pe; split; first exact: sparse_complement_cofinal hb hs.
split; first exact: sparse_head_complement_limit hb hs.
by move=> n alpha hn; exact: sparse_complement_density_limit hb hs hn.
Qed.

Theorem finite_sparse_shift_theorem (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  forall (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (n : nat -> nat),
  mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
  universality_density_tends_to n alpha ->
  forall m : forall d, 'cV[RR]_d,
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to
    (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
      (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) 1.
Proof.
move=> k1 K0 a0 below N w mu n hfam hfourth hn m hs.
pose base d := SparseFiniteParameters (n d) (N d) (w d) (mu d).
pose h d := #|coordinate_support (m d)|.
pose p d := #|~: coordinate_support (m d)|.
pose x d := sparse_finite_select (sparse_support_index (m d)) (base d).
pose mr d := sparse_support_shift_row (m d).
have base_ok d : sparse_finite_admissible K kappa d (base d).
  by split; [exact: hfam | exact: hfourth].
have x_ok d : sparse_finite_admissible K kappa (h d+p d) (x d).
  exact: sparse_finite_select_admissible (base_ok d).
have [pc [hrel nrel]] := sparse_support_dimension_limits hs.
have hbase : family_sequence_limit
    (fun d => (sparse_finite_n (base d))%:R/d%:R^+2 : RR) alpha.
  exact: reserve_density_scalar_limit hn.
have hlocal : family_sequence_limit
    (fun d => (sparse_finite_n (x d))%:R/(p d)%:R^+2 : RR) alpha.
  exact: nrel n alpha hn.
have cv := @finite_sparse_shift_pd kappa K alpha base h p x mr
  k1 K0 a0 below base_ok hbase pc x_ok hrel hlocal.
move=> eps eps0; have [D hD] := cv eps eps0.
exists D => d dD.
move: (hD d dD).
rewrite /sparse_finite_probability /x /sparse_finite_select /base /=.
rewrite /sparse_block_shift /mr -sparse_support_shift_row_block.
by rewrite -finite_sparse_shifted_fit_law //; exact: sparse_support_index_bij.
Qed.

Theorem countable_sparse_shift_theorem (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  forall (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (n : nat -> nat),
  countable_mixture_family K w mu -> countable_fourth_moment kappa w mu ->
  universality_density_tends_to n alpha ->
  forall m : forall d, 'cV[RR]_d,
  family_sequence_limit
    (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to
    (fun d => countable_mixture_probability (w d) (mu d) (n d) d
      (sample_translate (m d) @^-1` universality_pd_fit_event (n d) d)) 1.
Proof.
move=> k1 K0 a0 below w mu n hfam hfourth hn m hs.
pose base d := SparseCountableParameters (n d) (w d) (mu d).
pose h d := #|coordinate_support (m d)|.
pose p d := #|~: coordinate_support (m d)|.
pose x d := sparse_countable_select (sparse_support_index (m d)) (base d).
pose mr d := sparse_support_shift_row (m d).
have base_ok d : sparse_countable_admissible K kappa d (base d).
  by split; [exact: hfam | exact: hfourth].
have x_ok d : sparse_countable_admissible K kappa (h d+p d) (x d).
  exact: sparse_countable_select_admissible (base_ok d).
have [pc [hrel nrel]] := sparse_support_dimension_limits hs.
have hbase : family_sequence_limit
    (fun d => (sparse_countable_n (base d))%:R/d%:R^+2 : RR) alpha.
  exact: reserve_density_scalar_limit hn.
have hlocal : family_sequence_limit
    (fun d => (sparse_countable_n (x d))%:R/(p d)%:R^+2 : RR) alpha.
  exact: nrel n alpha hn.
have cv := @countable_sparse_shift_pd kappa K alpha base h p x mr
  k1 K0 a0 below base_ok hbase pc x_ok hrel hlocal.
move=> eps eps0; have [D hD] := cv eps eps0.
exists D => d dD.
move: (hD d dD).
rewrite /sparse_countable_probability /x /sparse_countable_select /base /=.
rewrite /sparse_block_shift /mr -sparse_support_shift_row_block.
by rewrite -countable_sparse_shifted_fit_law //; exact: sparse_support_index_bij.
Qed.
