(* Arbitrary sparse supports are moved to a leading coordinate block by the
   explicit partition bijection of coordinate_blocks. All law identities are
   exact. Coordinate laws outside the selected range use the original law at
   coordinate zero; no admissibility claim is made about that fallback.
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
From GaussianAnalysis.probability Require Import lindeberg tuple_rows conditioning.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality.Gaussian Require Import Limit.
From EllipsoidUniversality.Shifted Require Import GaussianRows SparseRows Translations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sparse_support_index d (m : 'cV[RR]_d) :=
  @coordinate_partition_index d (coordinate_support m).
Arguments sparse_support_index {d} m _.

Definition sparse_support_shift d (m : 'cV[RR]_d) :=
  usubmx (rowsub (sparse_support_index m) m).

Definition sparse_support_shift_row d (m : 'cV[RR]_d) :=
  (sparse_support_shift m)^T.

Lemma sparse_support_index_bij d (m : 'cV[RR]_d) :
  bijective (sparse_support_index m).
Proof. exact: coordinate_partition_bij. Qed.

Lemma sparse_support_shift_block d (m : 'cV[RR]_d) :
  rowsub (sparse_support_index m) m = col_mx (sparse_support_shift m) 0.
Proof.
rewrite /sparse_support_shift -{1}[rowsub _ _]vsubmxK.
congr (col_mx _ _); apply/matrixP => j k.
have -> : k = 0 by apply: ord1.
by rewrite !mxE; exact: coordinate_support_tail.
Qed.

Lemma sparse_support_shift_row_block d (m : 'cV[RR]_d) :
  rowsub (sparse_support_index m) m = col_mx (sparse_support_shift_row m)^T 0.
Proof. by rewrite /sparse_support_shift_row trmxK sparse_support_shift_block. Qed.

Lemma sparse_sample_pick_pointE n d e (f : 'I_e -> 'I_d)
    (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point (sparse_sample_pick f x) i = rowsub f (paper_main_point x i).
Proof.
apply/matrixP => j k; have -> : k = 0 by apply: ord1.
by rewrite [in RHS]mxE sparse_sample_pick_point.
Qed.

Lemma sparse_sample_pick_translate n d e (f : 'I_e -> 'I_d)
    (m : 'cV[RR]_d) (x : paper_main_sample n d) :
  sparse_sample_pick f (sample_translate m x) =
    sample_translate (rowsub f m) (sparse_sample_pick f x).
Proof.
have hp (i : 'I_n) :
    paper_main_point (sparse_sample_pick f (sample_translate m x)) i =
    paper_main_point (sample_translate (rowsub f m) (sparse_sample_pick f x)) i.
  by rewrite sparse_sample_pick_pointE !sample_translate_point
    sparse_sample_pick_pointE raddfD.
apply: eq_from_tnth => a.
by rewrite -{1 2}(sample_flat_indicesK a) -!sparse_point_entry hp.
Qed.

Lemma sparse_support_sample_translate n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) :
  sparse_sample_pick (sparse_support_index m) (sample_translate m x) =
    sample_translate (col_mx (sparse_support_shift_row m)^T 0)
      (sparse_sample_pick (sparse_support_index m) x).
Proof. by rewrite sparse_sample_pick_translate sparse_support_shift_row_block. Qed.

Lemma sparse_paper_pd_posdef d (A : 'M[RR]_d) :
  paper_main_pd A <-> posdefmx A.
Proof.
split => [[As Ap]|[As Ap]].
- have As' : A \is symmetricmx := (@paper_symmetricP d A).1 As.
  have AT : A^T = A by apply/symmetricmxP.
  split => // x x0.
  have xt0 : x^T != 0 by rewrite trmx_eq0.
  have h := Ap _ xt0.
  by rewrite paper_quadratic_mxdot -mxdot_trmx trmx_mul trmxK AT in h.
- have AT : A^T = A by apply/symmetricmxP.
  split; first exact: (@paper_symmetricP d A).2 As.
  move=> x x0; have xt0 : x^T != 0 by rewrite trmx_eq0.
  have h := Ap _ xt0.
  rewrite paper_quadratic_mxdot.
  by rewrite -mxdot_trmx trmx_mul trmxK AT in h.
Qed.

Lemma sparse_pd_fit_pullback n d e (f : 'I_e -> 'I_d)
    (x : paper_main_sample n d) :
  bijective f -> universality_pd_fit_event n e (sparse_sample_pick f x) ->
  universality_pd_fit_event n d x.
Proof.
move=> [g hfg hgf] [Q [Qp hfit]].
have Qpd : posdefmx Q := (sparse_paper_pd_posdef Q).1 Qp.
have hfit' (i : 'I_n) :
    mxdot (rowsub f (paper_main_point x i))
      (Q *m rowsub f (paper_main_point x i)) = 1.
  by rewrite -sparse_sample_pick_pointE -paper_quadratic_mxdot; exact: hfit.
have [Qpd' h] := coordinate_pd_fit_pullback hfg hgf Qpd hfit'.
exists (mxsub g g Q); split; first exact: (sparse_paper_pd_posdef _).2 Qpd'.
by move=> i; rewrite paper_quadratic_mxdot; exact: h.
Qed.

Lemma sparse_shifted_pd_fit_pullback n d e (f : 'I_e -> 'I_d)
    (m : 'cV[RR]_d) (x : paper_main_sample n d) :
  bijective f ->
  universality_pd_fit_event n e
    (sample_translate (rowsub f m) (sparse_sample_pick f x)) ->
  universality_pd_fit_event n d (sample_translate m x).
Proof.
move=> hf; rewrite -sparse_sample_pick_translate.
exact: sparse_pd_fit_pullback.
Qed.

Lemma sparse_support_pd_fit_pullback n d (m : 'cV[RR]_d)
    (x : paper_main_sample n d) :
  universality_pd_fit_event n (#|coordinate_support m| + #|~: coordinate_support m|)
    (sample_translate (col_mx (sparse_support_shift_row m)^T 0)
      (sparse_sample_pick (sparse_support_index m) x)) ->
  universality_pd_fit_event n d (sample_translate m x).
Proof.
rewrite -sparse_support_shift_row_block.
exact: sparse_shifted_pd_fit_pullback (sparse_support_index_bij m).
Qed.

Definition sparse_selected_law d e (f : 'I_e -> 'I_d)
    (mu : nat -> nat -> probability (measurableTypeR R) R) s j :=
  match insub j : option 'I_e with
  | Some k => mu s (f k)
  | None => mu s 0%N
  end.

Lemma sparse_selected_lawE d e (f : 'I_e -> 'I_d)
    (mu : nat -> nat -> probability (measurableTypeR R) R) s (j : 'I_e) :
  sparse_selected_law f mu s j = mu s (f j).
Proof. by rewrite /sparse_selected_law valK. Qed.

Lemma sparse_selected_component d e (f : 'I_e -> 'I_d)
    (mu : nat -> nat -> probability (measurableTypeR R) R) (K : R) s :
  (forall j, (j < d)%N -> mixture_component_law K (mu s j)) ->
  forall j, (j < e)%N -> mixture_component_law K (sparse_selected_law f mu s j).
Proof.
move=> hm j hj; rewrite (sparse_selected_lawE f mu s (Ordinal hj)).
exact: hm (ltn_ord _).
Qed.

Lemma sparse_selected_finite_fourth d e (f : 'I_e -> 'I_d)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (N : nat) (w : nat -> R) (kappa : R) :
  (forall j, (j < d)%N ->
    (\sum_(s < N) (w s)%:E * 'E_(mu s j)[universality_power 4])%E = kappa%:E) ->
  forall j, (j < e)%N ->
    (\sum_(s < N) (w s)%:E *
      'E_(sparse_selected_law f mu s j)[universality_power 4])%E = kappa%:E.
Proof.
move=> hm j hj.
under eq_bigr do rewrite (sparse_selected_lawE f mu _ (Ordinal hj)).
exact: hm (ltn_ord _).
Qed.

Lemma sparse_selected_countable_fourth d e (f : 'I_e -> 'I_d)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (w : nat -> R) (kappa : R) :
  (forall j, (j < d)%N ->
    (\sum_(s <oo) (w s)%:E * 'E_(mu s j)[universality_power 4])%E = kappa%:E) ->
  forall j, (j < e)%N ->
    (\sum_(s <oo) (w s)%:E *
      'E_(sparse_selected_law f mu s j)[universality_power 4])%E = kappa%:E.
Proof.
move=> hm j hj.
under eq_eseriesr do rewrite (sparse_selected_lawE f mu _ (Ordinal hj)).
exact: hm (ltn_ord _).
Qed.

Lemma finite_sparse_selected_law n d e (f : 'I_e -> 'I_d)
    (N : nat) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set (paper_main_sample n e)) : injective f -> measurable A ->
  mixture_probability N w mu n d ((@sparse_sample_pick n d e f) @^-1` A) =
  mixture_probability N w (sparse_selected_law f mu) n e A.
Proof.
move=> hf mA; apply: finite_sparse_sample_law hf _ mA => s j.
exact: sparse_selected_lawE.
Qed.

Lemma countable_sparse_selected_law n d e (f : 'I_e -> 'I_d)
    (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set (paper_main_sample n e)) : injective f -> measurable A ->
  countable_mixture_probability w mu n d ((@sparse_sample_pick n d e f) @^-1` A) =
  countable_mixture_probability w (sparse_selected_law f mu) n e A.
Proof.
move=> hf mA; apply: countable_sparse_sample_law hf _ mA => s j.
exact: sparse_selected_lawE.
Qed.
