(* Separately-even fitting consequences for symmetric product mixtures.
   These exact sample-law identities transfer centered PSD/PD fits only;
   the arbitrary-center quadric event is not asserted to be sign invariant.
   Sign weights may depend on the dimension and include both endpoints. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.analysis Require Import family_reindexing.
From GaussianAnalysis.matrix Require Import coordinate_blocks.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows independent_row_signs symmetric_shift.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Measurability Require Import Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions
  CountableMixtureDefinitions.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Shifted Require Import GaussianRows Translations MixtureRows
  SignMixture TranslatedNonexistence SparseShift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Section finite.
Variables (K : R) (N : nat -> nat) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Variable hfam : mixture_family K N w mu.

Lemma finite_iid_sample_law n d (A : set (paper_main_sample n d)) :
  measurable A -> iid_row_sample_law (finite_row_law hfam d) n A =
    mixture_probability (N d) (w d) (mu d) n d A.
Proof.
move=> mA.
have mB : measurable (@sample_of_row_tuple n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite iid_row_sample_lawE -(finite_sample_row_tuple_law hfam mB).
congr (mixture_probability _ _ _ _ _ _); apply/funext=>x.
by rewrite /preimage /= sample_row_tupleK.
Qed.

Lemma finite_shifted_iid_sample_law n d (m : 'cV[RR]_d)
    (A : set (paper_main_sample n d)) : measurable A ->
  shifted_iid_sample_law (finite_row_law hfam d) m n A =
    mixture_probability (N d) (w d) (mu d) n d (sample_translate m @^-1` A).
Proof.
move=> mA; rewrite shifted_iid_sample_lawE // finite_iid_sample_law //.
by rewrite -[X in measurable X]setTI; exact: measurable_sample_translate.
Qed.

Theorem finite_sign_psd_nonexistence (kappa alpha : R) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1) :
  1<kappa -> universality_alpha_star kappa<alpha -> 0<K ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (finite_row_law hfam d) (m d) (ha d) (n d) (paper_main_fit_event (n d) d)) 0.
Proof.
move=> k1 aa K0 sym fourth hn.
have h := @finite_translated_psd_nonexistence kappa alpha K N w mu hfam n m
  k1 aa K0 sym fourth hn.
move=> eps eps0; have [D hD] := h eps eps0.
exists D=>d dD.
rewrite (sign_mixture_psd_probability (m d) (ha d) (n d) (sym d)).
rewrite (finite_shifted_iid_sample_law (m d) (pm_fit_event_measurable (n d) d)).
exact: hD.
Qed.
End finite.

Section countable.
Variables (K : R) (w : nat -> nat -> R).
Variable mu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Variable hfam : countable_mixture_family K w mu.

Lemma countable_iid_sample_law n d (A : set (paper_main_sample n d)) :
  measurable A -> iid_row_sample_law (countable_row_law hfam d) n A =
    countable_mixture_probability (w d) (mu d) n d A.
Proof.
move=> mA.
have mB : measurable (@sample_of_row_tuple n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_sample_of_row_tuple.
rewrite iid_row_sample_lawE -(countable_sample_row_tuple_law hfam mB).
congr (countable_mixture_probability _ _ _ _ _); apply/funext=>x.
by rewrite /preimage /= sample_row_tupleK.
Qed.

Lemma countable_shifted_iid_sample_law n d (m : 'cV[RR]_d)
    (A : set (paper_main_sample n d)) : measurable A ->
  shifted_iid_sample_law (countable_row_law hfam d) m n A =
    countable_mixture_probability (w d) (mu d) n d (sample_translate m @^-1` A).
Proof.
move=> mA; rewrite shifted_iid_sample_lawE // countable_iid_sample_law //.
by rewrite -[X in measurable X]setTI; exact: measurable_sample_translate.
Qed.

Theorem countable_sign_psd_nonexistence (kappa alpha : R) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1) :
  1<kappa -> universality_alpha_star kappa<alpha -> 0<K ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu -> universality_density_tends_to n alpha ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (countable_row_law hfam d) (m d) (ha d) (n d) (paper_main_fit_event (n d) d)) 0.
Proof.
move=> k1 aa K0 sym fourth hn.
have h := @countable_translated_psd_nonexistence kappa alpha K w mu hfam n m
  k1 aa K0 sym fourth hn.
move=> eps eps0; have [D hD] := h eps eps0.
exists D=>d dD.
rewrite (sign_mixture_psd_probability (m d) (ha d) (n d) (sym d)).
rewrite (countable_shifted_iid_sample_law (m d) (pm_fit_event_measurable (n d) d)).
exact: hD.
Qed.
End countable.

Theorem finite_sign_sparse_pd (kappa K alpha : R)
    (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : mixture_family K N w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall d, row_symmetric_law (finite_row_law hfam d)) ->
  mixture_fourth_moment kappa N w mu -> universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (finite_row_law hfam d) (m d) (ha d) (n d) (universality_pd_fit_event (n d) d)) 1.
Proof.
move=>k1 K0 a0 below sym fourth hn hs.
have h := @finite_sparse_shift_theorem kappa K alpha k1 K0 a0 below
  N w mu n hfam fourth hn m hs.
move=>eps eps0; have [D hD] := h eps eps0.
exists D=>d dD.
rewrite (sign_mixture_pd_probability (m d) (ha d) (n d) (sym d)).
rewrite (finite_shifted_iid_sample_law hfam (m d) (measurable_pd_fit_event (n d) d)).
exact: hD.
Qed.

Theorem countable_sign_sparse_pd (kappa K alpha : R)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hfam : countable_mixture_family K w mu) (n : nat -> nat)
    (m : forall d, 'cV[RR]_d) (a : nat -> R) (ha : forall d, 0<=a d<=1) :
  1<kappa -> 0<K -> 0<alpha -> alpha<universality_alpha_star kappa ->
  (forall d, row_symmetric_law (countable_row_law hfam d)) ->
  countable_fourth_moment kappa w mu -> universality_density_tends_to n alpha ->
  family_sequence_limit (fun d => (#|coordinate_support (m d)|)%:R/d%:R : RR) 0 ->
  paper_main_tends_to (fun d=>sign_mixture_sample_law
    (countable_row_law hfam d) (m d) (ha d) (n d) (universality_pd_fit_event (n d) d)) 1.
Proof.
move=>k1 K0 a0 below sym fourth hn hs.
have h := @countable_sparse_shift_theorem kappa K alpha k1 K0 a0 below
  w mu n hfam fourth hn m hs.
move=>eps eps0; have [D hD] := h eps eps0.
exists D=>d dD.
rewrite (sign_mixture_pd_probability (m d) (ha d) (n d) (sym d)).
rewrite (countable_shifted_iid_sample_law hfam (m d) (measurable_pd_fit_event (n d) d)).
exact: hD.
Qed.
