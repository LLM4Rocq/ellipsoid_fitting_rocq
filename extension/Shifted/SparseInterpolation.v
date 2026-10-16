(* Deterministic interpolation with an arbitrary shifted coordinate block.
   The positive scalar on the head block may be arbitrarily small. Only
   the complementary block is perturbed, so the correction need not be
   smaller than the head weight. No independence of coordinate blocks is
   used. The common quadratic level is retained until positivity permits
   normalization.
   Source: doc/shifted-gaussian.tex, sparse non-Gaussian shifts. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean opnorm condition_cone condition_perturbation.
From GaussianAnalysis.convex Require Import logdet_barrier.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Condition Require Import Unsat.
From EllipsoidUniversality.Shifted Require Import GaussianTargets GaussianExistence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

Lemma sparse_block_common n h p (g : paper_main_sample n p)
    (x : paper_main_sample n (h+p)) (u : 'I_n -> 'cV[RR]_h)
    (A E : 'M[RR]_p) (s c q b : R) :
  (0 < p)%N ->
  (forall i : 'I_n, paper_main_point x i = col_mx (u i) (paper_main_point g i)) ->
  (forall i : 'I_n, paper_main_quadratic_form A (paper_main_point g i) = q) ->
  (forall i : 'I_n, (paper_main_quadratic_form E (paper_main_point g i) -
     paper_main_trace E) / Num.sqrt p%:R =
     -s*(mxdot (u i) (u i)-c)/Num.sqrt p%:R+b) ->
  forall i : 'I_n, paper_main_quadratic_form
    (block_mx (s%:M : 'M[RR]_h) 0 0 (A+E)) (paper_main_point x i) =
    q+s*c+paper_main_trace E+Num.sqrt p%:R*b.
Proof.
move=> p0 hx hA hE i.
have pn : Num.sqrt (p%:R : R) != 0 by rewrite gt_eqF // sqrtr_gt0 ltr0n.
rewrite hx pm_qf_col quadratic_block_diag mul_scalar_mx mxdotZr.
rewrite mulmxDl mxdotDr -!pm_qf_col hA.
have he := hE i.
have he' := congr1 (fun z : R => z*Num.sqrt p%:R) he.
rewrite /= !mulrDl !mulfVK // in he'.
nra.
Qed.

Theorem sparse_weighted_block_interpolation n h p (g : paper_main_sample n p)
    (x : paper_main_sample n (h+p)) (u : 'I_n -> 'cV[RR]_h)
    (A : 'M[RR]_p) (D s L c q : R) :
  (0 < p)%N -> 1 <= D -> 0 < s -> s <= 1 -> 0 <= L ->
  cond_slice D A -> mixture_interpolation n p L g ->
  (forall i : 'I_n, paper_main_point x i = col_mx (u i) (paper_main_point g i)) ->
  (forall i : 'I_n, paper_main_quadratic_form A (paper_main_point g i) = q) ->
  (exists i : 'I_n, paper_main_point x i != 0) ->
  shifted_interpolation_size p L
    (fun i => -s*(mxdot (u i) (u i)-c)/Num.sqrt p%:R) <= (2*D)^-1 ->
  universality_conditioned_fit_event n (h+p) (4%:R*D^+2/s) x.
Proof.
move=> p0 D1 s0 s1 L0 hA hI hx hq hn hsize.
pose y (i : 'I_n) : R := -s*(mxdot (u i) (u i)-c)/Num.sqrt p%:R.
have [E [b [Es hE Eb]]] := shifted_interpolation_opnorm L0 hI y.
have Ee : opnorm E <= (2*D)^-1 := le_trans Eb hsize.
have [hQ Qp] := cond_slice_weighted_block h D1 hA Es Ee s0 s1.
apply: conditioned_common_cone hQ Qp _ hn.
exact: (@sparse_block_common n h p g x u A E s c q b p0 hx hq hE).
Qed.

Lemma sparse_block_point_nonzero n h p (g : paper_main_sample n p)
    (x : paper_main_sample n (h+p)) (u : 'I_n -> 'cV[RR]_h) C :
  (forall i : 'I_n, paper_main_point x i = col_mx (u i) (paper_main_point g i)) ->
  universality_conditioned_fit_event n p C g ->
  forall i : 'I_n, paper_main_point x i != 0.
Proof.
move=> hx hf i.
have hi := gaussian_conditioned_point_nonzero i hf.
apply/eqP=> z.
have dz := congr1 (@dsubmx R h p 1) z.
have dz0 : @dsubmx R h p 1 0 = 0 by apply/matrixP=>j k; rewrite !mxE.
rewrite hx col_mxKd dz0 in dz.
by move: hi; rewrite dz eqxx.
Qed.

Theorem sparse_block_fit n h p (g : paper_main_sample n p)
    (x : paper_main_sample n (h+p)) (u : 'I_n -> 'cV[RR]_h)
    (D s L c : R) :
  (0 < n)%N -> (0 < p)%N -> 1 <= D -> 0 < s -> s <= 1 -> 0 <= L ->
  universality_conditioned_fit_event n p D g -> mixture_interpolation n p L g ->
  (forall i : 'I_n, paper_main_point x i = col_mx (u i) (paper_main_point g i)) ->
  shifted_interpolation_size p L
    (fun i => -s*(mxdot (u i) (u i)-c)/Num.sqrt p%:R) <= (2*D)^-1 ->
  universality_conditioned_fit_event n (h+p) (4%:R*D^+2/s) x.
Proof.
move=> n0 p0 D1 s0 s1 L0 hf hI hx hsize.
have [A [q [hA hq]]] := gaussian_fit_common_level p0 hf.
have hn : exists i : 'I_n, paper_main_point x i != 0.
  exists (Ordinal n0).
  exact: (@sparse_block_point_nonzero n h p g x u D hx hf (Ordinal n0)).
exact: sparse_weighted_block_interpolation p0 D1 s0 s1 L0 hA hI hx hq hn hsize.
Qed.

Corollary sparse_block_pd_fit n h p (g : paper_main_sample n p)
    (x : paper_main_sample n (h+p)) (u : 'I_n -> 'cV[RR]_h)
    (D s L c : R) :
  (0 < n)%N -> (0 < p)%N -> 1 <= D -> 0 < s -> s <= 1 -> 0 <= L ->
  universality_conditioned_fit_event n p D g -> mixture_interpolation n p L g ->
  (forall i : 'I_n, paper_main_point x i = col_mx (u i) (paper_main_point g i)) ->
  shifted_interpolation_size p L
    (fun i => -s*(mxdot (u i) (u i)-c)/Num.sqrt p%:R) <= (2*D)^-1 ->
  universality_pd_fit_event n (h+p) x.
Proof.
move=> n0 p0 D1 s0 s1 L0 hf hI hx hs.
apply: cond_sub_pd.
exact: sparse_block_fit n0 p0 D1 s0 s1 L0 hf hI hx hs.
Qed.
