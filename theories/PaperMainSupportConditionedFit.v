(* From positive dual cone support to an exact trace-d conditioned fit. *)
From Stdlib Require Import Reals List Lia Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions PaperMainMatrixDuality
  PaperMainHeadTailSupportSplit PaperMainHeadTailSupportAll
  PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth
  PaperMainGeometryHeadWidthCompact PaperMainConeKernelSlice PaperMainConeKernel.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_cone_kernel_conditioned_fit N d kappa
    (x : paper_main_sample N d) (P : 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa -> paper_main_head_cone_sphere kappa P ->
  (forall i : 'I_N, paper_main_pairing (paper_main_head_feature x i) P = 0) ->
  paper_main_conditioned_event N d kappa^-1 kappa x.
Proof.
move=> Hd Hk HP Hker.
have Hdp : (0 < d%:R :> R) by rewrite ltr0n.
have Hkp : 0 < kappa by exact: lt_le_trans ltr01 Hk.
have [Ht [lam HS]] := paper_main_cone_kernel_slice_of_sphere d kappa P Hd Hk HP.
rewrite /paper_main_cone_kernel_slice /= pmhw_S_lift pmhw_lam_lift in HS.
case: HS => Llo [Lhi [Qlo [Qhi Qtr]]].
pose Q := (paper_main_trace P)^-1 *: P.
pose S := d%:R *: Q.
have Htr : paper_main_trace S = d%:R.
{ by rewrite /S pms_trace_scale Qtr mulr1. }
have Hd0 : (d%:R : R) != 0 by rewrite (gt_eqF Hdp).
have HE : (d%:R : R) * (kappa*d%:R)^-1 = kappa^-1.
{ by rewrite invfM mulrCA mulfV // mulr1. }
have Hlower : kappa^-1 <= (d%:R : R)*lam.
{ have HH := ler_wpM2l (ltW Hdp) Llo.
  rewrite HE in HH; exact HH. }
have Hdl : (d%:R : R)*lam <= 1.
{ have HL := ler_wpM2l (ltW Hdp) Lhi.
  by rewrite mulfV // in HL. }
have Hupper : (d%:R : R)*(kappa*lam) <= kappa.
{ have HH := ler_wpM2l (ltW Hkp) Hdl.
  rewrite mulr1 in HH; rewrite mulrCA; exact HH. }
have SL : paper_main_loewner_le ((kappa^-1) *: 1%:M) S.
{ apply: (pmh_loewner_trans _ _ ((d%:R*lam) *: 1%:M)).
  - exact: pmh_loewner_scalar Hlower.
  - have H := pmh_loewner_scale _ d%:R _ _ (ltW Hdp) Qlo.
    by rewrite scalerA in H. }
have SU : paper_main_loewner_le S (kappa *: 1%:M).
{ apply: (pmh_loewner_trans _ _ ((d%:R*(kappa*lam)) *: 1%:M)).
  - have H := pmh_loewner_scale _ d%:R _ _ (ltW Hdp) Qhi.
    by rewrite scalerA in H.
  - exact: pmh_loewner_scalar Hupper. }
exists S; split.
- apply: pmh_loewner_psd SL; rewrite invr_ge0; exact: ltW Hkp.
- split.
  + move=> i; rewrite -Htr; apply: paper_main_head_feature_kernel.
    by rewrite /S /Q !paper_main_pairing_scale (Hker i) !mulr0.
  + by split=> //; split.
Qed.

Theorem paper_main_positive_support_conditioned_fit N d kappa
    (x : paper_main_sample N d) :
  (0 < d)%N -> 1 <= kappa ->
  (forall y : 'I_N -> R, \sum_(i < N) y i ^+ 2 = 1 ->
    0 < paper_main_head_support (\sum_(i < N) y i *: paper_main_head_feature x i)
      (paper_main_head_cone_sphere kappa)) ->
  paper_main_conditioned_event N d kappa^-1 kappa x.
Proof.
move=> Hd Hk Hsup.
have [P [HP Hker]] := paper_main_cone_kernel_exists_support d N kappa
  (fun i => paper_main_head_feature x i) Hd Hk Hsup.
exact: paper_main_cone_kernel_conditioned_fit Hd Hk HP Hker.
Qed.

Lemma paper_main_ordinal_unit_extension N (y : 'I_N -> R) :
  \sum_(i < N) y i ^+ 2 = 1 ->
  exists z : nat -> R,
    euclidean_norm z (List.seq 0 N) = 1 /\ forall i : 'I_N, z i = y i.
Proof.
move=> Hy.
pose z := fun i : nat => if insub i is Some j then y j else 0.
have HE : forall i : 'I_N, z i = y i by move=> i; rewrite /z valK.
have Hsq : squared_norm z (List.seq 0 N) = 1.
{ rewrite /squared_norm paper_main_finite_sum_public -Hy.
  by apply: eq_bigr => i _; rewrite HE RpowE. }
exists z; split; last exact HE.
by rewrite /euclidean_norm Hsq; exact: sqrt_1.
Qed.

Theorem paper_main_nat_support_conditioned_fit N d kappa
    (x : paper_main_sample N d) :
  (0 < d)%N -> 1 <= kappa ->
  (forall y : nat -> R, euclidean_norm y (List.seq 0 N) = 1 ->
    0 < paper_main_head_support (paper_main_support_combination d N (paper_main_head_feature x) y)
      (paper_main_head_cone_sphere kappa)) ->
  paper_main_conditioned_event N d kappa^-1 kappa x.
Proof.
move=> Hd Hk Hsup; apply: paper_main_positive_support_conditioned_fit => // y Hy.
have [z [Hz HE]] := paper_main_ordinal_unit_extension N y Hy.
have HC : \sum_(i < N) y i *: paper_main_head_feature x i =
    paper_main_support_combination d N (paper_main_head_feature x) z.
{ rewrite /paper_main_support_combination; apply: eq_bigr => i _; by rewrite HE. }
rewrite HC; exact: Hsup.
Qed.

Theorem paper_main_box_support_conditioned_fit N d lo hi
    (x : paper_main_sample N d) :
  (0 < d)%N -> 0 < lo -> lo <= hi ->
  (forall y : nat -> R, euclidean_norm y (List.seq 0 N) = 1 ->
    exists S : 'M[R]_d,
      paper_main_loewner_le (lo *: 1%:M) S /\
      paper_main_loewner_le S (hi *: 1%:M) /\
      Rlt 0 (paper_main_support_score d N (paper_main_head_feature x) y S)) ->
  paper_main_conditioned_event N d (hi/lo)^-1 (hi/lo) x.
Proof.
move=> Hd Hlo Hhi Hsup.
have Hk : 1 <= hi/lo by rewrite ler_pdivlMr // mul1r.
apply: paper_main_nat_support_conditioned_fit => // y Hy.
have [S [SL [SU HP]]] := Hsup y Hy.
rewrite paper_main_support_score_pairing in HP.
have [_ Hpos] := paper_main_support_cone_sphere d
  (paper_main_support_combination d N (paper_main_head_feature x) y) S lo hi
  (elimT RltP Hlo) SL SU HP.
exact/RltP.
Qed.

Local Open Scope R_scope.

Theorem paper_main_head_tail_conditioned_fit N d (x : paper_main_sample N d)
    (theta a b delta mu A : R) :
  (2 <= d)%coq_nat -> 0 < theta -> 0 < delta -> delta < a -> a <= b -> 0 < mu ->
  (forall J : list nat, NoDup J -> List.incl J (List.seq 0 N) ->
    INR (length J) <= paper_main_head_budget d theta ->
    exists S0 : 'M[R]_d,
      paper_main_loewner_le (a *: 1%:M)%R S0 /\ paper_main_loewner_le S0 (b *: 1%:M)%R /\
      forall i, In i J -> paper_main_pairing (paper_main_head_feature x i) S0 = 0) ->
  (forall J : list nat, NoDup J -> List.incl J (List.seq 0 N) ->
    INR (length J) <= paper_main_head_budget d theta ->
    forall c : nat -> R, (forall i, ~ In i J -> c i = 0) ->
      mu * squared_norm c (List.seq 0 N) <=
        paper_main_frobenius (paper_main_support_combination d N (paper_main_head_feature x) c) ^ 2) ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination d N (paper_main_head_feature x) c) <=
      A * euclidean_norm c (List.seq 0 N)) ->
  (forall J : list nat, NoDup J -> List.incl J (List.seq 0 N) ->
    INR (length J) <= paper_main_head_budget d theta ->
    forall t : nat -> R, euclidean_norm t (List.seq 0 N) = 1 ->
      (forall i, In i J -> t i = 0) ->
      (forall i, Rabs (t i) <= theta / sqrt (INR d)) ->
      exists S : 'M[R]_d,
        paper_main_loewner_le ((a - delta) *: 1%:M)%R S /\
        paper_main_loewner_le S ((b + delta) *: 1%:M)%R /\
        (forall i, In i J -> paper_main_pairing (paper_main_head_feature x i) S = 0) /\
        0 < paper_main_support_score d N (paper_main_head_feature x) t S) ->
  A * (1 / INR d ^ 2) * (b + delta) * sqrt (INR d) < delta * (sqrt mu / 2) ->
  paper_main_conditioned_event N d (((b+delta)/(a-delta))^-1)%R (((b+delta)/(a-delta)))%R x.
Proof.
move=> Hd Htheta Hdelta Hda Hab Hmu Hsec Hgram Hop Htail Hsmall.
have Hd0 : (0 < d)%N by apply/ssrnat.ltP; lia.
have Hlo : (0 < a-delta)%R by apply/RltP; change (0 < a-delta); lra.
have Hhi : (a-delta <= b+delta)%R by apply/RleP; change (a-delta <= b+delta); lra.
apply: paper_main_box_support_conditioned_fit Hd0 Hlo Hhi _.
apply: (paper_main_support_all d N (paper_main_head_feature x) theta a b delta mu A
  Hd Htheta _ Hdelta Hda Hmu Hsec Hgram Hop Htail Hsmall).
move=> i Hi; exact: paper_main_head_feature_symmetric.
Qed.
