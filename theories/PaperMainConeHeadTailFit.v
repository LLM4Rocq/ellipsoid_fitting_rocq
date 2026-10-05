(* Cone-section support gives a fixed conditioned fit by the proved head/tail split. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import SoftDefinitions PaperMainMatrixDuality PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainHeadTailSupportSplit PaperMainHeadTailSupportAll PaperMainSupportConditionedFit.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma paper_main_condition_box d kappa (P : 'M[R]_d) :
  paper_main_head_condition kappa P ->
  exists r : R, 0 < r /\
    paper_main_loewner_le (1%:M : 'M[R]_d) (r *: P) /\
    paper_main_loewner_le (r *: P) (kappa *: 1%:M).
Proof.
move=> [lam [Hl [Hlo Hhi]]].
have Hl0 : lam != 0 by rewrite gt_eqF.
have Hli : 0 <= lam^-1 by rewrite invr_ge0; exact: ltW.
exists lam^-1; split; first by rewrite invr_gt0.
split.
- have H := pmh_loewner_scale d lam^-1 _ _ Hli Hlo.
  by rewrite scalerA mulVf // scale1r in H.
- have H := pmh_loewner_scale d lam^-1 _ _ Hli Hhi.
  by rewrite scalerA mulrCA mulVf // mulr1 in H.
Qed.

Lemma paper_main_nat_combination_gram d N (W : nat -> 'M[R]_d) (c : nat -> R) :
  paper_main_frobenius (paper_main_support_combination d N W c) ^+ 2 =
    ((\col_i c i)^T *m paper_main_head_gram (fun i : 'I_N => W i) *m (\col_i c i)) 0 0.
Proof.
have H := paper_main_head_correction_frobenius d N (fun i : 'I_N => W i) (\col_i c i).
rewrite /paper_main_head_correction pmh_frobeniusN in H.
rewrite /paper_main_support_combination.
have E : (\sum_(i < N) (\col_j c j) i 0 *: W i) = \sum_(i < N) c i *: W i.
{ by apply: eq_bigr => i _; rewrite mxE. }
by rewrite E in H.
Qed.

Lemma paper_main_nat_coercive_combination d N (W : nat -> 'M[R]_d) (mu : R) :
  paper_main_head_coercive (paper_main_head_gram (fun i : 'I_N => W i)) mu ->
  forall c : nat -> R,
    Rle (Rmult mu (squared_norm c (List.seq 0 N)))
      (pow (paper_main_frobenius (paper_main_support_combination d N W c)) 2).
Proof.
move=> HG c; apply/RleP; rewrite RmultE RpowE paper_main_nat_combination_gram.
have H := HG (\col_i c i).
have E : (((\col_i c i) : 'cV[R]_N)^T *m (\col_i c i)) 0 0 = squared_norm c (List.seq 0 N).
{ rewrite pmh_vec_dot /squared_norm paper_main_finite_sum_public.
  by apply: eq_bigr => i _; rewrite !mxE RpowE expr2. }
by rewrite E in H.
Qed.

Local Open Scope R_scope.

Theorem paper_main_cone_head_tail_conditioned_fit N d (x : paper_main_sample N d)
    (theta kappa mu A : R) :
  (2 <= d)%coq_nat -> 0 < theta -> 1 <= kappa -> 0 < mu ->
  paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) mu ->
  (forall J : list nat, NoDup J -> List.incl J (List.seq 0 N) ->
    INR (length J) <= paper_main_head_budget d theta ->
    exists P : 'M[R]_d, paper_main_head_condition kappa P /\
      forall i, In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0%R) ->
  (forall c : nat -> R,
    paper_main_frobenius (paper_main_support_combination d N (paper_main_head_feature x) c) <=
      A * euclidean_norm c (List.seq 0 N)) ->
  (forall J : list nat, NoDup J -> List.incl J (List.seq 0 N) ->
    INR (length J) <= paper_main_head_budget d theta ->
    forall t : nat -> R, euclidean_norm t (List.seq 0 N) = 1 ->
      (forall i, In i J -> t i = 0) ->
      (forall i, Rabs (t i) <= theta / sqrt (INR d)) ->
      exists P : 'M[R]_d, paper_main_head_condition kappa P /\
        (forall i, In i J -> paper_main_pairing (paper_main_head_feature x i) P = 0%R) /\
        0 < paper_main_support_score d N (paper_main_head_feature x) t P) ->
  A * (1 / INR d ^ 2) * (kappa + 1/2) * sqrt (INR d) < (1/2) * (sqrt mu / 2) ->
  paper_main_conditioned_event N d (((kappa+1/2)/(1-1/2))^-1)%R
    (((kappa+1/2)/(1-1/2)))%R x.
Proof.
move=> Hd Htheta Hk Hmu HG Hhead Hop Htail Hsmall.
apply: (paper_main_head_tail_conditioned_fit N d x theta 1 kappa (1/2) mu A
  Hd Htheta ltac:(lra) ltac:(lra) Hk Hmu _ _ Hop _ Hsmall).
- move=> J HJ Hin Hlen.
  have [P [HP HK]] := Hhead J HJ Hin Hlen.
  have [r [Hr [Hlo Hhi]]] := paper_main_condition_box d kappa P HP.
  exists (r *: P)%R; split; first by rewrite scale1r.
  split; first exact Hhi.
  move=> i Hi; by rewrite paper_main_pairing_scale (HK i Hi) mulr0.
- move=> J HJ Hin Hlen c Hc.
  exact: paper_main_nat_coercive_combination d N (paper_main_head_feature x) mu HG c.
- move=> J HJ Hin Hlen t Ht Hzero Hcap.
  have [P [HP [HK Hpos]]] := Htail J HJ Hin Hlen t Ht Hzero Hcap.
  have [r [Hr [Hlo Hhi]]] := paper_main_condition_box d kappa P HP.
  exists (r *: P)%R; split.
  + apply: (pmh_loewner_trans d _ (1%:M) _ _ Hlo).
    have HH : ((1-1/2) <= 1 :> R)%R by apply/RleP; change (1-1/2 <= 1); lra.
    have H := pmh_loewner_scalar d _ _ HH; by rewrite scale1r in H.
  + split.
    * apply: (pmh_loewner_trans d _ (kappa *: 1%:M)%R _ Hhi).
      apply: pmh_loewner_scalar; apply/RleP; change (kappa <= kappa+1/2); lra.
    * split.
      -- move=> i Hi; by rewrite paper_main_pairing_scale (HK i Hi) mulr0.
      -- rewrite !paper_main_support_score_pairing paper_main_pairing_scale.
         rewrite paper_main_support_score_pairing in Hpos.
         apply/RltP; rewrite mulr_gt0 //; exact/RltP.
Qed.

Lemma paper_main_cone_head_tail_small_large kappa L c :
  1 <= kappa -> 0 <= L -> 0 < c ->
  exists D, forall d, Nat.le D d ->
    (L*sqrt(INR d)) * (1/(INR d)^2) * (kappa+1/2) * sqrt(INR d) <
      (1/2)*(sqrt(c*INR d)/2).
Proof.
move=> Hk HL Hc.
have Hsc : 0 < sqrt c by exact: sqrt_lt_R0.
have [D HD] := INR_unbounded (1+4*L*(kappa+1/2)/sqrt c).
exists D => d Hdd.
have Hlarge : 1+4*L*(kappa+1/2)/sqrt c < INR d.
{ have := le_INR D d Hdd; lra. }
have Hterm : 0 <= 4*L*(kappa+1/2)/sqrt c.
{ unfold Rdiv; apply Rmult_le_pos; first nra.
  left; exact: Rinv_0_lt_compat. }
have Hd : 0 < INR d by lra.
have Hsq := pow2_sqrt (INR d) (Rlt_le _ _ Hd).
have HE : (L*sqrt(INR d)) * (1/(INR d)^2) * (kappa+1/2) * sqrt(INR d) =
    L*(kappa+1/2)/INR d.
{ replace ((L*sqrt(INR d)) * (1/(INR d)^2) * (kappa+1/2) * sqrt(INR d))
    with (L*(kappa+1/2)*(sqrt(INR d))^2/(INR d)^2) by (unfold Rdiv; ring).
  rewrite Hsq; field; lra. }
rewrite HE.
have Hp := Rmult_lt_compat_r (sqrt c) _ _ Hsc Hlarge.
have Ediv : (1+4*L*(kappa+1/2)/sqrt c)*sqrt c = sqrt c+4*L*(kappa+1/2).
{ field; lra. }
rewrite Ediv in Hp.
have Hfrac : L*(kappa+1/2)/INR d < sqrt c/4.
{ apply Rmult_lt_reg_r with (r := INR d); first exact Hd.
  replace (L*(kappa+1/2)/INR d*INR d) with (L*(kappa+1/2)) by (field; lra).
  nra. }
have Hsqrt : sqrt c <= sqrt(c*INR d).
{ apply sqrt_le_1; nra. }
lra.
Qed.
