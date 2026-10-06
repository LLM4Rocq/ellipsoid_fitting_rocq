(* Exact transport from raw feature Gram edges to the normalized tail map. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductContinuity SoftDefinitions PaperMainMatrixDuality
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometrySeparation PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFeature PaperMainHeadTailSupportSplit PaperMainConeHeadTailFit
  PaperMainGordonProcessCovariance PaperMainGordonBilinear
  PaperMainHeadSectionApprox PaperMainFeatureGramBlocks.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_nat_gram_vector_norm N (y : nat -> R) :
  (((\col_i y i) : 'cV[R]_N)^T *m (\col_i y i)) 0 0 =
    (euclidean_norm y (List.seq 0 N)) ^+ 2.
Proof.
rewrite -RpowE paper_main_gordon_euclidean_squared -paper_main_gordon_squared_norm_dot.
rewrite pmh_vec_dot /squared_norm finite_sum_seqE.
by apply: eq_bigr => i _; rewrite !mxE RpowE expr2.
Qed.

Theorem paper_main_head_gram_operator_bound d N (W : nat -> 'M[R]_d) (L : R) :
  0 <= L ->
  paper_main_loewner_le (paper_main_head_gram (fun i : 'I_N => W i)) ((L^+2) *: 1%:M) ->
  paper_main_head_section_operator_bound N W L.
Proof.
move=> HL [_ HG]; split; first exact HL.
move=> y.
have H := HG (\col_i y i).
rewrite pms_formB paper_main_form_scale pmh_form_id in H.
have HE : paper_main_quadratic_form (paper_main_head_gram (fun i : 'I_N => W i)) (\col_i y i) =
    (((\col_i y i) : 'cV[R]_N)^T *m paper_main_head_gram (fun i : 'I_N => W i) *m (\col_i y i)) 0 0.
{ exact: paper_main_quadratic_formE. }
rewrite HE -paper_main_nat_combination_gram paper_main_nat_gram_vector_norm in H.
have HF := pmh_frobenius_ge0 d (paper_main_support_combination d N W y).
have Hnorm : (0 <= euclidean_norm y (List.seq 0 N))%R by apply/RleP; exact: sqrt_pos.
apply/RleP; move/RleP: HL => HL; move/RleP: HF => HF; move/RleP: Hnorm => Hnorm.
move/RleP: H; rewrite -RminusE -RmultE -!RpowE => H.
change (Rle (paper_main_frobenius (paper_main_support_combination d N W y))
  (Rmult L (euclidean_norm y (List.seq 0 N)))).
change (Rle 0 L) in HL.
change (Rle 0 (paper_main_frobenius (paper_main_support_combination d N W y))) in HF.
change (Rle 0 (euclidean_norm y (List.seq 0 N))) in Hnorm.
change (Rle 0 (L^2 * (euclidean_norm y (List.seq 0 N))^2 -
  (paper_main_frobenius (paper_main_support_combination d N W y))^2)%Rcoq) in H.
have HP := Rmult_le_pos _ _ HL Hnorm.
replace (L^2*(euclidean_norm y (List.seq 0 N))^2)%Rcoq with
  ((L*euclidean_norm y (List.seq 0 N))^2)%Rcoq in H by ring.
nra.
Qed.

Theorem paper_main_raw_feature_coercive N d (x : paper_main_sample N d) c :
  (0 < d)%N ->
  paper_main_head_coercive (paper_main_feature_gram N d x) (c*d%:R^+2)%R ->
  paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) (c*d%:R)%R.
Proof.
move=> Hd HG u.
have HdR : (0 < d%:R :> R) by rewrite ltr0n.
have H := HG u.
rewrite paper_main_feature_gram_head // -/(paper_main_head_gram _) in H.
rewrite -scalemxAr -scalemxAl in H.
rewrite [leRHS]mxE in H.
have E : d%:R * (c*d%:R * (u^T *m u) 0 0) = c*d%:R^+2 * (u^T *m u) 0 0.
{ by rewrite expr2 !mulrA (mulrC d%:R c). }
rewrite -E in H.
by move: H; rewrite ler_pM2l.
Qed.

Theorem paper_main_raw_feature_upper N d (x : paper_main_sample N d) C :
  (0 < d)%N ->
  paper_main_loewner_le (paper_main_feature_gram N d x) ((C*d%:R^+2) *: 1%:M) ->
  paper_main_loewner_le
    (paper_main_head_gram (fun i : 'I_N => paper_main_head_feature x i)) ((C*d%:R) *: 1%:M).
Proof.
move=> Hd HG.
have HdR : (0 < d%:R :> R) by rewrite ltr0n.
have Hd0 : (d%:R : R) != 0 by rewrite gt_eqF.
have HH := pmh_loewner_scale N (d%:R)^-1 _ _ ltac:(by rewrite invr_ge0 ler0n) HG.
rewrite paper_main_feature_gram_head // -/(paper_main_head_gram _) !scalerA mulVf // scale1r in HH.
have E : (d%:R : R)^-1*(C*d%:R^+2) = C*d%:R.
{ by rewrite expr2 mulrCA (mulrA (d%:R)^-1 d%:R d%:R) mulVf // mul1r. }
by rewrite E in HH.
Qed.

Corollary paper_main_raw_feature_operator N d (x : paper_main_sample N d) C :
  (0 < d)%N -> (0 <= C)%Rcoq ->
  paper_main_loewner_le (paper_main_feature_gram N d x) ((C*d%:R^+2) *: 1%:M) ->
  paper_main_head_section_operator_bound N (fun i => paper_main_head_feature x i)
    (sqrt C*sqrt(INR d))%Rcoq.
Proof.
move=> Hd HC HG.
have HH := paper_main_raw_feature_upper N d x C Hd HG.
have HCroot := sqrt_pos C.
have Hdroot := sqrt_pos (INR d).
have HC2 := pow2_sqrt C HC.
have Hd2 := pow2_sqrt (INR d) (pos_INR d).
have HL : (0 <= (sqrt C*sqrt(INR d))%Rcoq)%R.
{ apply/RleP; exact: Rmult_le_pos. }
have E : ((sqrt C*sqrt(INR d))%Rcoq)^+2 = C*d%:R.
{ rewrite -RpowE -INRE -RmultE.
  change ((sqrt C*sqrt(INR d))^2 = C*INR d)%Rcoq.
  replace ((sqrt C*sqrt(INR d))^2)%Rcoq with ((sqrt C)^2*(sqrt(INR d))^2)%Rcoq by ring.
  by rewrite HC2 Hd2. }
apply: paper_main_head_gram_operator_bound HL _.
by rewrite E.
Qed.
