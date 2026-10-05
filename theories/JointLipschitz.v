From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions OperatorProperties TensorDefinitions SymmetricBasis
  SoftDefinitions MatrixGibbsDefinitions MatrixGibbs GradientDefinitions
  MatrixGradient GoeDefinitions GoeSynthesis JointDefinitions JointUniform
  JointGrowth TimeDefinitions JointTimeCalculus.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module JointLipschitz of theories/InterpolationProofs.v,
   extracted to build/agent2/unbundled/JointLipschitz.v, from Coquelicot to
   MathComp-Analysis, as a standalone module. The original imports the
   bundle GoeProofs and names GoeProofs.GoeSynthesis through it; this port
   imports the standalone module GoeSynthesis instead. The other imports are
   the ported modules of the same names. AnalysisBridge2 brings the
   MathComp-Analysis libraries and the bridge lemmas.

   Every lemma and theorem of the original keeps its name and its
   arguments, in the same order. No item is added. joint_matrix_path_difference
   keeps its text. The other statements change form in three ways, without
   a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l, for g : R -> V, becomes MathComp's
      @is_derive R R^o V t 1 g l, as in the port of JointTimeCalculus: g is
      derivable at t in the direction 1 and its derivative there is l. Both
      say that (g (t + h) - g t) / h tends to l as h tends to 0 with h <> 0.
      This concerns joint_affine_matrix_line_derivative
      (V = matrix_NormedModule n, the nested tuples of MatrixDefinitions with
      the Frobenius norm) and joint_soft_affine_line_derivative (V = R^o, the
      normed module view of R).

   2. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. On
      matrix n it is the Frobenius norm of the ported MatrixDefinitions, as
      in the original, and not MathComp's max norm (analysis/README.md,
      difference 1). So every bound means the same, constants included. The
      bounds are stated with Stdlib's order, product, sum, power, inverse,
      sqrt, INR and Rabs around MathComp's norms.

   3. Joint vectors. Coquelicot's
        prod_NormedModule R_AbsRing (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      becomes
        euclidean_product (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      of MatrixEuclideanProduct, the type of joint vectors in the ported
      JointDefinitions. It carries Coquelicot's product norm
      sqrt (norm (fst q) ^ 2 + norm (snd q) ^ 2), so (1 + `|q|) ^ 2 is the
      same bound as before. Its elements are pairs, and fst and snd act on
      them as before. This concerns joint_matrix_path_difference_bound and
      joint_soft_value_difference_bound. The latter is, word for word, the
      first clause of group 5 of the restated challenge
      ellipsoid_interpolation_time in analysis/challenges.

   What changes in the proofs. Coquelicot's is_derive_scal_l,
   is_derive_plus and is_derive_const on matrix_NormedModule n become
   joint_time_derive_scale of the ported JointTimeCalculus with
   AnalysisBridge.is_derive_id_R, MathComp's is_deriveD and is_derive_cst.
   Coquelicot's filterdiff_comp' becomes is_diff_comp, fed by
   joint_time_is_diff_of_derive of JointTimeCalculus, and filterdiff_ext_lin
   becomes the computation of the derivative through deriveE and diff_val,
   as in the port of joint_soft_time_derivative. The Frechet derivative of
   the soft value is matrix_nested_soft_minimax_frechet of the ported
   MatrixGibbs, as before. Stdlib's mean value theorem MVT_cor2 is used as in
   the original, with AnalysisBridge.is_derive_Reals in place of Coquelicot's
   is_derive_Reals. Coquelicot's norm_ge_0 and norm_triangle become
   MathComp's normr_ge0 and ler_normD, and norm_le_prod_norm_1 and
   norm_le_prod_norm_2 become euclidean_product_norm_fst and
   euclidean_product_norm_snd of MatrixEuclideanProduct, all read in
   Stdlib's order through RleP; normr_ge0 is used through the local tactic
   joint_norm_nonneg, which is not a lemma and is not visible to importers.
   real_norm_scal_exact is rewritten with explicit arguments, because a bare
   rewrite would also rewrite inside goe_matrix, which is itself a
   matrix_scale. Stdlib's "rewrite A, B" and "rewrite ... by tac" become
   ssreflect rewrites.

   Assumptions. joint_soft_affine_line_derivative,
   joint_soft_matrix_lipschitz and joint_soft_value_difference_bound mention
   soft_minimax, whose definition uses Stdlib's logarithm Rpower.ln, so they
   rest on Classical_Prop.classic besides the seven axioms of
   analysis/README.md. Stdlib's MVT_cor2 also rests on classic, but it is
   used only in joint_soft_matrix_lipschitz, which carries classic through
   its statement anyway. joint_affine_matrix_line_derivative,
   joint_matrix_path_difference and joint_matrix_path_difference_bound rest
   on the seven axioms only. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac joint_norm_nonneg := apply/RleP; apply normr_ge0.

Lemma joint_affine_matrix_line_derivative n (A B : matrix n) t :
  @is_derive R R^o (matrix_NormedModule n) t 1
    (fun u : R => matrix_add n A (matrix_scale n u B)) B.
Proof.
  have HB : @is_derive R R^o (matrix_NormedModule n) t 1
      (fun u : R => matrix_scale n u B) B.
  { have HD := @joint_time_derive_scale (matrix_NormedModule n)
      (fun u => u) t 1 B (is_derive_id_R t).
    unfold matrix_scale.
    rewrite -[X in is_derive _ _ _ X](scale1r B).
    exact HD. }
  have HD := is_deriveD (is_derive_cst (A : matrix_NormedModule n) (t : R^o) 1) HB.
  unfold matrix_add.
  rewrite -[X in is_derive _ _ _ X](add0r B).
  exact HD.
Qed.

Lemma joint_soft_affine_line_derivative n beta gamma offset coeff Y S (A B : matrix n) t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  @is_derive R R^o R^o t 1 (fun u => soft_minimax beta gamma
    (matrix_affine_scores n offset coeff (matrix_add n A (matrix_scale n u B))) Y S)
    (trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n A (matrix_scale n t B))) B).
Proof.
  intros Hb Hg HY HS.
  have HP := @joint_time_is_diff_of_derive (matrix_NormedModule n)
    (fun u : R => matrix_add n A (matrix_scale n u B)) t B
    (joint_affine_matrix_line_derivative n A B t).
  have HF := matrix_nested_soft_minimax_frechet n beta gamma offset coeff Y S
    (matrix_add n A (matrix_scale n t B)) Hb Hg HY HS.
  have HC := is_diff_comp HP HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r.
  rewrite -matrix_nested_gradient_trace; reflexivity.
Qed.

Theorem joint_soft_matrix_lipschitz n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists K : R, 0 <= K /\ forall A B : matrix n,
    Rabs (soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S -
      soft_minimax beta gamma (matrix_affine_scores n offset coeff B) Y S) <=
    K * (`|matrix_add n A (matrix_scale n (-1) B)|)%R.
Proof.
  intros Hb Hg HY HS.
  destruct (joint_gibbs_uniform n beta gamma offset coeff Y S Hb Hg HY HS)
    as [K0 [K1 [K2 [H0 [H1 [H2 HB]]]]]].
  exists K0; split; [exact H0|]; intros A B.
  set (D := matrix_add n A (matrix_scale n (-1) B)).
  destruct (MVT_cor2
    (fun u => soft_minimax beta gamma
      (matrix_affine_scores n offset coeff (matrix_add n B (matrix_scale n u D))) Y S)
    (fun u => trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n B (matrix_scale n u D))) D) 0 1 ltac:(lra)) as [c [HE HC]].
  { intros u Hu; apply is_derive_Reals, joint_soft_affine_line_derivative; assumption. }
  assert (Hone : matrix_add n B (matrix_scale n 1 D) = A).
  { unfold D; apply matrix_ext; intros i j Hi Hj.
    repeat first [rewrite matrix_entry_add | rewrite matrix_entry_scale]; ring. }
  assert (Hzero : matrix_add n B (matrix_scale n 0 D) = B).
  { apply matrix_ext; intros i j Hi Hj.
    rewrite matrix_entry_add matrix_entry_scale; ring. }
  rewrite Hone Hzero Rminus_0_r Rmult_1_r in HE.
  rewrite HE symmetric_trace_pair_comm.
  exact (proj1 (HB (matrix_add n B (matrix_scale n c D)) D (matrix_zero n) (matrix_zero n))).
Qed.

Lemma joint_matrix_path_difference n C s t x z : 0 <= s -> 0 <= t ->
  matrix_add n (joint_matrix n C t x z) (matrix_scale n (-1) (joint_matrix n C s x z)) =
  matrix_add n
    (matrix_scale n (sqrt t - sqrt s) (joint_quadratic_input n x))
    (matrix_scale n (sqrt (1-t) - sqrt (1-s)) (goe_matrix n z)).
Proof.
  intros Hs Ht.
  rewrite (joint_matrix_normalized_path n C t x z Ht)
    (joint_matrix_normalized_path n C s x z Hs).
  apply matrix_ext; intros i j Hi Hj;
    repeat first [rewrite matrix_entry_add | rewrite matrix_entry_scale]; ring.
Qed.

Lemma joint_matrix_path_difference_bound n C s t
  (q : euclidean_product (vector_NormedModule n)
    (vector_NormedModule (goe_vector_index n))) : 0 <= s -> 0 <= t ->
  (`|matrix_add n (joint_matrix n C t (fst q) (snd q))
    (matrix_scale n (-1) (joint_matrix n C s (fst q) (snd q)))|)%R <=
  (INR (S n)^2 * Rabs (/sqrt (INR (S n))) +
    goe_scale n * INR (S (goe_vector_index n))) *
  (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) * (1+(`|q|)%R)^2.
Proof.
  intros Hs Ht.
  set (CW := INR (S n)^2 * Rabs (/sqrt (INR (S n)))).
  set (CZ := goe_scale n * INR (S (goe_vector_index n))).
  assert (HW : 0 <= CW) by (unfold CW; apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]).
  assert (HZ : 0 <= CZ).
  { unfold CZ; apply Rmult_le_pos; [pose proof (goe_scale_positive n); lra|apply pos_INR]. }
  assert (Hq : 0 <= (`|q|)%R) by joint_norm_nonneg.
  assert (Hx : 0 <= (`|fst q|)%R) by joint_norm_nonneg.
  assert (Hz : 0 <= (`|snd q|)%R) by joint_norm_nonneg.
  assert (Hxq : (`|fst q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_fst).
  assert (Hzq : (`|snd q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_snd).
  assert (HWB : (`|joint_quadratic_input n (fst q)|)%R <= (CW+CZ)*(1+(`|q|)%R)^2).
  { eapply Rle_trans; [apply joint_quadratic_input_norm|].
    fold CW; apply Rmult_le_compat; [exact HW|apply pow2_ge_0|lra|nra]. }
  assert (HZB : (`|goe_matrix n (snd q)|)%R <= (CW+CZ)*(1+(`|q|)%R)^2).
  { eapply Rle_trans; [apply goe_matrix_norm_bound|].
    fold CZ; apply Rmult_le_compat; [exact HZ|exact Hz|lra|nra]. }
  rewrite (joint_matrix_path_difference n C s t (fst q) (snd q) Hs Ht).
  unfold matrix_add, matrix_scale.
  eapply Rle_trans; [apply/RleP; apply ler_normD|].
  rewrite (real_norm_scal_exact (sqrt t - sqrt s))
    (real_norm_scal_exact (sqrt (1-t) - sqrt (1-s))).
  eapply Rle_trans.
  - apply Rplus_le_compat; apply Rmult_le_compat_l; try apply Rabs_pos; eassumption.
  - right; ring.
Qed.

Theorem joint_soft_value_difference_bound n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists K : R, 0 <= K /\ forall (C : matrix n) s t
    (q : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n))),
  0 <= s <= 1 -> 0 <= t <= 1 ->
  Rabs (joint_soft_value n beta gamma offset coeff Y S C t (fst q) (snd q) -
    joint_soft_value n beta gamma offset coeff Y S C s (fst q) (snd q)) <=
  K * (Rabs (sqrt t - sqrt s) + Rabs (sqrt (1-t) - sqrt (1-s))) * (1+(`|q|)%R)^2.
Proof.
  intros Hb Hg HY HS.
  destruct (joint_soft_matrix_lipschitz n beta gamma offset coeff Y S Hb Hg HY HS) as [L [HL HB]].
  set (K := INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n))) +
    goe_scale n * INR (Datatypes.S (goe_vector_index n))).
  assert (HK : 0 <= K).
  { unfold K; pose proof (pow2_ge_0 (INR (Datatypes.S n)));
    pose proof (Rabs_pos (/sqrt (INR (Datatypes.S n))));
    pose proof (goe_scale_positive n); pose proof (pos_INR (Datatypes.S (goe_vector_index n))); nra. }
  exists (L*K); split; [apply Rmult_le_pos; assumption|].
  intros C s t q Hs Ht; unfold joint_soft_value.
  eapply Rle_trans; [apply HB|].
  eapply Rle_trans; [apply Rmult_le_compat_l; [exact HL|apply joint_matrix_path_difference_bound; lra]|].
  unfold K; right; ring.
Qed.
