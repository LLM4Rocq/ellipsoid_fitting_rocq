From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace OperatorDefinitions
  OperatorProperties TensorDefinitions SymmetricBasis SoftDefinitions MatrixGibbsDefinitions
  MatrixGibbs GradientDefinitions MatrixGradient QuadraticGrowthProofs GoeDefinitions
  GoeSynthesis JointDefinitions JointUniform JointContinuity JointGrowth TimeDefinitions
  JointTimeCalculus.
Import ListNotations.
Import QuadraticGrowthProofs.QuadraticGrowthContinuity.
Open Scope R_scope.

(* Port of the inner module JointValueGrowth of theories/InterpolationProofs.v,
   extracted to build/agent2/unbundled/JointValueGrowth.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundle GoeProofs and its inner module
   GoeSynthesis. This port imports the standalone ported GoeSynthesis, which
   provides goe_scale_positive and goe_matrix_norm_bound.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No lemma is added. The five statements change form in
   the following ways, without a change of meaning.

   1. Derivatives of a function of a real variable. Coquelicot's
      is_derive g t l, for g : R -> V, becomes MathComp's
      @is_derive R R^o V t 1 g l, as in the ported JointTimeCalculus. This
      concerns joint_matrix_scalar_line_derivative (V = matrix_NormedModule n,
      the nested tuples of MatrixDefinitions with the Frobenius norm) and
      joint_soft_line_derivative (V = R^o).

   2. Norms. Coquelicot's norm becomes MathComp's `|.|%R, in
      joint_soft_matrix_growth, joint_matrix_path_norm and
      joint_soft_value_polynomial_regular. On matrix n it is the Frobenius
      norm of the ported MatrixDefinitions, as before.

   3. Joint vectors. The type
        prod_NormedModule R_AbsRing (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      of q becomes
        euclidean_product (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      of MatrixEuclideanProduct, as in the ported JointDefinitions. It keeps
      Coquelicot's product norm, so the bounds (1 + `|q|) ^ 2 mean what
      (1 + norm q) ^ 2 meant, and its topology is the product topology. This
      concerns joint_matrix_path_norm and
      joint_soft_value_polynomial_regular.

   4. Pointwise continuity. Coquelicot's continuous f q becomes MathComp's
      {for q, continuous f}, with the bound variable of f annotated with the
      type of item 3, in joint_soft_value_polynomial_regular. Its statement is
      the one of group 2 of the restated challenge
      ellipsoid_interpolation_time, word for word.

   What changes in the proofs. Coquelicot's is_derive_scal_l with
   is_derive_id becomes joint_time_derive_scale of the ported
   JointTimeCalculus with AnalysisBridge.is_derive_id_R. In
   joint_soft_line_derivative, filterdiff_comp' becomes is_diff_comp, with
   joint_time_is_diff_of_derive of the ported JointTimeCalculus for the line,
   and filterdiff_ext_lin becomes the computation of the derivative through
   deriveE and diff_val, as in the port of joint_soft_time_derivative.
   Stdlib's MVT_cor2, which asks for the derivative on the closed segment,
   becomes AnalysisBridge.MVT_Reals, which asks for it on the open segment
   and for continuity on the closed one; both come from
   joint_soft_line_derivative, the second through
   AnalysisBridge.is_derive_continuity_pt. norm_triangle becomes MathComp's
   ler_normD, and norm_le_prod_norm_1 and norm_le_prod_norm_2 become
   euclidean_product_norm_fst and euclidean_product_norm_snd, through RleP.
   filterdiff_continuous becomes differentiable_continuous applied to the
   differentiability contained in matrix_nested_soft_minimax_frechet, and
   Coquelicot's continuous_comp becomes MathComp's continuous_comp.

   Where norms are compared by lra or nra, every norm is written in this file
   with the same syntax, so that the tactics see the same atoms: a norm that
   comes from unfolding matrix_add or matrix_scale is elaborated through
   other, convertible, canonical instances. So joint_matrix_path_norm states
   the triangle inequality and the scaling of the norm at matrix_add and
   matrix_scale first. It rewrites the scaling at its two arguments
   explicitly, because goe_matrix is itself a matrix_scale.

   Assumptions. joint_soft_line_derivative, joint_soft_matrix_growth and
   joint_soft_value_polynomial_regular mention soft_minimax, whose definition
   uses Stdlib's logarithm Rpower.ln, so they rest on Classical_Prop.classic
   besides the seven axioms of analysis/README.md. The two other statements
   rest on the seven axioms only. Print Assumptions shows both. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac joint_norm_nonneg := apply/RleP; apply normr_ge0.

(* The joint vector space, named for the proofs only. *)
Local Notation joint_space n :=
  (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))).

Lemma joint_matrix_scalar_line_derivative n (A : matrix n) t :
  @is_derive R R^o (matrix_NormedModule n) t 1 (fun u : R => matrix_scale n u A) A.
Proof.
  have HD := @joint_time_derive_scale (matrix_NormedModule n) (fun u => u) t 1 A
    (is_derive_id_R t).
  rewrite scale1r in HD.
  unfold matrix_scale; exact HD.
Qed.

Lemma joint_soft_line_derivative n beta gamma offset coeff Y S (A : matrix n) t :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  @is_derive R R^o R^o t 1
    (fun u=>soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_scale n u A)) Y S)
    (trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S (matrix_scale n t A)) A).
Proof.
  intros Hb Hg HY HS.
  have HP := @joint_time_is_diff_of_derive (matrix_NormedModule n)
    (fun u : R => matrix_scale n u A) t A (joint_matrix_scalar_line_derivative n A t).
  have HF := matrix_nested_soft_minimax_frechet n beta gamma offset coeff Y S
    (matrix_scale n t A) Hb Hg HY HS.
  have HC := is_diff_comp HP HF.
  apply: DeriveDef.
    exact/diff_derivable/ex_diff.
  rewrite deriveE ?diff_val //= scale1r.
  rewrite -matrix_nested_gradient_trace; reflexivity.
Qed.

Theorem joint_soft_matrix_growth n beta gamma offset coeff Y S :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  exists K : R, 0<=K /\ forall A : matrix n,
    Rabs(soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S)<=
    Rabs(soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_zero n)) Y S)+
      K*(`|A|)%R.
Proof.
  intros Hb Hg HY HS.
  destruct (joint_gibbs_uniform n beta gamma offset coeff Y S Hb Hg HY HS)
    as [K0 [K1 [K2 [H0 [H1 [H2 HB]]]]]].
  exists K0; split; [exact H0|]; intro A.
  destruct (MVT_Reals
    (fun u=>soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_scale n u A)) Y S)
    (fun u=>trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S (matrix_scale n u A)) A)
    0 1 ltac:(lra)) as [c [Hc HE]].
  { intros u Hu; apply joint_soft_line_derivative; assumption. }
  { intros u Hu; apply (is_derive_continuity_pt _ u
      (trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S (matrix_scale n u A)) A)).
    apply joint_soft_line_derivative; assumption. }
  cbv beta in HE.
  assert (Hone : matrix_scale n 1 A=A).
  { apply matrix_ext; intros i j Hi Hj; rewrite matrix_entry_scale; ring. }
  assert (Hzero : matrix_scale n 0 A=matrix_zero n).
  { apply matrix_ext; intros i j Hi Hj; rewrite matrix_entry_scale matrix_entry_zero; ring. }
  rewrite Hone Hzero Rminus_0_r Rmult_1_r in HE.
  assert (HD : Rabs (trace_pair n (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_scale n c A)) A)<=K0*(`|A|)%R).
  { rewrite symmetric_trace_pair_comm.
    exact (proj1 (HB (matrix_scale n c A) A (matrix_zero n) (matrix_zero n))). }
  pose proof (Rabs_triang
    (soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S-
     soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_zero n)) Y S)
    (soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_zero n)) Y S)) as H.
  replace (soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S-
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_zero n)) Y S+
    soft_minimax beta gamma (matrix_affine_scores n offset coeff (matrix_zero n)) Y S) with
    (soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S) in H by ring.
  rewrite HE in H; lra.
Qed.

Lemma joint_matrix_path_norm n C t
  (q : euclidean_product (vector_NormedModule n) (vector_NormedModule(goe_vector_index n))) :
  0<=t<=1 ->
  (`|joint_matrix n C t (fst q)(snd q)|)%R<=
    ((`|C|)%R+INR(S n)^2*Rabs(/sqrt(INR(S n)))+goe_scale n*INR(S(goe_vector_index n)))*
      (1+(`|q|)%R)^2.
Proof.
  intro Ht.
  set (CW:=INR(S n)^2*Rabs(/sqrt(INR(S n)))).
  set (CZ:=goe_scale n*INR(S(goe_vector_index n))).
  assert (HW:0<=CW) by(unfold CW;apply Rmult_le_pos;[apply pow2_ge_0|apply Rabs_pos]).
  assert (HZ:0<=CZ) by(unfold CZ;apply Rmult_le_pos;[pose proof(goe_scale_positive n);lra|apply pos_INR]).
  assert (Hq : 0 <= (`|q|)%R) by joint_norm_nonneg.
  assert (Hx : 0 <= (`|fst q|)%R) by joint_norm_nonneg.
  assert (Hz : 0 <= (`|snd q|)%R) by joint_norm_nonneg.
  assert (Hxq : (`|fst q|)%R <= (`|q|)%R)
    by (apply/RleP; apply euclidean_product_norm_fst).
  assert (Hzq : (`|snd q|)%R <= (`|q|)%R)
    by (apply/RleP; apply euclidean_product_norm_snd).
  assert (Hx2 : (1+(`|fst q|)%R)^2 <= (1+(`|q|)%R)^2) by nra.
  assert (Hz2 : (`|snd q|)%R <= (1+(`|q|)%R)^2) by nra.
  pose proof(sqrt_pos t) as Hs;pose proof(sqrt_pos(1-t)) as Hs1.
  pose proof(sqrt_def t ltac:(lra)) as He;pose proof(sqrt_def(1-t)ltac:(lra)) as He1.
  assert (HS : sqrt t<=1) by nra;assert(HS1:sqrt(1-t)<=1) by nra.
  assert(HWB:(`|joint_quadratic_input n(fst q)|)%R<=CW*(1+(`|q|)%R)^2).
  { eapply Rle_trans;[apply joint_quadratic_input_norm|];apply Rmult_le_compat_l;[exact HW|exact Hx2]. }
  assert(HZB:(`|goe_matrix n(snd q)|)%R<=CZ*(1+(`|q|)%R)^2).
  { eapply Rle_trans;[apply goe_matrix_norm_bound|];apply Rmult_le_compat_l;[exact HZ|exact Hz2]. }
  assert (Hadd : forall P Q : matrix n, (`|matrix_add n P Q|)%R <= (`|P|)%R + (`|Q|)%R).
  { intros P Q; unfold matrix_add; apply/RleP; apply ler_normD. }
  assert (Hscale : forall c (P : matrix n), (`|matrix_scale n c P|)%R = Rabs c * (`|P|)%R).
  { intros c P; unfold matrix_scale; apply real_norm_scal_exact. }
  rewrite (joint_matrix_normalized_path n C t (fst q) (snd q) ltac:(lra)).
  eapply Rle_trans;[apply Hadd|].
  eapply Rle_trans;[apply Rplus_le_compat_l; apply Hadd|].
  (* goe_matrix is itself a matrix_scale, so the two rewrites are explicit. *)
  rewrite (Hscale (sqrt t) (joint_quadratic_input n (fst q)))
    (Hscale (sqrt (1-t)) (goe_matrix n (snd q)))
    (Rabs_pos_eq (sqrt t) Hs) (Rabs_pos_eq (sqrt (1-t)) Hs1).
  assert (HC : 0 <= (`|C|)%R) by joint_norm_nonneg.
  assert (HWn : 0 <= (`|joint_quadratic_input n (fst q)|)%R) by joint_norm_nonneg.
  assert (HZn : 0 <= (`|goe_matrix n (snd q)|)%R) by joint_norm_nonneg.
  nra.
Qed.

Theorem joint_soft_value_polynomial_regular n beta gamma offset coeff Y S C :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] ->
  exists K : R, 0<=K /\ forall t,
  (forall q : euclidean_product (vector_NormedModule n) (vector_NormedModule(goe_vector_index n)),
    {for q, continuous (fun p : euclidean_product (vector_NormedModule n) (vector_NormedModule(goe_vector_index n)) =>
      joint_soft_value n beta gamma offset coeff Y S C t (fst p)(snd p))}) /\
  (0<=t<=1 -> forall q : euclidean_product (vector_NormedModule n) (vector_NormedModule(goe_vector_index n)),
    Rabs(joint_soft_value n beta gamma offset coeff Y S C t (fst q)(snd q))<=K*(1+`|q|%R)^2).
Proof.
  intros Hb Hg HY HS;destruct(joint_soft_matrix_growth n beta gamma offset coeff Y S Hb Hg HY HS)as[L[HL HG]].
  set (B:=(`|C|)%R+INR(Datatypes.S n)^2*Rabs(/sqrt(INR(Datatypes.S n)))+
    goe_scale n*INR(Datatypes.S(goe_vector_index n))).
  assert(HB:0<=B).
  { unfold B;assert (HC : 0 <= (`|C|)%R) by joint_norm_nonneg;
      pose proof(pow2_ge_0(INR(Datatypes.S n)));
      pose proof(Rabs_pos(/sqrt(INR(Datatypes.S n))));pose proof(goe_scale_positive n);
      pose proof(pos_INR(Datatypes.S(goe_vector_index n)));nra. }
  exists (Rabs(soft_minimax beta gamma(matrix_affine_scores n offset coeff(matrix_zero n))Y S)+L*B).
  split;[pose proof(Rabs_pos(soft_minimax beta gamma(matrix_affine_scores n offset coeff(matrix_zero n))Y S));nra|].
  intro t;split.
  - intro q;unfold joint_soft_value.
    have HD : differentiable
        ((fun A : matrix n => soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S)
          : matrix n -> R^o) (joint_matrix n C t (fst q) (snd q)).
    { have HF := matrix_nested_soft_minimax_frechet n beta gamma offset coeff Y S
        (joint_matrix n C t (fst q) (snd q)) Hb Hg HY HS.
      by have := HF; case. }
    exact (@continuous_comp (joint_space n) (matrix n) R^o
      (fun p : joint_space n => joint_matrix n C t (fst p) (snd p))
      (fun A : matrix n => soft_minimax beta gamma (matrix_affine_scores n offset coeff A) Y S) q
      (joint_matrix_continuous n C t q) (differentiable_continuous HD)).
  - intros Ht q;unfold joint_soft_value;eapply Rle_trans;[apply HG|].
    pose proof(joint_matrix_path_norm n C t q Ht)as HN.
    assert (Hq : 0 <= (`|q|)%R) by joint_norm_nonneg.
    pose proof(Rabs_pos(soft_minimax beta gamma(matrix_affine_scores n offset coeff(matrix_zero n))Y S));
      fold B in HN;nra.
Qed.
