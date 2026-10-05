From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  OperatorDefinitions TensorDefinitions SecondChaosDefinitions
  SymmetricDefinitions GradientDefinitions HessianDefinitions
  MatrixThirdDefinitions CoefficientBounds QuadraticDefinitions
  QuadraticGaussianRegular GoeDefinitions GoeSynthesis JointDefinitions
  JointUniform JointContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of the inner module JointGrowth of theories/InterpolationProofs.v
   (also copied in theories/JointProofs.v), extracted to
   build/agent2/unbundled/JointGrowth.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundles QuadraticGaussianProofs and GoeProofs
   and opened their inner modules QuadraticGaussianRegular and GoeSynthesis.
   The port imports these standalone ported modules directly.

   The three statements keep their names, their arguments in the same order
   and their hypotheses. No item is added. They change form in three ways,
   the ways of the ported modules this one imports, and none changes
   meaning.

   1. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. On
      vector n and matrix n the norms are those of the ports of
      OperatorDefinitions and MatrixDefinitions, which nest euclidean_product
      of MatrixEuclideanProduct and keep Coquelicot's Euclidean norm of all
      entries, not MathComp's max norm (difference 1 of analysis/README.md).
      The bounds are stated with Stdlib's order, sum, product, power,
      inverse, sqrt and INR around MathComp's norms, and Rabs stays Stdlib's.
      The constants are unchanged.

   2. Joint vectors. Coquelicot's
        prod_NormedModule R_AbsRing (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      becomes
        euclidean_product (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      as in the ported JointDefinitions and JointContinuity. Its norm is
      Coquelicot's product norm sqrt (norm (fst q) ^ 2 + norm (snd q) ^ 2),
      so the polynomial bounds (1 + norm q) ^ p mean what they meant.

   3. Pointwise continuity. Coquelicot's continuous f q becomes MathComp's
      {for q, continuous f} (difference 5 of analysis/README.md). The bound
      variable of each function is annotated with the joint vector type, so
      that joint_observables_polynomial_regular has the text of group 4 of
      analysis/challenges/ellipsoid_joint/Challenge.v.

   In the proofs, Coquelicot's norm_ge_0 becomes normr_ge0 through RleP,
   norm_le_prod_norm_1 and norm_le_prod_norm_2 become
   euclidean_product_norm_fst and euclidean_product_norm_snd through RleP,
   and Stdlib's "rewrite A, B" becomes an ssreflect rewrite. *)

(* The joint vector space, named for the proofs only. *)
Local Notation joint_space n :=
  (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))).

Lemma joint_quadratic_input_norm n (x : vector n) :
  (`|joint_quadratic_input n x|)%R <=
    (INR (S n)^2 * Rabs (/sqrt (INR (S n)))) * (1+(`|x|)%R)^2.
Proof.
  unfold joint_quadratic_input, quadratic_matrix.
  replace ((INR (S n)^2 * Rabs (/sqrt (INR (S n)))) * (1+(`|x|)%R)^2) with
    (INR (S n)^2 * (Rabs (/sqrt (INR (S n))) * (1+(`|x|)%R)^2)) by ring.
  apply matrix_build_norm_bound.
  - apply Rmult_le_pos; [apply Rabs_pos|apply pow2_ge_0].
  - intros i j Hi Hj; rewrite matrix_entry_zero Rplus_0_l Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos|apply gaussian_centered_coordinate_product_bound].
Qed.

Theorem joint_observables_uniform_growth n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists KP KQ KD KR : R, 0 <= KP /\ 0 <= KQ /\ 0 <= KD /\ 0 <= KR /\
  forall (C : matrix n) (t : R)
    (q : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n))),
  Rabs (joint_quadratic_trace n beta gamma offset coeff Y S C t (fst q) (snd q)) <=
    KP * (1+`|q|%R)^2 /\
  Rabs (joint_goe_trace n beta gamma offset coeff Y S C t (fst q) (snd q)) <=
    KQ * (1+`|q|%R)^1 /\
  Rabs (joint_divergence n beta gamma offset coeff Y S C t (fst q) (snd q)) <=
    KD * (1+`|q|%R)^0 /\
  Rabs (joint_remainder n beta gamma offset coeff Y S C t (fst q) (snd q)) <=
    KR * (1+`|q|%R)^2.
Proof.
  intros Hb Hg HY HS.
  destruct (joint_gibbs_uniform n beta gamma offset coeff Y S Hb Hg HY HS)
    as [K0 [K1 [K2 [H0 [H1 [H2 HB]]]]]].
  set CW := INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n))).
  set CZ := goe_scale n * INR (Datatypes.S (goe_vector_index n)).
  set CR := /2 * INR (Datatypes.S n)^2 * K2 * (2*INR (Datatypes.S n)^2)^3.
  assert (HW : 0 <= CW) by (unfold CW; apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]).
  assert (HZ : 0 <= CZ).
  { unfold CZ; apply Rmult_le_pos; [pose proof (goe_scale_positive n); lra|apply pos_INR]. }
  assert (HR : 0 <= CR).
  { unfold CR; apply Rmult_le_pos.
    - apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|exact H2].
    - apply pow_le; pose proof (pow2_ge_0 (INR (Datatypes.S n))); nra. }
  exists (K0*CW), (K0*CZ), (INR (Datatypes.S (goe_vector_index n))*K1), CR.
  split; [apply Rmult_le_pos; assumption|].
  split; [apply Rmult_le_pos; assumption|].
  split; [apply Rmult_le_pos; [apply pos_INR|exact H1]|].
  split; [exact HR|].
  intros C t q.
  assert (Hq : 0 <= (`|q|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hx : 0 <= (`|fst q|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hz : 0 <= (`|snd q|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hxq : (`|fst q|)%R <= (`|q|)%R)
    by (apply/RleP; apply euclidean_product_norm_fst).
  assert (Hzq : (`|snd q|)%R <= (`|q|)%R)
    by (apply/RleP; apply euclidean_product_norm_snd).
  assert (Hsquare : (1+(`|fst q|)%R)^2 <= (1+(`|q|)%R)^2) by nra.
  split.
  - unfold joint_quadratic_trace.
    destruct (HB (joint_matrix n C t (fst q) (snd q)) (joint_quadratic_input n (fst q))
      (matrix_zero n) (matrix_zero n)) as [HT _].
    eapply Rle_trans; [exact HT|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H0|].
    eapply Rle_trans; [apply joint_quadratic_input_norm|].
    apply Rmult_le_compat_l; [exact HW|exact Hsquare].
  - split.
    + unfold joint_goe_trace.
      destruct (HB (joint_matrix n C t (fst q) (snd q)) (goe_matrix n (snd q))
        (matrix_zero n) (matrix_zero n)) as [HT _].
      eapply Rle_trans; [exact HT|].
      replace (K0 * CZ * (1+(`|q|)%R)^1) with (K0 * (CZ*(1+(`|q|)%R))) by ring.
      apply Rmult_le_compat_l; [exact H0|].
      eapply Rle_trans; [apply goe_matrix_norm_bound|].
      apply Rmult_le_compat_l; [exact HZ|lra].
    + split.
      * unfold joint_divergence; rewrite pow_O Rmult_1_r.
        apply joint_divergence_uniform; [exact H1|].
        intros A U V; destruct (HB A U V (matrix_zero n)) as [_ [H _]]; exact H.
      * unfold joint_remainder.
        eapply Rle_trans.
        -- apply (joint_remainder_uniform n beta gamma offset coeff Y S K2); [exact H2|].
           intros A U V W; destruct (HB A U V W) as [_ [_ H]]; exact H.
        -- apply Rmult_le_compat_l; [exact HR|exact Hsquare].
Qed.

Theorem joint_observables_polynomial_regular n beta gamma offset coeff Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists KP KQ KD KR : R, 0 <= KP /\ 0 <= KQ /\ 0 <= KD /\ 0 <= KR /\
  forall (C : matrix n) (t : R)
    (q : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n))),
  ({for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
      joint_quadratic_trace n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
    Rabs (joint_quadratic_trace n beta gamma offset coeff Y S C t (fst q) (snd q)) <= KP*(1+`|q|%R)^2) /\
  ({for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
      joint_goe_trace n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
    Rabs (joint_goe_trace n beta gamma offset coeff Y S C t (fst q) (snd q)) <= KQ*(1+`|q|%R)^1) /\
  ({for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
      joint_divergence n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
    Rabs (joint_divergence n beta gamma offset coeff Y S C t (fst q) (snd q)) <= KD*(1+`|q|%R)^0) /\
  ({for q, continuous (fun z : euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) =>
      joint_remainder n beta gamma offset coeff Y S C t (fst z) (snd z))} /\
    Rabs (joint_remainder n beta gamma offset coeff Y S C t (fst q) (snd q)) <= KR*(1+`|q|%R)^2).
Proof.
  intros Hb Hg HY HS.
  destruct (joint_observables_uniform_growth n beta gamma offset coeff Y S Hb Hg HY HS)
    as [KP [KQ [KD [KR [HP [HQ [HD [HR HB]]]]]]]].
  exists KP, KQ, KD, KR.
  split; [exact HP|]. split; [exact HQ|]. split; [exact HD|]. split; [exact HR|].
  intros C t q.
  destruct (joint_observables_continuous n beta gamma offset coeff Y S C t Hb Hg HY HS q)
    as [HC1 [HC2 [HC3 HC4]]].
  destruct (HB C t q) as [HB1 [HB2 [HB3 HB4]]].
  split; [split; assumption|].
  split; [split; assumption|].
  split; split; assumption.
Qed.
