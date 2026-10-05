From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates MatrixTrace
  GradientDefinitions MatrixGradient OperatorDefinitions SecondChaosDefinitions
  SymmetricDefinitions NormEquivalence GaussianVectorDefinitions GoeDefinitions
  GoePairs GoeSynthesis AffineGaussianGibbs AffineGaussianRegular
  GaussianVectorDomain GaussianVectorAlgebra GaussianVectorFinite.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module GoeGibbs of theories/InterpolationProofs.v (also
   copied in GoeProofs.v and JointProofs.v), extracted to
   build/agent2/unbundled/GoeGibbs.v, from Coquelicot to MathComp-Analysis,
   as a standalone module.

   The original imported the bundle GaussianVectorProofs and named its inner
   modules GaussianVectorDomain, GaussianVectorAlgebra and
   GaussianVectorFinite through it. The port imports these standalone ported
   modules directly.

   The four statements keep their names, their arguments in the same order
   and their hypotheses. No item is added. One statement changes form, and
   none changes its meaning.

   1. Order on indices. With ssreflect loaded, (k <= n)%nat would mean
      ssrnat's boolean leq. The original means Stdlib's Peano order le, so
      the hypothesis of goe_gibbs_coordinate_derivative is written
      (k <= goe_vector_index n)%coq_nat, which is Stdlib's le, as in the
      ported goe_matrix_coordinate_direction of GoeSynthesis.

   The other statements keep the text of the original. Their meaning changes
   only through the ported definitions they mention: gaussian_vector_domain
   and gaussian_vector_expectation follow the ported
   GaussianVectorDefinitions (difference 4 of analysis/README.md), that is
   Lebesgue integrability against the Gaussian kernel at each level of the
   iterated expectation, and Lebesgue integrals. The functions of the
   statements are continuous and bounded by a polynomial in the Euclidean
   norm of the vector (by the ported AffineGaussianRegular), so they are
   absolutely integrable against the kernel, and the Lebesgue and improper
   Riemann values agree. The statement of goe_gibbs_matrix_stein is the text
   of the clause "GOE matrix integration by parts and separate domains" of
   the restated challenge ellipsoid_goe.

   What changes in the proofs. In goe_gibbs_coordinate_derivative, the
   original uses Coquelicot's linear_scal twice: for the derivative of
   matrix_nested_gradient, whose linearity it takes from proj1 of
   Coquelicot's filterdiff, and for trace_pair. The port takes the first
   from the ported matrix_nested_gradient_frechet: the derivative is the
   differential 'd f A of MathComp (the field diff_val of is_diff), which is
   a linear map, so linearZ applies. The second is trace_pair_scale of
   MatrixTrace. Stdlib's "rewrite A, B" and "rewrite ... by tac" are written
   in the form that ssreflect accepts. *)

Lemma goe_gibbs_coordinate_derivative n beta gamma offset coeff Y S C r k z :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> (k <= goe_vector_index n)%coq_nat ->
  trace_pair n (goe_basis n k)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z)))
      (matrix_scale n r (goe_matrix n (chaos_basis (goe_vector_index n) k)))) =
  (r * goe_scale n) * trace_pair n (goe_basis n k)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))) (goe_basis n k)).
Proof.
  intros Hb Hg HY HS Hk.
  rewrite (goe_matrix_coordinate_direction n k Hk).
  set A := matrix_add n C (matrix_scale n r (goe_matrix n z)).
  have HD := matrix_nested_gradient_frechet n beta gamma offset coeff Y S Hb Hg HY HS A.
  have [_ Hv] := HD.
  (* Coquelicot's linear_scal for the derivative of matrix_nested_gradient,
     which is the linear differential 'd f A of MathComp. *)
  have HZ : forall (c : R) (M : matrix n),
    matrix_nested_gradient_derivative n beta gamma offset coeff Y S A (matrix_scale n c M) =
    matrix_scale n c (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A M).
  { intros c M; unfold matrix_scale; rewrite -Hv; exact: linearZ. }
  rewrite (HZ r) (HZ (goe_scale n)) !trace_pair_scale; ring.
Qed.

Theorem goe_gibbs_weighted_sum n beta gamma offset coeff Y S C r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_vector_domain (goe_vector_index n)
    (fun z => coordinate_sum (goe_vector_index n) (fun k =>
      vector_entry (goe_vector_index n) z k * trace_pair n (goe_basis n k)
        (matrix_nested_gradient n beta gamma offset coeff Y S
          (matrix_add n C (matrix_scale n r (goe_matrix n z)))))) /\
  gaussian_vector_expectation (goe_vector_index n)
    (fun z => coordinate_sum (goe_vector_index n) (fun k =>
      vector_entry (goe_vector_index n) z k * trace_pair n (goe_basis n k)
        (matrix_nested_gradient n beta gamma offset coeff Y S
          (matrix_add n C (matrix_scale n r (goe_matrix n z)))))) =
  coordinate_sum (goe_vector_index n) (fun k => gaussian_vector_expectation (goe_vector_index n)
    (fun z => vector_entry (goe_vector_index n) z k * trace_pair n (goe_basis n k)
      (matrix_nested_gradient n beta gamma offset coeff Y S
        (matrix_add n C (matrix_scale n r (goe_matrix n z)))))).
Proof.
  intros Hb Hg HY HS.
  apply (gaussian_vector_polynomial_sum_domain (goe_vector_index n) (goe_vector_index n) 1).
  - intros k Hk; apply (proj1 (affine_gaussian_weighted_trace_regular n (goe_vector_index n)
      beta gamma offset coeff Y S (goe_matrix n) C r (goe_basis n k) k Hb Hg HY HS (goe_matrix_linear n))).
  - intros k Hk; apply (proj2 (affine_gaussian_weighted_trace_regular n (goe_vector_index n)
      beta gamma offset coeff Y S (goe_matrix n) C r (goe_basis n k) k Hb Hg HY HS (goe_matrix_linear n))).
Qed.

Theorem goe_gibbs_direction_sum n beta gamma offset coeff Y S C r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_vector_domain (goe_vector_index n)
    (fun z => coordinate_sum (goe_vector_index n) (fun k =>
      trace_pair n (goe_basis n k) (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (matrix_add n C (matrix_scale n r (goe_matrix n z))) (goe_basis n k)))) /\
  gaussian_vector_expectation (goe_vector_index n)
    (fun z => coordinate_sum (goe_vector_index n) (fun k =>
      trace_pair n (goe_basis n k) (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (matrix_add n C (matrix_scale n r (goe_matrix n z))) (goe_basis n k)))) =
  coordinate_sum (goe_vector_index n) (fun k => gaussian_vector_expectation (goe_vector_index n)
    (fun z => trace_pair n (goe_basis n k) (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))) (goe_basis n k)))).
Proof.
  intros Hb Hg HY HS.
  apply (gaussian_vector_polynomial_sum_domain (goe_vector_index n) (goe_vector_index n) 0).
  - intros k Hk; apply (proj1 (affine_gaussian_direction_trace_regular n (goe_vector_index n)
      beta gamma offset coeff Y S (goe_matrix n) C r (goe_basis n k) (goe_basis n k)
      Hb Hg HY HS (goe_matrix_linear n))).
  - intros k Hk; apply (proj2 (affine_gaussian_direction_trace_regular n (goe_vector_index n)
      beta gamma offset coeff Y S (goe_matrix n) C r (goe_basis n k) (goe_basis n k)
      Hb Hg HY HS (goe_matrix_linear n))).
Qed.

Theorem goe_gibbs_matrix_stein n beta gamma offset coeff Y S C r :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  List.Forall (gaussian_vector_domain (goe_vector_index n))
    [(fun z => trace_pair n (goe_matrix n z) (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z)))));
     (fun z => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
       (matrix_add n C (matrix_scale n r (goe_matrix n z)))))] /\
  gaussian_vector_expectation (goe_vector_index n)
    (fun z => trace_pair n (goe_matrix n z) (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))))) =
  (2 * r / INR (Datatypes.S n)) * gaussian_vector_expectation (goe_vector_index n)
    (fun z => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))))).
Proof.
  intros Hb Hg HY HS.
  set (f := fun k z => vector_entry (goe_vector_index n) z k * trace_pair n (goe_basis n k)
    (matrix_nested_gradient n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))))).
  set (h := fun k z => trace_pair n (goe_basis n k)
    (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))) (goe_basis n k))).
  destruct (goe_gibbs_weighted_sum n beta gamma offset coeff Y S C r Hb Hg HY HS) as [HF EF].
  destruct (goe_gibbs_direction_sum n beta gamma offset coeff Y S C r Hb Hg HY HS) as [HH EH].
  change (gaussian_vector_domain (goe_vector_index n) (fun z => coordinate_sum (goe_vector_index n) (fun k => f k z))) in HF.
  change (gaussian_vector_domain (goe_vector_index n) (fun z => coordinate_sum (goe_vector_index n) (fun k => h k z))) in HH.
  assert (HI : forall k, (k <= goe_vector_index n)%coq_nat ->
    gaussian_vector_domain (goe_vector_index n) (h k)).
  { intros k Hk.
    destruct (affine_gaussian_direction_trace_regular n (goe_vector_index n)
      beta gamma offset coeff Y S (goe_matrix n) C r (goe_basis n k) (goe_basis n k)
      Hb Hg HY HS (goe_matrix_linear n)) as [HC [K [HK HB]]].
    apply (gaussian_vector_polynomial_domain (goe_vector_index n) (h k) K 0); assumption. }
  assert (HE : forall k, (k <= goe_vector_index n)%coq_nat ->
    gaussian_vector_expectation (goe_vector_index n) (f k) =
      (r*goe_scale n)*gaussian_vector_expectation (goe_vector_index n) (h k)).
  { intros k Hk.
    destruct (affine_gaussian_trace_stein n (goe_vector_index n) beta gamma offset coeff Y S
      (goe_matrix n) C r (goe_basis n k) k Hb Hg HY HS (goe_matrix_linear n) Hk) as [_ HE].
    eapply eq_trans; [symmetry; exact HE|].
    transitivity (gaussian_vector_expectation (goe_vector_index n) (fun z => (r*goe_scale n)*h k z)).
    - apply gaussian_vector_expectation_ext; intro z; apply goe_gibbs_coordinate_derivative; assumption.
    - apply (proj2 (gaussian_vector_scale (goe_vector_index n) (h k) (r*goe_scale n) (proj1 (HI k Hk)))). }
  assert (HD : forall z,
    symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z)))) =
    coordinate_sum (goe_vector_index n) (fun k => h k z)).
  { intro z; symmetry; apply goe_basis_divergence. }
  assert (ET : gaussian_vector_expectation (goe_vector_index n)
    (fun z => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
      (matrix_add n C (matrix_scale n r (goe_matrix n z))))) =
    gaussian_vector_expectation (goe_vector_index n) (fun z => coordinate_sum (goe_vector_index n) (fun k => h k z))).
  { apply gaussian_vector_expectation_ext; exact HD. }
  split.
  - constructor.
    + eapply gaussian_vector_domain_ext.
      * intro z; symmetry; apply goe_matrix_trace.
      * apply gaussian_vector_domain_scale; exact HF.
    + constructor; [|constructor].
      eapply gaussian_vector_domain_ext; [intro z; symmetry; apply HD|exact HH].
  - transitivity (goe_scale n * gaussian_vector_expectation (goe_vector_index n)
      (fun z => coordinate_sum (goe_vector_index n) (fun k => f k z))).
    + transitivity (gaussian_vector_expectation (goe_vector_index n)
        (fun z => goe_scale n * coordinate_sum (goe_vector_index n) (fun k => f k z))).
      * apply gaussian_vector_expectation_ext; intro z; apply goe_matrix_trace.
      * exact (proj2 (gaussian_vector_scale (goe_vector_index n) _ (goe_scale n) (proj1 HF))).
    + change (gaussian_vector_expectation (goe_vector_index n) (fun z => coordinate_sum (goe_vector_index n) (fun k => f k z)) =
        coordinate_sum (goe_vector_index n) (fun k => gaussian_vector_expectation (goe_vector_index n) (f k))) in EF.
      rewrite EF.
      transitivity (goe_scale n * ((r*goe_scale n) * coordinate_sum (goe_vector_index n)
        (fun k => gaussian_vector_expectation (goe_vector_index n) (h k)))).
      * f_equal; transitivity (coordinate_sum (goe_vector_index n) (fun k =>
          (r*goe_scale n)*gaussian_vector_expectation (goe_vector_index n) (h k))).
        -- apply coordinate_sum_ext; exact HE.
        -- apply normeq_coordinate_sum_scale.
      * change (gaussian_vector_expectation (goe_vector_index n) (fun z => coordinate_sum (goe_vector_index n) (fun k => h k z)) =
          coordinate_sum (goe_vector_index n) (fun k => gaussian_vector_expectation (goe_vector_index n) (h k))) in EH.
        rewrite -EH -ET.
        replace (goe_scale n * (r*goe_scale n * gaussian_vector_expectation (goe_vector_index n)
          (fun z => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
            (matrix_add n C (matrix_scale n r (goe_matrix n z))))))) with
          ((goe_scale n * goe_scale n)*r * gaussian_vector_expectation (goe_vector_index n)
          (fun z => symmetric_divergence n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
            (matrix_add n C (matrix_scale n r (goe_matrix n z)))))) by ring.
        rewrite goe_scale_square; unfold Rdiv; ring.
Qed.
