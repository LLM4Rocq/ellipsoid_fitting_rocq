From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions
  SecondChaosDefinitions VectorCoordinateDefinitions VectorCoordinates
  VectorCoordinateCalculus VectorCoordinateContinuity GaussianProductDefinitions
  GaussianProduct GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateStein
  GaussianVectorDefinitions GaussianVectorGrowth GaussianVectorDomain.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module GaussianVectorStein of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/GaussianVectorStein.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundle GaussianCoordinateProofs and named its
   inner modules GaussianProduct and GaussianCoordinateStein through it. The
   port imports the standalone ported modules GaussianProduct and
   GaussianCoordinateStein directly.

   Both theorems keep their names and their arguments, in the same order.
   Their statements change form in four ways, none of which changes their
   meaning. The new forms are those of the vector Stein clauses of the
   restated challenge ellipsoid_gaussian_matrix
   (analysis/challenges/ellipsoid_gaussian_matrix/Challenge.v).

   1. Indices. With ssreflect loaded, (i <= n)%nat would be ssrnat's boolean
      leq. The statements write (i <= n)%coq_nat, which is Stdlib's Peano
      order le, as in the original.

   2. Frechet derivatives. Coquelicot's filterdiff f (locally x) (df x)
      becomes is_diff x (f : vector n -> R^o) (df x) of MathComp-Analysis
      (difference 2 of analysis/README.md): f is differentiable at x and its
      differential 'd f x is df x. Both say that df x is linear and
      continuous and that f (x + h) = f x + df x h + o (h). The cast to R^o
      gives the real line its normed module structure; R^o is R by
      definition, so f and df are unchanged. In the second theorem the same
      change applies to the hypothesis on z |-> df z (chaos_basis n a).

   3. Pointwise continuity. Coquelicot's continuous g x becomes MathComp's
      {for x, continuous g} (difference 5), in the continuity hypotheses on
      the derivatives.

   4. Norms. Coquelicot's norm x becomes MathComp's (`|x|)%R in the
      polynomial bounds. The vectors nest euclidean_product of
      MatrixEuclideanProduct, so this is still the Euclidean norm.

   The meaning of gaussian_vector_domain and gaussian_vector_expectation
   follows the ported GaussianVectorDefinitions (difference 4): Lebesgue
   integrability over the line against the Gaussian kernel at each level of
   the iterated expectation, and Lebesgue integrals. Under the hypotheses of
   each theorem, every function whose domain or expectation is asserted is
   continuous and bounded by a polynomial in the norm, so it is absolutely
   integrable against the kernel and the Lebesgue and improper Riemann
   values agree. The domains are proved in the Lebesgue reading by the
   ported gaussian_vector_polynomial_domain, gaussian_vector_coordinate_domain
   and gaussian_vector_centered_product_domain, and the identities by the
   ported Stein identities of GaussianCoordinateStein.

   What changes in the proofs. Coquelicot's filterdiff_continuous becomes
   MathComp's differentiable_continuous applied to the differentiability
   that is_diff contains, through the one lemma the port adds,
   gaussian_vector_stein_is_diff_continuous. The ported vector_frechet_coordinate_derivative
   takes the is_diff hypotheses as they are. Stdlib's
   "rewrite ... by tac" is written with explicit arguments, since
   ssreflect's rewrite is loaded, and nth is written List.nth. *)

(* Added by the port: a function with a Frechet derivative at every point is
   continuous at every point. This replaces Coquelicot's
   filterdiff_continuous in the two proofs below. *)
Lemma gaussian_vector_stein_is_diff_continuous n (f : vector n -> R)
    (df : vector n -> vector n -> R) :
  (forall x, is_diff x (f : vector n -> R^o) (df x)) ->
  forall x, {for x, continuous f}.
Proof.
  intros HD x.
  have Hd : differentiable (f : vector n -> R^o) x by have := HD x; case.
  exact (differentiable_continuous Hd).
Qed.

Theorem gaussian_vector_first_stein n i (f : vector n -> R)
    (df : vector n -> vector n -> R) C p D q :
  (i <= n)%coq_nat ->
  (forall x, is_diff x (f : vector n -> R^o) (df x)) ->
  (forall x, {for x, continuous (fun z => df z (chaos_basis n i))}) ->
  0 <= C -> 0 <= D ->
  (forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^p) ->
  (forall x, Rabs (df x (chaos_basis n i)) <= D * (1 + (`|x|)%R)^q) ->
  List.Forall (gaussian_vector_domain n)
    [f; (fun x => df x (chaos_basis n i)); (fun x => vector_entry n x i * f x)] /\
  gaussian_vector_expectation n (fun x => df x (chaos_basis n i)) =
    gaussian_vector_expectation n (fun x => vector_entry n x i * f x).
Proof.
  intros Hi HD HCD HC0 HD0 HB HBD.
  assert (HC : forall x, {for x, continuous f}).
  { exact (gaussian_vector_stein_is_diff_continuous n f df HD). }
  split.
  - constructor.
    + apply (gaussian_vector_polynomial_domain n f C p); assumption.
    + constructor.
      * apply (gaussian_vector_polynomial_domain n _ D q); assumption.
      * constructor; [|constructor].
        apply (gaussian_vector_coordinate_domain n i f C p); assumption.
  - unfold gaussian_vector_expectation.
    eapply eq_trans.
    + exact (gaussian_iterated_coordinate_first_stein n i _ _ C p D q Hi
        (vector_continuous_joint n f HC)
        (vector_continuous_joint n _ HCD)
        (vector_polynomial_bound_pullback n C p f HC0 HB)
        (vector_polynomial_bound_pullback n D q _ HD0 HBD)
        (vector_frechet_coordinate_derivative n i f df Hi HD)).
    + apply gaussian_iterated_expectation_ext; intros xs Hxs.
      rewrite (vector_entry_of_list n xs i Hi); reflexivity.
Qed.

Theorem gaussian_vector_second_stein n a b (f : vector n -> R)
    (df : vector n -> vector n -> R) (ddf : vector n -> vector n -> vector n -> R)
    C p D q E r :
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  (forall x, is_diff x (f : vector n -> R^o) (df x)) ->
  (forall x, is_diff x ((fun z => df z (chaos_basis n a)) : vector n -> R^o)
    (ddf x (chaos_basis n a))) ->
  (forall x, {for x, continuous (fun z => ddf z (chaos_basis n a) (chaos_basis n b))}) ->
  0 <= C -> 0 <= D -> 0 <= E ->
  (forall x, Rabs (f x) <= C * (1 + (`|x|)%R)^p) ->
  (forall x, Rabs (df x (chaos_basis n a)) <= D * (1 + (`|x|)%R)^q) ->
  (forall x, Rabs (ddf x (chaos_basis n a) (chaos_basis n b)) <= E * (1 + (`|x|)%R)^r) ->
  List.Forall (gaussian_vector_domain n)
    [f; (fun x => df x (chaos_basis n a));
     (fun x => ddf x (chaos_basis n a) (chaos_basis n b));
     (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) * f x)] /\
  gaussian_vector_expectation n (fun x => ddf x (chaos_basis n a) (chaos_basis n b)) =
    gaussian_vector_expectation n
      (fun x => (vector_entry n x a * vector_entry n x b - if Nat.eqb a b then 1 else 0) * f x).
Proof.
  intros Ha Hb HD HDD HCDD HC0 HD0 HE0 HB0 HB1 HB2.
  assert (HC : forall x, {for x, continuous f}).
  { exact (gaussian_vector_stein_is_diff_continuous n f df HD). }
  assert (HCD : forall x, {for x, continuous (fun z => df z (chaos_basis n a))}).
  { exact (gaussian_vector_stein_is_diff_continuous n _
      (fun x => ddf x (chaos_basis n a)) HDD). }
  split.
  - constructor.
    + apply (gaussian_vector_polynomial_domain n f C p); assumption.
    + constructor.
      * apply (gaussian_vector_polynomial_domain n _ D q); assumption.
      * constructor.
        -- apply (gaussian_vector_polynomial_domain n _ E r); assumption.
        -- constructor; [|constructor].
           apply (gaussian_vector_centered_product_domain n a b f C p); assumption.
  - pose proof (vector_frechet_coordinate_derivative n a f df Ha HD) as Hfirst.
    pose proof (vector_frechet_coordinate_derivative n b _
      (fun x => ddf x (chaos_basis n a)) Hb HDD) as Hsecond.
    pose proof (vector_continuous_joint n f HC) as HCF.
    pose proof (vector_continuous_joint n _ HCD) as HCDF.
    pose proof (vector_continuous_joint n _ HCDD) as HCDDF.
    pose proof (vector_polynomial_bound_pullback n C p f HC0 HB0) as HBF.
    pose proof (vector_polynomial_bound_pullback n D q _ HD0 HB1) as HBDF.
    pose proof (vector_polynomial_bound_pullback n E r _ HE0 HB2) as HBDDF.
    unfold gaussian_vector_expectation.
    destruct (Nat.eq_dec a b) as [He|Hne].
    + subst b; rewrite Nat.eqb_refl.
      eapply eq_trans.
      * exact (gaussian_iterated_coordinate_second_stein n a _ _ _ C p D q E r
          Ha HCF HCDDF HBF HBDF HBDDF Hfirst Hsecond).
      * apply gaussian_iterated_expectation_ext; intros xs Hxs.
        rewrite (vector_entry_of_list n xs a Ha); reflexivity.
    + assert (He : Nat.eqb a b = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite He; eapply eq_trans.
      * exact (gaussian_iterated_coordinate_mixed_stein n b a _ _ _ C p D q E r
          Hb Ha ltac:(congruence) HCF HCDF HCDDF HBF HBDF HBDDF Hfirst Hsecond).
      * apply gaussian_iterated_expectation_ext; intros xs Hxs.
        rewrite (vector_entry_of_list n xs a Ha) (vector_entry_of_list n xs b Hb); ring.
Qed.
