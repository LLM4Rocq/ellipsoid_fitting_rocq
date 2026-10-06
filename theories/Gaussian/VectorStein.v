From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Tensor.Definitions Chaos.SecondOrderDefinitions
  Matrix.VectorListDefinitions Matrix.VectorCoordinates
  Analysis.VectorPartialDerivatives Matrix.VectorCoordinateContinuity
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateDerivativeDefinitions Gaussian.CoordinateStein
  Gaussian.VectorDefinitions Gaussian.VectorPolynomialGrowth
  Gaussian.VectorDomain.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Stein's identities for a standard Gaussian vector x of vector n. The
   function f is differentiable (is_diff), the partial derivatives in the
   identities are continuous, and f and these derivatives are bounded by
   polynomials in `|x|. Write x_i for vector_entry n x i. The expectation
   of df x (chaos_basis n i) is that of x_i * f x
   (gaussian_vector_first_stein). The expectation of
   ddf x (chaos_basis n a) (chaos_basis n b) is that of
   (x_a * x_b - 1) * f x if a = b, and of x_a * x_b * f x otherwise
   (gaussian_vector_second_stein). Both theorems also give
   gaussian_vector_domain for every function involved. *)

(* A function with a Frechet derivative at every point is continuous. *)
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
