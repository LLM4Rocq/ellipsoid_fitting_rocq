(* Port of the inner module FiniteGaussianParameter of
   theories/InterpolationProofs.v, extracted to
   build/agent2/unbundled/FiniteGaussianParameter.v, from Coquelicot to
   MathComp-Analysis.

   The three results keep their names, their arguments in the same order and
   their hypotheses. The arithmetic in every statement is Stdlib's, as in the
   original.

   Statements that change form, without a change of meaning.

   1. Coquelicot's is_derive f x l, for f : R -> R, becomes
      @is_derive R R^o R^o x 1 f l of MathComp-Analysis. This concerns the
      two derivative hypotheses of finite_gaussian_parameter_remainder and
      finite_gaussian_parameter_differentiation, and the last conjunct of
      the conclusion of finite_gaussian_parameter_differentiation. Both
      forms say that (f (x + h) - f x) / h tends to l when h tends to 0
      (is_derive_Reals of AnalysisBridge proves the equivalence of the new
      form with Stdlib's derivable_pt_lim). The text of
      finite_gaussian_parameter_differentiation is that of clause 3.1 of
      analysis/challenges/ellipsoid_interpolation_time/Challenge.v.

   2. The power gaussian_coordinate_weight_moment p^d of
      finite_gaussian_parameter_remainder is written with spaces,
      gaussian_coordinate_weight_moment p ^ d: under MathComp, ^d is a
      token (the dual order notation), so p^d does not parse as a power.
      The term is Stdlib's pow, as before.

   gaussian_iterated_linear_remainder keeps its text.

   The Gaussian notions come from the ported GaussianDefinitions,
   GaussianProductDefinitions, GaussianCoordinateWeightDefinitions and
   JointDefinitions, whose texts are the original ones:
   gaussian_iterated_integrable and gaussian_list_domain ask at each level
   of the iteration for Borel measurability and Lebesgue integrability over
   the line against the kernel, in place of the convergence of an improper
   Riemann integral (difference 4 of analysis/README.md). Under the
   hypotheses of the two theorems every function whose domain or
   expectation is asserted is continuous and bounded by a polynomial, and
   for such functions both readings hold and the values agree.

   Imports. The bundle imported GaussianCoordinateProofs and JointProofs and
   named their inner modules GaussianProduct, GaussianCoordinateMarginals,
   GaussianCoordinatePolynomialContinuity and GaussianBlockExchange through
   them. This port imports the standalone ported modules of the same names,
   in the same order, and AnalysisBridge2 for the MathComp notations and
   is_derive. The Coquelicot import is dropped.

   Proofs. They are the original ones, except that Stdlib's
   "rewrite A, B by tac", which does not parse once ssreflect is loaded,
   is replaced by rewrites with explicit arguments, and the proof of a = a
   is written erefl a, since ssreflect's eq_refl is a lemma about boolean
   equality. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions JointDefinitions ScalarParameterCalculus.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateMarginals
  GaussianCoordinatePolynomialContinuity GaussianBlockExchange.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_iterated_linear_remainder d F G D h :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  gaussian_iterated_integrable d D ->
  gaussian_iterated_expectation d (fun xs=>F xs-G xs-h*D xs) =
    gaussian_iterated_expectation d F-gaussian_iterated_expectation d G-
      h*gaussian_iterated_expectation d D.
Proof.
  intros HF HG HD.
  destruct (gaussian_iterated_scale d G (-1) HG) as [HnG EnG].
  destruct (gaussian_iterated_scale d D (-h) HD) as [HnD EnD].
  destruct (gaussian_iterated_add d F (fun xs=> -1*G xs) HF HnG) as [HFG EFG].
  eapply eq_trans with (gaussian_iterated_expectation d (fun xs=>(F xs+(-1)*G xs)+(-h)*D xs)).
  - apply gaussian_iterated_expectation_ext; intros xs Hxs; ring.
  - rewrite (proj2 (gaussian_iterated_add d _ _ HFG HnD)) EFG EnG EnD; ring.
Qed.

Theorem finite_gaussian_parameter_remainder d (F D D2 : R->list R->R) a rho C p A q B r :
  0<rho ->
  (forall t xs, Rabs(t-a)<=rho -> length xs=d -> @is_derive R R^o R^o t 1 (fun u=>F u xs) (D t xs)) ->
  (forall t xs, Rabs(t-a)<=rho -> length xs=d -> @is_derive R R^o R^o t 1 (fun u=>D u xs) (D2 t xs)) ->
  (forall t, Rabs(t-a)<=rho -> finite_polynomial_bound d C p (D2 t)) ->
  (forall t, Rabs(t-a)<=rho -> finite_joint_continuous d (F t)) ->
  finite_joint_continuous d (D a) ->
  (forall t, Rabs(t-a)<=rho -> finite_polynomial_bound d A q (F t)) ->
  finite_polynomial_bound d B r (D a) ->
  forall b, Rabs(b-a)<=rho ->
  List.Forall (gaussian_list_domain d)
    [F b;F a;D a;(fun xs=>F b xs-F a xs-(b-a)*D a xs)] /\
  Rabs(gaussian_iterated_expectation d (F b)-gaussian_iterated_expectation d (F a)-
    (b-a)*gaussian_iterated_expectation d (D a)) <=
    (C*gaussian_coordinate_weight_moment p ^ d)*Rabs(b-a)^2.
Proof.
  intros Hr HD HD2 HB2 HCF HCD HBF HBD b Hba.
  assert (Haa:Rabs(a-a)<=rho)
    by (rewrite (Rminus_diag_eq a a (erefl a)) Rabs_R0; lra).
  assert (HFdom:forall t, Rabs(t-a)<=rho -> gaussian_list_domain d (F t)).
  { intros t Ht; exact(gaussian_list_domain_polynomial d (F t) A q (HCF t Ht) (HBF t Ht)). }
  assert (HDdom:gaussian_list_domain d (D a)).
  { exact(gaussian_list_domain_polynomial d (D a) B r HCD HBD). }
  set (Rfun:=fun xs=>F b xs-F a xs-(b-a)*D a xs).
  assert (HC:finite_joint_continuous d Rfun).
  { unfold Rfun; apply finite_joint_continuous_minus.
    - apply finite_joint_continuous_minus; [exact(HCF b Hba)|exact(HCF a Haa)].
    - apply finite_joint_continuous_scale; exact HCD. }
  assert (HB:finite_polynomial_bound d (C*Rabs(b-a)^2) p Rfun).
  { split.
    - apply Rmult_le_pos; [exact(proj1(HB2 a Haa))|apply pow2_ge_0].
    - intros xs Hxs; unfold Rfun.
      pose proof(local_second_derivative_remainder
        (fun t=>F t xs) (fun t=>D t xs) (fun t=>D2 t xs) a rho
        (C*gaussian_coordinate_product_weight p xs)
        (fun t Ht=>HD t xs Ht Hxs) (fun t Ht=>HD2 t xs Ht Hxs)
        (fun t Ht=>proj2(HB2 t Ht) xs Hxs) b Hba) as H.
      nra. }
  assert (HRdom:gaussian_list_domain d Rfun).
  { exact(gaussian_list_domain_polynomial d Rfun (C*Rabs(b-a)^2) p HC HB). }
  split.
  - constructor; [exact(HFdom b Hba)|].
    constructor; [exact(HFdom a Haa)|].
    constructor; [exact HDdom|].
    constructor; [exact HRdom|constructor].
  - pose proof(gaussian_iterated_polynomial_expectation_bound d Rfun
      (C*Rabs(b-a)^2) p (proj1 HRdom) HB) as H.
    unfold Rfun in H.
    rewrite (gaussian_iterated_linear_remainder d (F b) (F a) (D a) (b-a)
      (proj1(HFdom b Hba)) (proj1(HFdom a Haa)) (proj1 HDdom)) in H.
    nra.
Qed.

Theorem finite_gaussian_parameter_differentiation d (F D D2 : R->list R->R) a rho C p A q B r :
  0<rho ->
  (forall t xs, Rabs(t-a)<=rho -> length xs=d -> @is_derive R R^o R^o t 1 (fun u=>F u xs) (D t xs)) ->
  (forall t xs, Rabs(t-a)<=rho -> length xs=d -> @is_derive R R^o R^o t 1 (fun u=>D u xs) (D2 t xs)) ->
  (forall t, Rabs(t-a)<=rho -> finite_polynomial_bound d C p (D2 t)) ->
  (forall t, Rabs(t-a)<=rho -> finite_joint_continuous d (F t)) ->
  finite_joint_continuous d (D a) ->
  (forall t, Rabs(t-a)<=rho -> finite_polynomial_bound d A q (F t)) ->
  finite_polynomial_bound d B r (D a) ->
  (forall t, Rabs(t-a)<=rho -> gaussian_list_domain d (F t)) /\
  gaussian_list_domain d (D a) /\
  @is_derive R R^o R^o a 1 (fun t=>gaussian_iterated_expectation d (F t))
    (gaussian_iterated_expectation d (D a)).
Proof.
  intros Hr HD HD2 HB2 HCF HCD HBF HBD.
  split.
  - intros t Ht; exact(gaussian_list_domain_polynomial d (F t) A q (HCF t Ht) (HBF t Ht)).
  - split.
    + exact(gaussian_list_domain_polynomial d (D a) B r HCD HBD).
    + apply quadratic_remainder_derivative with(rho:=rho)(K:=C*gaussian_coordinate_weight_moment p ^ d).
      * exact Hr.
      * intros b Hba; exact(proj2(finite_gaussian_parameter_remainder d F D D2 a rho C p A q B r
          Hr HD HD2 HB2 HCF HCD HBF HBD b Hba)).
Qed.
