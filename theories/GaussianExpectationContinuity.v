(* Continuity of an iterated Gaussian expectation in a real parameter b that
   ranges over a set D. Each level of the expectation is a Lebesgue integral
   over the line.
   - gaussian_iterated_difference_bound: if F and G are integrable and
     F - G has the polynomial bound C, p, then the expectations of F and G
     differ by at most C * (gaussian_coordinate_weight_moment p) ^ d.
   - gaussian_iterated_local_admissible_within: if F a has a polynomial
     bound and, for b in D near a, F b is jointly continuous and
     |F b - F a| <= (1 + |x_1|)^p ... (1 + |x_d|)^p, then F b has an
     expectation for b in D near a, with a uniform bound.
   - gaussian_iterated_expectation_continuous_within: if moreover, for
     every eps > 0, F b - F a has the polynomial bound eps, p for b in D
     near a, then the expectation of F b tends to that of F a as b tends
     to a within D. gaussian_iterated_expectation_continuous_modulus_within
     takes the bound c b, for a function c continuous at a with c a = 0.
   The limit within D, (f @ within D (nbhs a) --> l)%classic, says: for every
   eps > 0 there is delta > 0 such that |f b - l| < eps for every b of D with
   |b - a| < delta. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateWeights
  GaussianCoordinateMarginals GaussianCoordinatePolynomialContinuity.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_iterated_difference d F G :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  gaussian_iterated_integrable d (fun xs => F xs-G xs) /\
  gaussian_iterated_expectation d (fun xs => F xs-G xs) =
    gaussian_iterated_expectation d F-gaussian_iterated_expectation d G.
Proof.
  intros HF HG.
  destruct (gaussian_iterated_scale d G (-1) HG) as [HGI HGE].
  destruct (gaussian_iterated_add d F (fun xs => -1*G xs) HF HGI) as [HI HE].
  assert (Hfun : (fun xs => F xs+-1*G xs) = (fun xs => F xs-G xs)).
  { apply functional_extensionality; intro xs; ring. }
  rewrite -> Hfun in HI; rewrite -> Hfun in HE; rewrite -> HGE in HE.
  split; [exact HI|lra].
Qed.

Theorem gaussian_iterated_difference_bound d F G C p :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  finite_polynomial_bound d C p (fun xs => F xs-G xs) ->
  Rabs (gaussian_iterated_expectation d F-gaussian_iterated_expectation d G) <=
    C*gaussian_coordinate_weight_moment p ^ d.
Proof.
  intros HF HG Hb.
  destruct (gaussian_iterated_difference d F G HF HG) as [HI HE].
  rewrite <- HE; exact (gaussian_iterated_polynomial_expectation_bound d _ C p HI Hb).
Qed.

Lemma finite_polynomial_bound_from_difference d F G C D p q :
  finite_polynomial_bound d C p G ->
  finite_polynomial_bound d D q (fun xs => F xs-G xs) ->
  finite_polynomial_bound d (C+D) (p+q)%coq_nat F.
Proof.
  intros HG HD.
  pose proof (finite_polynomial_bound_degree_monotone d C p (p+q)%coq_nat G HG
    ltac:(lia)) as HG'.
  pose proof (finite_polynomial_bound_degree_monotone d D q (p+q)%coq_nat
    (fun xs => F xs-G xs) HD ltac:(lia)) as HD'.
  pose proof (finite_polynomial_bound_add d C D (p+q)%coq_nat G
    (fun xs => F xs-G xs) HG' HD') as H.
  cbn beta in H.
  replace (fun xs => G xs+(F xs-G xs)) with F in H; [exact H|].
  apply functional_extensionality; intro xs; ring.
Qed.

Theorem gaussian_iterated_local_admissible_within d (F : R -> list R -> R)
    (D : R -> Prop) a C q p :
  finite_polynomial_bound d C q (F a) ->
  (exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    finite_joint_continuous d (F b)) ->
  (exists delta, 0<delta /\ forall b, D b -> Rabs (b-a)<delta ->
    finite_polynomial_bound d 1 p (fun xs => F b xs-F a xs)) ->
  exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    gaussian_iterated_integrable d (F b) /\
    gaussian_iterated_absolutely_integrable d (F b) /\
    gaussian_iterated_has_expectation d (F b) (gaussian_iterated_expectation d (F b)) /\
    gaussian_iterated_has_expectation d (fun xs => Rabs (F b xs))
      (gaussian_iterated_expectation d (fun xs => Rabs (F b xs))) /\
    Rabs (gaussian_iterated_expectation d (F b)) <=
      (C+1)*gaussian_coordinate_weight_moment (q+p)%coq_nat ^ d.
Proof.
  intros Hb [eta [Heta HC]] [delta [Hdelta HD]].
  exists (Rmin eta delta); split; [apply Rmin_pos; assumption|].
  intros b Db Hnear.
  apply (gaussian_iterated_polynomial_admissible d (F b) (C+1) (q+p)%coq_nat).
  - apply HC; [exact Db|].
    eapply Rlt_le_trans; [exact Hnear|apply Rmin_l].
  - apply (finite_polynomial_bound_from_difference d (F b) (F a) C 1 q p Hb).
    apply HD; [exact Db|].
    eapply Rlt_le_trans; [exact Hnear|apply Rmin_r].
Qed.

Theorem gaussian_iterated_expectation_continuous_within d
    (F : R -> list R -> R) (D : R -> Prop) a C q p :
  D a -> finite_polynomial_bound d C q (F a) ->
  (exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    finite_joint_continuous d (F b)) ->
  (forall epsilon, 0<epsilon -> exists delta, 0<delta /\
    forall b, D b -> Rabs (b-a)<delta ->
      finite_polynomial_bound d epsilon p (fun xs => F b xs-F a xs)) ->
  ((fun b => gaussian_iterated_expectation d (F b)) @ within D (nbhs a) -->
    gaussian_iterated_expectation d (F a))%classic /\
  exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    gaussian_iterated_integrable d (F b) /\
    gaussian_iterated_absolutely_integrable d (F b) /\
    gaussian_iterated_has_expectation d (F b) (gaussian_iterated_expectation d (F b)) /\
    gaussian_iterated_has_expectation d (fun xs => Rabs (F b xs))
      (gaussian_iterated_expectation d (fun xs => Rabs (F b xs))) /\
    Rabs (gaussian_iterated_expectation d (F b)) <=
      (C+1)*gaussian_coordinate_weight_moment (q+p)%coq_nat ^ d.
Proof.
  intros Da Hb HC HD.
  pose proof (gaussian_iterated_local_admissible_within d F D a C q p
    Hb HC (HD 1 ltac:(lra))) as Hlocal.
  split; [|exact Hlocal].
  destruct Hlocal as [eta [Heta HI]].
  assert (Ha : Rabs (a-a)<eta).
  { replace (a-a) with 0 by ring; rewrite Rabs_R0; exact Heta. }
  pose proof (proj1 (HI a Da Ha)) as HIa.
  set (M := gaussian_coordinate_weight_moment p ^ d).
  assert (HM : 0<M).
  { unfold M; apply pow_lt; pose proof (gaussian_coordinate_weight_moment_at_least_one p); lra. }
  intros A HA; apply nbhs_Reals in HA; destruct HA as [eps [Heps HA]].
  assert (Hsmall : 0<eps/(2*M)) by (apply Rdiv_lt_0_compat; nra).
  destruct (HD (eps/(2*M)) Hsmall) as [delta [Hdelta Hbound]].
  assert (Hmin : 0<Rmin eta delta) by (apply Rmin_pos; assumption).
  change (nbhs a (fun b => D b -> A (gaussian_iterated_expectation d (F b)))).
  apply nbhs_Reals; exists (Rmin eta delta); split; [exact Hmin|].
  intros b Hnear Db; apply HA.
  assert (Hbe : Rabs (b-a)<eta) by (eapply Rlt_le_trans; [exact Hnear|apply Rmin_l]).
  assert (Hbd : Rabs (b-a)<delta) by (eapply Rlt_le_trans; [exact Hnear|apply Rmin_r]).
  eapply Rle_lt_trans.
  - exact (gaussian_iterated_difference_bound d (F b) (F a) _ p
      (proj1 (HI b Db Hbe)) HIa (Hbound b Db Hbd)).
  - fold M; replace (eps/(2*M)*M) with (eps/2) by (field; lra); lra.
Qed.

Lemma gaussian_iterated_weighted_modulus_within d (F : R -> list R -> R)
    (D : R -> Prop) a p c :
  {for a, continuous c} -> c a=0 ->
  (exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    finite_polynomial_bound d (c b) p (fun xs => F b xs-F a xs)) ->
  forall epsilon, 0<epsilon -> exists delta, 0<delta /\
    forall b, D b -> Rabs (b-a)<delta ->
      finite_polynomial_bound d epsilon p (fun xs => F b xs-F a xs).
Proof.
  intros Hc Hca [eta [Heta Hb]] eps Heps.
  destruct (proj1 (continuous_Reals c a) Hc eps Heps) as [delta [Hdelta Hnear]].
  exists (Rmin eta delta); split; [apply Rmin_pos; assumption|].
  intros b Db Hdist.
  assert (Hbe : Rabs (b-a)<eta) by (eapply Rlt_le_trans; [exact Hdist|apply Rmin_l]).
  assert (Hbd : Rabs (b-a)<delta) by (eapply Rlt_le_trans; [exact Hdist|apply Rmin_r]).
  assert (Hcb : c b<eps).
  { specialize (Hnear b Hbd).
    rewrite Hca Rminus_0_r in Hnear; pose proof (Rle_abs (c b)); lra. }
  destruct (Hb b Db Hbe) as [Hnonneg Hbound]; split; [lra|].
  intros xs Hxs; specialize (Hbound xs Hxs).
  pose proof (gaussian_coordinate_product_weight_nonnegative p xs); nra.
Qed.

Theorem gaussian_iterated_expectation_continuous_modulus_within d
    (F : R -> list R -> R) (D : R -> Prop) a C q p c :
  D a -> finite_polynomial_bound d C q (F a) ->
  (exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    finite_joint_continuous d (F b)) ->
  {for a, continuous c} -> c a=0 ->
  (exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    finite_polynomial_bound d (c b) p (fun xs => F b xs-F a xs)) ->
  ((fun b => gaussian_iterated_expectation d (F b)) @ within D (nbhs a) -->
    gaussian_iterated_expectation d (F a))%classic /\
  exists eta, 0<eta /\ forall b, D b -> Rabs (b-a)<eta ->
    gaussian_iterated_integrable d (F b) /\
    gaussian_iterated_absolutely_integrable d (F b) /\
    gaussian_iterated_has_expectation d (F b) (gaussian_iterated_expectation d (F b)) /\
    gaussian_iterated_has_expectation d (fun xs => Rabs (F b xs))
      (gaussian_iterated_expectation d (fun xs => Rabs (F b xs))) /\
    Rabs (gaussian_iterated_expectation d (F b)) <=
      (C+1)*gaussian_coordinate_weight_moment (q+p)%coq_nat ^ d.
Proof.
  intros Da Hb HC Hc Hca HD.
  apply (gaussian_iterated_expectation_continuous_within d F D a C q p Da Hb HC).
  exact (gaussian_iterated_weighted_modulus_within d F D a p c Hc Hca HD).
Qed.
