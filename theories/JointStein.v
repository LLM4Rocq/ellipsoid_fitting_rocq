From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions TensorDefinitions
  GaussianVectorDefinitions GaussianVectorAlgebra GoeDefinitions JointDefinitions
  GaussianPairExchange JointGrowth JointSections JointCancellationAlgebra
  FiniteGibbsContinuity.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Gaussian integration by parts along the joint interpolation path
   joint_matrix n C t x z = C + sqrt t * joint_quadratic_input n x +
   sqrt (1-t) * goe_matrix n z, where x and z are independent standard
   Gaussian vectors. The four joint observables of JointDefinitions are the
   pairings of the nested gradient with joint_quadratic_input n x and with
   goe_matrix n z (joint_quadratic_trace, joint_goe_trace), the symmetric
   divergence of the derivative of the gradient (joint_divergence), and the
   contraction of the third derivative with x (joint_remainder).
   - joint_observables_exchange: each observable satisfies
     gaussian_pair_domain and the domain conditions in each variable, and
     its joint expectation is the iterated expectation in either order.
   - joint_quadratic_pair_stein: by Stein's identity in x, the expectation
     of joint_quadratic_trace is a combination of those of joint_divergence
     and joint_remainder, when the coefficients coeff y s are symmetric.
   - joint_goe_pair_stein: by Stein's identity in z, the expectation of
     joint_goe_trace is (2 * sqrt (1-t) / (n + 1)) times that of
     joint_divergence.
   - joint_velocity_domain and joint_gaussian_stein_cancellation: the
     velocity joint_quadratic_trace / (2 * sqrt t) -
     joint_goe_trace / (2 * sqrt (1-t)), the pairing of the gradient with
     the time derivative of the path, satisfies gaussian_pair_domain, and
     for 0 < t < 1 the divergence terms cancel in its expectation, which is
     sqrt t / (2 * (n + 1) * sqrt (n + 1)) times that of joint_remainder.
   The observables are continuous and polynomially bounded (JointGrowth),
   which gives the integrability (GaussianPairExchange). Each level of the
   iterated expectation is a Lebesgue integral against the Gaussian
   kernel. *)

(* The joint vector space, named for the proofs only. *)
Local Notation joint_space n :=
  (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))).

Lemma joint_vector_linear_expectation n F G a b :
  gaussian_vector_domain n F -> gaussian_vector_domain n G ->
  gaussian_vector_expectation n (fun x => a*F x+b*G x) =
    a*gaussian_vector_expectation n F+b*gaussian_vector_expectation n G.
Proof.
  intros [HF _] [HG _].
  destruct (gaussian_vector_scale n F a HF) as [HFa EFa].
  destruct (gaussian_vector_scale n G b HG) as [HGb EGb].
  rewrite (proj2 (gaussian_vector_add n _ _ HFa HGb)) EFa EGb; reflexivity.
Qed.

Theorem joint_observables_exchange n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall F : vector n -> vector (goe_vector_index n) -> R,
  In F [joint_quadratic_trace n beta gamma offset coeff Y S C t;
        joint_goe_trace n beta gamma offset coeff Y S C t;
        joint_divergence n beta gamma offset coeff Y S C t;
        joint_remainder n beta gamma offset coeff Y S C t] ->
  gaussian_pair_domain n (goe_vector_index n) F /\
  (forall x, gaussian_vector_domain (goe_vector_index n) (F x)) /\
  (forall z, gaussian_vector_domain n (fun x => F x z)) /\
  gaussian_vector_domain n (fun x => gaussian_vector_expectation (goe_vector_index n) (F x)) /\
  gaussian_vector_domain (goe_vector_index n) (fun z => gaussian_vector_expectation n (fun x => F x z)) /\
  gaussian_pair_expectation n (goe_vector_index n) F =
    gaussian_vector_expectation n (fun x => gaussian_vector_expectation (goe_vector_index n) (F x)) /\
  gaussian_pair_expectation n (goe_vector_index n) F =
    gaussian_vector_expectation (goe_vector_index n) (fun z => gaussian_vector_expectation n (fun x => F x z)).
Proof.
  intros Hb Hg HY HS F HF.
  destruct (joint_observables_polynomial_regular n beta gamma offset coeff Y S Hb Hg HY HS)
    as [KP [KQ [KD [KR [HP [HQ [HD [HR H]]]]]]]].
  simpl in HF; destruct HF as [HF|[HF|[HF|[HF|HF]]]]; [subst F|subst F|subst F|subst F|contradiction].
  - apply (gaussian_pair_polynomial_exchange n (goe_vector_index n) _ KP 2); [|exact HP|];
      intro q; specialize (H C t q); tauto.
  - apply (gaussian_pair_polynomial_exchange n (goe_vector_index n) _ KQ 1); [|exact HQ|];
      intro q; specialize (H C t q); tauto.
  - apply (gaussian_pair_polynomial_exchange n (goe_vector_index n) _ KD 0); [|exact HD|];
      intro q; specialize (H C t q); tauto.
  - apply (gaussian_pair_polynomial_exchange n (goe_vector_index n) _ KR 2); [|exact HR|];
      intro q; specialize (H C t q); tauto.
Qed.

Theorem joint_quadratic_pair_stein n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= t ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_quadratic_trace n beta gamma offset coeff Y S C t) =
  (2*sqrt t/INR(Datatypes.S n)) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_divergence n beta gamma offset coeff Y S C t) +
  (t/(INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_remainder n beta gamma offset coeff Y S C t).
Proof.
  intros Hb Hg HY HS Ht HC.
  pose proof (joint_observables_exchange n beta gamma offset coeff Y S C t Hb Hg HY HS) as H.
  destruct (H (joint_quadratic_trace n beta gamma offset coeff Y S C t) ltac:(simpl; auto)) as [_ [_ [_ [_ [_ [_ EP]]]]]].
  destruct (H (joint_divergence n beta gamma offset coeff Y S C t) ltac:(simpl; auto))
    as [_ [_ [_ [_ [HD [_ ED]]]]]].
  destruct (H (joint_remainder n beta gamma offset coeff Y S C t) ltac:(simpl; auto))
    as [_ [_ [_ [_ [HR [_ ER]]]]]].
  rewrite EP ED ER.
  eapply eq_trans.
  - apply gaussian_vector_expectation_ext; intro z.
    exact (proj2 (joint_quadratic_section_stein n beta gamma offset coeff Y S C t z Hb Hg HY HS Ht HC)).
  - apply joint_vector_linear_expectation; assumption.
Qed.

Theorem joint_goe_pair_stein n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_goe_trace n beta gamma offset coeff Y S C t) =
  (2*sqrt(1-t)/INR(Datatypes.S n)) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_divergence n beta gamma offset coeff Y S C t).
Proof.
  intros Hb Hg HY HS.
  pose proof (joint_observables_exchange n beta gamma offset coeff Y S C t Hb Hg HY HS) as H.
  destruct (H (joint_goe_trace n beta gamma offset coeff Y S C t) ltac:(simpl; auto))
    as [_ [_ [_ [_ [_ [EQ _]]]]]].
  destruct (H (joint_divergence n beta gamma offset coeff Y S C t) ltac:(simpl; auto))
    as [_ [_ [_ [HD [_ [ED _]]]]]].
  rewrite EQ ED.
  eapply eq_trans.
  - apply gaussian_vector_expectation_ext; intro x.
    exact (proj2 (joint_goe_section_stein n beta gamma offset coeff Y S C t x Hb Hg HY HS)).
  - exact (proj2 (gaussian_vector_scale n _ _ (proj1 HD))).
Qed.

Theorem joint_velocity_domain n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_pair_domain n (goe_vector_index n) (fun x z =>
    joint_quadratic_trace n beta gamma offset coeff Y S C t x z / (2*sqrt t) -
    joint_goe_trace n beta gamma offset coeff Y S C t x z / (2*sqrt(1-t))).
Proof.
  intros Hb Hg HY HS.
  destruct (joint_observables_polynomial_regular n beta gamma offset coeff Y S Hb Hg HY HS)
    as [KP [KQ [KD [KR [HP [HQ [HD [HR H]]]]]]]].
  refine (proj1 (gaussian_pair_polynomial_exchange n (goe_vector_index n) _
    (Rabs (/(2*sqrt t))*KP+Rabs (/(2*sqrt(1-t)))*KQ) 2 _ _ _)).
  - intro q; specialize (H C t q); destruct H as [[HPC _] [[HQC _] _]].
    apply (@continuous_Rminus_fct (joint_space n)
      (fun z : joint_space n => joint_quadratic_trace n beta gamma offset coeff Y S C t (fst z) (snd z) / (2*sqrt t))
      (fun z : joint_space n => joint_goe_trace n beta gamma offset coeff Y S C t (fst z) (snd z) / (2*sqrt(1-t)))).
    + apply (@continuous_Rmult_fct (joint_space n)
        (fun z : joint_space n => joint_quadratic_trace n beta gamma offset coeff Y S C t (fst z) (snd z))
        (fun _ : joint_space n => / (2*sqrt t))); [exact HPC|apply: cst_continuous].
    + apply (@continuous_Rmult_fct (joint_space n)
        (fun z : joint_space n => joint_goe_trace n beta gamma offset coeff Y S C t (fst z) (snd z))
        (fun _ : joint_space n => / (2*sqrt(1-t)))); [exact HQC|apply: cst_continuous].
  - apply Rplus_le_le_0_compat; apply Rmult_le_pos; [apply Rabs_pos|exact HP|apply Rabs_pos|exact HQ].
  - intro q; specialize (H C t q); destruct H as [[HPC HPB] [[HQC HQB] _]].
    set N := (`|q|)%R in HPB HQB |- *.
    assert (Hq : 0 <= N) by (unfold N; apply/RleP; apply normr_ge0).
    assert (HQB2 : Rabs (joint_goe_trace n beta gamma offset coeff Y S C t (fst q) (snd q)) <= KQ*(1+N)^2).
    { eapply Rle_trans; [exact HQB|]. apply Rmult_le_compat_l; [exact HQ|].
      rewrite pow_1; replace ((1+N)^2) with ((1+N)*(1+N)) by ring; nra. }
    eapply Rle_trans; [apply Rabs_triang|].
    unfold Rdiv; rewrite Rabs_Ropp !Rabs_mult.
    replace ((Rabs (/(2*sqrt t))*KP+Rabs (/(2*sqrt(1-t)))*KQ)*(1+N)^2) with
      ((KP*(1+N)^2)*Rabs (/(2*sqrt t))+(KQ*(1+N)^2)*Rabs (/(2*sqrt(1-t)))) by ring.
    apply Rplus_le_compat; apply Rmult_le_compat_r; try apply Rabs_pos; assumption.
Qed.

Theorem joint_gaussian_stein_cancellation n beta gamma offset coeff Y S C t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 < t < 1 ->
  (forall y s, In y Y -> In s S -> symmetric_matrix n (coeff y s)) ->
  List.Forall (gaussian_pair_domain n (goe_vector_index n))
    [joint_quadratic_trace n beta gamma offset coeff Y S C t;
     joint_goe_trace n beta gamma offset coeff Y S C t;
     joint_divergence n beta gamma offset coeff Y S C t;
     joint_remainder n beta gamma offset coeff Y S C t] /\
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_quadratic_trace n beta gamma offset coeff Y S C t) =
  (2*sqrt t/INR(Datatypes.S n)) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_divergence n beta gamma offset coeff Y S C t) +
  (t/(INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_remainder n beta gamma offset coeff Y S C t) /\
  gaussian_pair_expectation n (goe_vector_index n)
    (joint_goe_trace n beta gamma offset coeff Y S C t) =
  (2*sqrt(1-t)/INR(Datatypes.S n)) * gaussian_pair_expectation n (goe_vector_index n)
    (joint_divergence n beta gamma offset coeff Y S C t) /\
  gaussian_pair_domain n (goe_vector_index n) (fun x z =>
    joint_quadratic_trace n beta gamma offset coeff Y S C t x z / (2*sqrt t) -
    joint_goe_trace n beta gamma offset coeff Y S C t x z / (2*sqrt(1-t))) /\
  gaussian_pair_expectation n (goe_vector_index n) (fun x z =>
    joint_quadratic_trace n beta gamma offset coeff Y S C t x z / (2*sqrt t) -
    joint_goe_trace n beta gamma offset coeff Y S C t x z / (2*sqrt(1-t))) =
  (sqrt t/(2*INR(Datatypes.S n)*sqrt(INR(Datatypes.S n)))) *
    gaussian_pair_expectation n (goe_vector_index n) (joint_remainder n beta gamma offset coeff Y S C t).
Proof.
  intros Hb Hg HY HS Ht HC.
  assert (HD : List.Forall (gaussian_pair_domain n (goe_vector_index n))
    [joint_quadratic_trace n beta gamma offset coeff Y S C t;
     joint_goe_trace n beta gamma offset coeff Y S C t;
     joint_divergence n beta gamma offset coeff Y S C t;
     joint_remainder n beta gamma offset coeff Y S C t]).
  { apply Forall_forall; intros F HF.
    exact (proj1 (joint_observables_exchange n beta gamma offset coeff Y S C t Hb Hg HY HS F HF)). }
  pose proof (joint_quadratic_pair_stein n beta gamma offset coeff Y S C t Hb Hg HY HS ltac:(lra) HC) as HP.
  pose proof (joint_goe_pair_stein n beta gamma offset coeff Y S C t Hb Hg HY HS) as HQ.
  split; [exact HD|]; split; [exact HP|]; split; [exact HQ|]; split.
  - apply joint_velocity_domain; assumption.
  - eapply eq_trans with
      (gaussian_pair_expectation n (goe_vector_index n) (fun x z =>
        /(2*sqrt t)*joint_quadratic_trace n beta gamma offset coeff Y S C t x z +
        (-/(2*sqrt(1-t)))*joint_goe_trace n beta gamma offset coeff Y S C t x z)).
    + apply gaussian_pair_expectation_ext; intros x z; unfold Rdiv; ring.
    + assert (HPD : gaussian_pair_domain n (goe_vector_index n)
        (joint_quadratic_trace n beta gamma offset coeff Y S C t)) by (inversion HD; assumption).
      assert (HQD : gaussian_pair_domain n (goe_vector_index n)
        (joint_goe_trace n beta gamma offset coeff Y S C t))
        by (inversion HD as [|? ? HPD' HTD]; subst; inversion HTD; assumption).
      rewrite (gaussian_pair_linear_expectation _ _ _ _ _ _ HPD HQD).
      replace (/(2*sqrt t)*gaussian_pair_expectation n (goe_vector_index n)
        (joint_quadratic_trace n beta gamma offset coeff Y S C t) +
        (-/(2*sqrt(1-t)))*gaussian_pair_expectation n (goe_vector_index n)
        (joint_goe_trace n beta gamma offset coeff Y S C t)) with
        (gaussian_pair_expectation n (goe_vector_index n) (joint_quadratic_trace n beta gamma offset coeff Y S C t)/(2*sqrt t) -
        gaussian_pair_expectation n (goe_vector_index n) (joint_goe_trace n beta gamma offset coeff Y S C t)/(2*sqrt(1-t))) by (unfold Rdiv; ring).
      apply (joint_stein_cancellation n t _ _
        (gaussian_pair_expectation n (goe_vector_index n) (joint_divergence n beta gamma offset coeff Y S C t))); assumption.
Qed.
