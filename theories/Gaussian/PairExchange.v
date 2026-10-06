From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.VectorListDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.VectorDefinitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.SuffixMarginalDefinitions Gaussian.IteratedExpectation
  Matrix.VectorCoordinates Gaussian.VectorDomain Joint.Definitions
  Joint.ListCoordinates Gaussian.BlockExchange.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Fubini's theorem for the Gaussian expectation of a function F x z of two
   independent standard Gaussian vectors x and z, of dimensions S m and
   S n. Integrating out z, or x, gives the suffix or the prefix marginal of
   the pullback of F to lists of S m + S n coordinates
   (gaussian_pair_suffix_marginal, gaussian_pair_prefix_marginal). If that
   pullback is jointly continuous and polynomially bounded, then F, its
   sections and its two partial expectations are in the Gaussian domain,
   and the joint expectation equals both iterated expectations
   (gaussian_pair_finite_exchange). gaussian_pair_polynomial_exchange
   concludes the same when F is continuous on the joint vectors q = (x, z)
   of euclidean_product and Rabs (F x z) <= C * (1 + |q|) ^ p, where |q| is
   the Euclidean norm of the S m + S n coordinates. The joint expectation
   is linear (gaussian_pair_linear_expectation).

   With ssreflect loaded, + on nat would be ssrnat's addn and ++ MathComp's
   cat, so the statements write (S m + S n)%coq_nat and (xs ++ ys)%list. *)

Lemma gaussian_pair_suffix_marginal m n F xs : length xs = S m ->
  gaussian_suffix_marginal (S n) (gaussian_pair_pullback m n F) xs =
  gaussian_vector_expectation n (F (vector_of_list m xs)).
Proof.
  intro Hxs; unfold gaussian_suffix_marginal, gaussian_vector_expectation.
  apply gaussian_iterated_expectation_ext; intros ys Hys.
  apply gaussian_pair_pullback_append; exact Hxs.
Qed.

Lemma gaussian_pair_prefix_marginal m n F ys :
  gaussian_iterated_expectation (S m)
    (fun xs => gaussian_pair_pullback m n F (xs ++ ys)%list) =
  gaussian_vector_expectation m (fun x => F x (vector_of_list n ys)).
Proof.
  unfold gaussian_vector_expectation.
  apply gaussian_iterated_expectation_ext; intros xs Hxs.
  apply gaussian_pair_pullback_append; exact Hxs.
Qed.

Theorem gaussian_pair_finite_exchange m n F C p :
  finite_joint_continuous (S m + S n)%coq_nat (gaussian_pair_pullback m n F) ->
  finite_polynomial_bound (S m + S n)%coq_nat C p (gaussian_pair_pullback m n F) ->
  gaussian_pair_domain m n F /\
  (forall x, gaussian_vector_domain n (F x)) /\
  (forall z, gaussian_vector_domain m (fun x => F x z)) /\
  gaussian_vector_domain m (fun x => gaussian_vector_expectation n (F x)) /\
  gaussian_vector_domain n (fun z => gaussian_vector_expectation m (fun x => F x z)) /\
  gaussian_pair_expectation m n F =
    gaussian_vector_expectation m (fun x => gaussian_vector_expectation n (F x)) /\
  gaussian_pair_expectation m n F =
    gaussian_vector_expectation n (fun z => gaussian_vector_expectation m (fun x => F x z)).
Proof.
  intros HC HB.
  destruct (gaussian_block_suffix_domains (S m) (S n) _ C p HC HB)
    as [HS [HM _]].
  destruct (gaussian_block_prefix_domains (S m) (S n) _ C p HC HB)
    as [HR [HN _]].
  destruct (gaussian_block_exchange_signed (S m) (S n) _ C p HC HB) as [EF ER].
  split; [exact (gaussian_list_domain_polynomial _ _ C p HC HB)|].
  split.
  - intro x; change (gaussian_list_domain (S n) (fun ys => F x (vector_of_list n ys))).
    eapply gaussian_list_domain_ext; [|exact (HS (vector_to_list m x) (vector_to_list_length m x))].
    intros ys Hys; cbn beta.
    rewrite (gaussian_pair_pullback_append m n F _ ys (vector_to_list_length m x)).
    rewrite vector_of_to_list; reflexivity.
  - split.
    + intro z; change (gaussian_list_domain (S m) (fun xs => F (vector_of_list m xs) z)).
      eapply gaussian_list_domain_ext; [|exact (HR (vector_to_list n z) (vector_to_list_length n z))].
      intros xs Hxs; cbn beta.
      rewrite (gaussian_pair_pullback_append m n F xs _ Hxs).
      rewrite vector_of_to_list; reflexivity.
    + split.
      * change (gaussian_list_domain (S m)
          (fun xs => gaussian_vector_expectation n (F (vector_of_list m xs)))).
        eapply gaussian_list_domain_ext; [|exact HM].
        intros xs Hxs; exact (gaussian_pair_suffix_marginal m n F xs Hxs).
      * split.
        -- change (gaussian_list_domain (S n)
             (fun ys => gaussian_vector_expectation m (fun x => F x (vector_of_list n ys)))).
           eapply gaussian_list_domain_ext; [|exact HN].
           intros ys Hys; exact (gaussian_pair_prefix_marginal m n F ys).
        -- split.
           ++ eapply eq_trans; [exact EF|].
              unfold gaussian_vector_expectation at 1.
              apply gaussian_iterated_expectation_ext; intros xs Hxs.
              exact (gaussian_pair_suffix_marginal m n F xs Hxs).
           ++ eapply eq_trans; [exact ER|].
              unfold gaussian_vector_expectation at 1.
              apply gaussian_iterated_expectation_ext; intros ys Hys.
              exact (gaussian_pair_prefix_marginal m n F ys).
Qed.

Theorem gaussian_pair_polynomial_exchange m n F C p :
  (forall q : euclidean_product (vector_NormedModule m) (vector_NormedModule n),
    {for q, continuous (fun q : euclidean_product (vector_NormedModule m) (vector_NormedModule n) =>
      F (fst q) (snd q))}) -> 0 <= C ->
  (forall q : euclidean_product (vector_NormedModule m) (vector_NormedModule n),
    Rabs (F (fst q) (snd q)) <= C*(1+`|q|%R)^p) ->
  gaussian_pair_domain m n F /\
  (forall x, gaussian_vector_domain n (F x)) /\
  (forall z, gaussian_vector_domain m (fun x => F x z)) /\
  gaussian_vector_domain m (fun x => gaussian_vector_expectation n (F x)) /\
  gaussian_vector_domain n (fun z => gaussian_vector_expectation m (fun x => F x z)) /\
  gaussian_pair_expectation m n F =
    gaussian_vector_expectation m (fun x => gaussian_vector_expectation n (F x)) /\
  gaussian_pair_expectation m n F =
    gaussian_vector_expectation n (fun z => gaussian_vector_expectation m (fun x => F x z)).
Proof.
  intros HC HK HB; apply (gaussian_pair_finite_exchange m n F C p).
  - exact (joint_continuous_pullback m n F HC).
  - exact (joint_polynomial_pullback m n F C p HK HB).
Qed.

Lemma gaussian_pair_expectation_ext m n F G :
  (forall x z, F x z = G x z) ->
  gaussian_pair_expectation m n F = gaussian_pair_expectation m n G.
Proof.
  intro HE; unfold gaussian_pair_expectation; apply gaussian_iterated_expectation_ext.
  intros xs Hxs; unfold gaussian_pair_pullback; apply HE.
Qed.

Lemma gaussian_pair_linear_expectation m n F G a b :
  gaussian_pair_domain m n F -> gaussian_pair_domain m n G ->
  gaussian_pair_expectation m n (fun x z => a*F x z+b*G x z) =
    a*gaussian_pair_expectation m n F+b*gaussian_pair_expectation m n G.
Proof.
  intros [HF _] [HG _].
  destruct (gaussian_iterated_scale (S m + S n)%coq_nat
    (gaussian_pair_pullback m n F) a HF) as [HFa EFa].
  destruct (gaussian_iterated_scale (S m + S n)%coq_nat
    (gaussian_pair_pullback m n G) b HG) as [HGb EGb].
  unfold gaussian_pair_expectation, gaussian_pair_pullback in *.
  rewrite (proj2 (gaussian_iterated_add _ _ _ HFa HGb)) EFa EGb; reflexivity.
Qed.
