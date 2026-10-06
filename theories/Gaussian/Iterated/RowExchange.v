(* Integrating out one row of a Gaussian matrix. A list of N * K
   coordinates is read as N rows of K coordinates, and
   row_assemble N K i background row puts row in place of row i. For F
   continuous and polynomially bounded, the expectation of F is the
   expectation over the background of the expectation over row i, and
   every function integrated on the way is integrable
   (gaussian_row_block_exchange). So if the expectations over row i of F
   and of c * G agree for every background, the expectation of F is c
   times that of G (gaussian_row_conditional_identity). *)

From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Gaussian.Iterated.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions
  Gaussian.Iterated.SuffixMarginalDefinitions Joint.Definitions
  Row.CoordinateDefinitions Row.Coordinates.
From EllipsoidFitting Require Import Gaussian.Iterated.Expectation
  Analysis.CoordinateTopology Gaussian.Iterated.SuffixAlgebra
  Gaussian.Coordinate.PermutationWeights Gaussian.Iterated.LastIntegration.
From EllipsoidFitting Require Import Gaussian.Iterated.BlockRotation
  Gaussian.Iterated.BlockExchange.
From EllipsoidFitting Require Gaussian.Iterated.PolynomialGrowth.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_list_domain_scale d (F : list R -> R) c :
  gaussian_list_domain d F ->
  gaussian_list_domain d (fun xs => c * F xs) /\
  gaussian_iterated_expectation d (fun xs => c * F xs) =
    c * gaussian_iterated_expectation d F.
Proof.
  intros [HI [HA _]].
  destruct (gaussian_iterated_scale d F c HI) as [HS HE].
  split; [|exact HE].
  apply gaussian_list_domain_of_integrable; [exact HS|].
  destruct (gaussian_iterated_scale d (fun xs => Rabs (F xs)) (Rabs c) HA) as [HA' _].
  eapply gaussian_iterated_integrable_ext; [|exact HA'].
  intros xs Hxs; rewrite Rabs_mult; reflexivity.
Qed.

Theorem gaussian_row_block_exchange N K i (F : list R -> R) C p :
  (i < N)%nat ->
  finite_joint_continuous (N*K) F -> finite_polynomial_bound (N*K) C p F ->
  gaussian_list_domain (N*K) F /\
  (forall background, length background = ((N-1)*K)%nat ->
    gaussian_list_domain K (fun row => F (row_assemble N K i background row))) /\
  gaussian_list_domain ((N-1)*K)
    (fun background => gaussian_iterated_expectation K
      (fun row => F (row_assemble N K i background row))) /\
  gaussian_list_domain ((N-1)*K)
    (fun background => gaussian_iterated_expectation K
      (fun row => Rabs (F (row_assemble N K i background row)))) /\
  finite_joint_continuous ((N-1)*K)
    (fun background => gaussian_iterated_expectation K
      (fun row => F (row_assemble N K i background row))) /\
  finite_polynomial_bound ((N-1)*K)
    (C*gaussian_coordinate_weight_moment p^K) p
    (fun background => gaussian_iterated_expectation K
      (fun row => F (row_assemble N K i background row))) /\
  gaussian_iterated_expectation (N*K) F =
    gaussian_iterated_expectation ((N-1)*K)
      (fun background => gaussian_iterated_expectation K
        (fun row => F (row_assemble N K i background row))) /\
  gaussian_iterated_expectation (N*K) (fun xs => Rabs (F xs)) =
    gaussian_iterated_expectation ((N-1)*K)
      (fun background => gaussian_iterated_expectation K
        (fun row => Rabs (F (row_assemble N K i background row)))).
Proof.
  intros Hi HC HB.
  set (L := ((N-1)*K)%nat).
  set (b := ((N-1-i)*K)%nat).
  set (G := fun xs : list R => F (skipn b xs ++ firstn b xs)).
  assert (Hdim : (N*K)%nat = (L+K)%nat) by (unfold L; assert (N=1+(N-1))%nat by lia; nia).
  assert (Hb : (b <= N*K)%nat) by (unfold b; pose proof (row_index_lengths N K i Hi); lia).
  assert (HCg : finite_joint_continuous (L+K) G).
  { rewrite <- Hdim; apply finite_joint_continuous_block_rotation; exact HC. }
  assert (HBg : finite_polynomial_bound (L+K) C p G).
  { rewrite <- Hdim; apply finite_polynomial_bound_block_rotation; exact HB. }
  destruct (gaussian_block_exchange L K G C p HCg HBg)
    as [HD [HS [HT [HM [HN [HMC [HMB [HNC [HNB [HE1 [HE2 [HA1 HA2]]]]]]]]]]]].
  assert (Hm : forall background, length background = L ->
    gaussian_suffix_marginal K G background =
      gaussian_iterated_expectation K (fun row => F (row_assemble N K i background row))).
  { intros background HL; unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros row HR.
    unfold G, b; rewrite <- row_assemble_rotation by assumption; reflexivity. }
  assert (Hma : forall background, length background = L ->
    gaussian_suffix_marginal K (fun xs => Rabs (G xs)) background =
      gaussian_iterated_expectation K (fun row => Rabs (F (row_assemble N K i background row)))).
  { intros background HL; unfold gaussian_suffix_marginal.
    apply gaussian_iterated_expectation_ext; intros row HR.
    unfold G, b; rewrite <- row_assemble_rotation by assumption; reflexivity. }
  inversion HM as [|? ? HM1 HMrest]; subst.
  inversion HMrest as [|? ? HM2 HMnil]; subst.
  split; [exact (gaussian_list_domain_polynomial (N*K) F C p HC HB)|].
  split.
  - intros background HL.
    eapply gaussian_list_domain_ext; [|exact (HS background HL)].
    intros row HR; unfold G, b; rewrite <- row_assemble_rotation by assumption; reflexivity.
  - split; [eapply gaussian_list_domain_ext; [exact Hm|exact HM1]|].
    split; [eapply gaussian_list_domain_ext; [exact Hma|exact HM2]|].
    split; [eapply finite_joint_continuous_ext; [exact Hm|exact HMC]|].
    split; [eapply finite_polynomial_bound_ext; [exact Hm|exact HMB]|].
    split.
    + transitivity (gaussian_iterated_expectation (N*K) G).
      * exact (gaussian_iterated_block_rotation_bounded (N*K) b F C p Hb HC HB).
      * rewrite Hdim, HE1; apply gaussian_iterated_expectation_ext; exact Hm.
    + transitivity (gaussian_iterated_expectation (N*K) (fun xs => Rabs (G xs))).
      * exact (gaussian_iterated_block_rotation_bounded (N*K) b (fun xs => Rabs (F xs)) C p Hb
          (finite_joint_continuous_abs (N*K) F HC)
          (Gaussian.Iterated.PolynomialGrowth.finite_polynomial_bound_abs (N*K) C p F HB)).
      * rewrite Hdim, HA1; apply gaussian_iterated_expectation_ext; exact Hma.
Qed.

Theorem gaussian_row_conditional_identity N K i (F G : list R -> R) CF CG p q c :
  (i < N)%nat ->
  finite_joint_continuous (N*K) F -> finite_polynomial_bound (N*K) CF p F ->
  finite_joint_continuous (N*K) G -> finite_polynomial_bound (N*K) CG q G ->
  (forall background, length background = ((N-1)*K)%nat ->
    gaussian_iterated_expectation K (fun row => F (row_assemble N K i background row)) =
    c * gaussian_iterated_expectation K (fun row => G (row_assemble N K i background row))) ->
  gaussian_list_domain (N*K) F /\ gaussian_list_domain (N*K) G /\
  gaussian_iterated_expectation (N*K) F = c * gaussian_iterated_expectation (N*K) G.
Proof.
  intros Hi HCF HBF HCG HBG Hrow.
  destruct (gaussian_row_block_exchange N K i F CF p Hi HCF HBF)
    as [HF [_ [HFM [_ [_ [_ [HEF _]]]]]]].
  destruct (gaussian_row_block_exchange N K i G CG q Hi HCG HBG)
    as [HG [_ [HGM [_ [_ [_ [HEG _]]]]]]].
  split; [exact HF|]; split; [exact HG|].
  rewrite HEF, HEG.
  transitivity (gaussian_iterated_expectation ((N-1)*K)
    (fun background => c * gaussian_iterated_expectation K
      (fun row => G (row_assemble N K i background row)))).
  - apply gaussian_iterated_expectation_ext; exact Hrow.
  - exact (proj2 (gaussian_list_domain_scale ((N-1)*K) _ c HGM)).
Qed.
