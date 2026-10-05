(* Port of theories/GaussianRowExchange.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The proofs are the original ones, word for word, except
   for one qualified name described below. The changes are in the import
   lines.
   - "From Coquelicot Require Import Coquelicot." is dropped: no statement
     or proof here names a Coquelicot notion.
   - The original imported the bundles GaussianCoordinateProofs and
     InterpolationProofs, and opened their inner modules GaussianProduct,
     GaussianCoordinateTopology, GaussianCoordinateSuffixAlgebra,
     GaussianPermutationWeights and GaussianLastIntegration (of the first)
     and InterpolationProofs.JointProofs.GaussianBlockPermutation and
     InterpolationProofs.JointProofs.GaussianBlockExchange (of the second).
     Here the standalone ported modules of the same names are imported
     directly, in the same order, so that every short name resolves to the
     same module as before.
   - The original named one lemma through the bundle, as
     GaussianCoordinateProofs.GaussianCoordinateMarginals.finite_polynomial_bound_abs.
     Here it is GaussianCoordinateMarginals.finite_polynomial_bound_abs, in
     the standalone module, which is required but not imported, as the
     original did not open that inner module either.

   This module imports no MathComp library itself, and none of its imports
   re-exports one. So (i < N)%nat is Peano's lt, N*K, N-1 and (N-1)*K are
   Stdlib's operations on nat, and the lists (firstn, skipn, ++, length),
   the arithmetic on R and the tactic syntax are Stdlib's, as in the
   original. An importer that loads ssreflect reads (i < N)%nat as ssrnat's
   boolean ltn; the statements here keep Peano's lt, which lia proves, as
   the original RowStein does with [lia|].

   The meaning of the statements follows the ported definitions they use.
   finite_joint_continuous (GaussianCoordinateDefinitions),
   finite_polynomial_bound (GaussianCoordinateWeightDefinitions) and
   row_assemble (RowCoordinateDefinitions, a byte copy) have their original
   texts. gaussian_iterated_integrable, gaussian_iterated_has_expectation
   and gaussian_iterated_expectation (GaussianProductDefinitions), and
   through them gaussian_list_domain (JointDefinitions), now use at each
   level Lebesgue integrability over the line and the Lebesgue integral
   against the Gaussian kernel, in place of Coquelicot's improper Riemann
   integral (difference 4 of analysis/README.md). The statements keep their
   text in that vocabulary, and none of them gains a hypothesis.
   gaussian_list_domain_scale relates these notions to one another and holds
   in either meaning. Under the hypotheses finite_joint_continuous and
   finite_polynomial_bound of the two theorems, every function integrated at
   every level is continuous and bounded by a constant times a polynomial
   weight, so it is absolutely integrable against the kernel, where the two
   meanings agree. This agreement is a mathematical argument and is not
   proved in Rocq. No statement is weakened. *)

From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianLastDefinitions
  JointDefinitions RowCoordinateDefinitions RowCoordinates.
From EllipsoidFitting Require Import GaussianProduct GaussianCoordinateTopology
  GaussianCoordinateSuffixAlgebra GaussianPermutationWeights
  GaussianLastIntegration.
From EllipsoidFitting Require Import GaussianBlockPermutation GaussianBlockExchange.
From EllipsoidFitting Require GaussianCoordinateMarginals.
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
          (GaussianCoordinateMarginals.finite_polynomial_bound_abs (N*K) C p F HB)).
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
