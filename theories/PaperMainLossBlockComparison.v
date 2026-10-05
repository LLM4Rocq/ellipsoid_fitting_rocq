(* Comparison of Gaussian expectations block by block. F and G are
   regular functions (pmdf_regular: continuous with a polynomial bound) of
   the concatenation of two blocks of independent standard Gaussian
   coordinates.
   - paper_main_loss_prefix_integral_regular and
     paper_main_loss_suffix_integral_regular: integrating out one block
     keeps regularity.
   - paper_main_loss_conditional_prefix_comparison: if, for every fixed
     suffix ys of length m, the expectations of F and G over the prefix
     (of lengths p and q) differ by at most B, then so do the full
     expectations.
   - paper_main_loss_conditional_suffix_comparison: the same with the
     prefix fixed and the suffix integrated. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianLastDefinitions
  GaussianLastIntegration GaussianBlockExchange PaperMainDataFeatureMomentsCoordinates
  PaperMainLossRowIncrement.
Open Scope R_scope.

Lemma paper_main_loss_prefix_integral_regular p m F : pmdf_regular (Nat.add p m) F ->
  pmdf_regular m (fun ys => gaussian_iterated_expectation p (fun xs => F(List.app xs ys))).
Proof.
intros [HF [C [k HB]]].
destruct(gaussian_block_prefix_domains p m F C k HF HB) as [_ [_ [HC Hbound]]].
split; [exact HC|exists (C*gaussian_coordinate_weight_moment k^p),k; exact Hbound].
Qed.

Lemma paper_main_loss_suffix_integral_regular p m F : pmdf_regular (Nat.add p m) F ->
  pmdf_regular p (fun xs => gaussian_iterated_expectation m (fun ys => F(List.app xs ys))).
Proof.
intros [HF [C [k HB]]].
destruct(gaussian_block_suffix_domains p m F C k HF HB) as [_ [_ [HC Hbound]]].
split; [exact HC|exists (C*gaussian_coordinate_weight_moment k^m),k; exact Hbound].
Qed.

Theorem paper_main_loss_conditional_prefix_comparison p q m F G B :
  pmdf_regular (Nat.add p m) F -> pmdf_regular (Nat.add q m) G ->
  (forall ys, List.length ys=m ->
    Rabs(gaussian_iterated_expectation p (fun xs => F(List.app xs ys))-
      gaussian_iterated_expectation q (fun xs => G(List.app xs ys)))<=B) ->
  Rabs(gaussian_iterated_expectation (Nat.add p m) F-
    gaussian_iterated_expectation (Nat.add q m) G)<=B.
Proof.
intros HF HG HB.
pose proof(paper_main_loss_prefix_integral_regular p m F HF) as HFI.
pose proof(paper_main_loss_prefix_integral_regular q m G HG) as HGI.
destruct HF as [HF [CF [kF HBF]]]; destruct HG as [HG [CG [kG HBG]]].
rewrite (proj2(gaussian_block_exchange_signed p m F CF kF HF HBF))
  (proj2(gaussian_block_exchange_signed q m G CG kG HG HBG)).
apply paper_main_loss_expected_difference; [apply pmdf_regular_integrable; exact HFI|
  apply pmdf_regular_integrable; exact HGI|exact HB].
Qed.

Theorem paper_main_loss_conditional_suffix_comparison p m n F G B :
  pmdf_regular (Nat.add p m) F -> pmdf_regular (Nat.add p n) G ->
  (forall xs, List.length xs=p ->
    Rabs(gaussian_iterated_expectation m (fun ys => F(List.app xs ys))-
      gaussian_iterated_expectation n (fun ys => G(List.app xs ys)))<=B) ->
  Rabs(gaussian_iterated_expectation (Nat.add p m) F-
    gaussian_iterated_expectation (Nat.add p n) G)<=B.
Proof.
intros HF HG HB.
pose proof(paper_main_loss_suffix_integral_regular p m F HF) as HFI.
pose proof(paper_main_loss_suffix_integral_regular p n G HG) as HGI.
rewrite (gaussian_iterated_suffix_expectation p m F)
  (gaussian_iterated_suffix_expectation p n G).
apply paper_main_loss_expected_difference; [apply pmdf_regular_integrable; exact HFI|
  apply pmdf_regular_integrable; exact HGI|exact HB].
Qed.
