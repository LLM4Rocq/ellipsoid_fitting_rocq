(* Integrating out the last coordinates of an iterated Gaussian
   expectation. The expectation over d + 1 coordinates is the expectation
   over d coordinates of the last marginal
   (gaussian_iterated_last_expectation), and the expectation over d + n
   coordinates is the expectation over d coordinates of the suffix marginal
   over n coordinates (gaussian_iterated_suffix_expectation). Iterated
   integrability over d + 1 (or d + n) coordinates is equivalent to the
   integrability of every section in the last coordinate (or in the last n
   coordinates) together with the iterated integrability of the marginal
   (gaussian_iterated_last_integrable, gaussian_iterated_suffix_integrable).
   Finally, if F and G are integrable and Rabs F <= G, then the expectation
   of G bounds the absolute value of that of F
   (gaussian_iterated_majorant_bound). *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Gaussian.SuffixMarginalDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_iterated_last_expectation d F :
  gaussian_iterated_expectation (S d) F =
  gaussian_iterated_expectation d (gaussian_last_marginal F).
Proof.
  revert F; induction d as [|d IH]; intro F.
  - reflexivity.
  - change (gaussian_expectation (fun x =>
      gaussian_iterated_expectation (S d) (fun ys => F (x::ys))) =
      gaussian_expectation (fun x =>
      gaussian_iterated_expectation d (fun xs => gaussian_last_marginal F (x::xs)))).
    apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
    exact (IH (fun ys => F (x::ys))).
Qed.

Theorem gaussian_iterated_last_integrable d F :
  gaussian_iterated_integrable (S d) F <->
  (forall xs, length xs = d ->
    gaussian_integral_exists (fun t => F (xs ++ [t]))) /\
  gaussian_iterated_integrable d (gaussian_last_marginal F).
Proof.
  revert F; induction d as [|d IH]; intro F.
  - simpl. split.
    + intros [_ Ho]; split; [|exact I].
      intros xs Hxs; destruct xs; [exact Ho|discriminate].
    + intros [Hs _]; split; [intro x; exact I|exact (Hs [] eq_refl)].
  - split.
    + intros [Hs Ho]; split.
      * intros xs Hxs; destruct xs as [|x xs]; [discriminate|].
        apply (proj1 (proj1 (IH (fun ys => F (x::ys))) (Hs x))).
        simpl in Hxs; lia.
      * split.
        -- intro x; exact (proj2 (proj1 (IH (fun ys => F (x::ys))) (Hs x))).
        -- apply gaussian_integral_exists_ext with
             (f := fun x => gaussian_iterated_expectation (S d) (fun ys => F (x::ys))).
           ++ intro x; apply gaussian_iterated_last_expectation.
           ++ exact Ho.
    + intros [Hsections [Hs Ho]]; split.
      * intro x; apply (proj2 (IH (fun ys => F (x::ys)))); split.
        -- intros xs Hxs; apply (Hsections (x::xs)); simpl; now rewrite Hxs.
        -- exact (Hs x).
      * apply gaussian_integral_exists_ext with
          (f := fun x => gaussian_iterated_expectation d
             (fun xs => gaussian_last_marginal F (x::xs))).
        -- intro x; symmetry; apply gaussian_iterated_last_expectation.
        -- exact Ho.
Qed.

Theorem gaussian_iterated_suffix_expectation d n F :
  gaussian_iterated_expectation (d+n) F =
  gaussian_iterated_expectation d (gaussian_suffix_marginal n F).
Proof.
  revert F; induction d as [|d IH]; intro F.
  - reflexivity.
  - change (gaussian_expectation (fun x =>
      gaussian_iterated_expectation (d+n) (fun ys => F (x::ys))) =
      gaussian_expectation (fun x =>
      gaussian_iterated_expectation d (fun xs => gaussian_suffix_marginal n F (x::xs)))).
    apply (f_equal gaussian_expectation); apply functional_extensionality; intro x.
    exact (IH (fun ys => F (x::ys))).
Qed.

Theorem gaussian_iterated_suffix_integrable d n F :
  gaussian_iterated_integrable (d+n) F <->
  (forall xs, length xs = d ->
    gaussian_iterated_integrable n (fun ys => F (xs ++ ys))) /\
  gaussian_iterated_integrable d (gaussian_suffix_marginal n F).
Proof.
  revert F; induction d as [|d IH]; intro F.
  - simpl. split.
    + intro HI; split; [|exact I].
      intros xs Hxs; destruct xs; [exact HI|discriminate].
    + intros [Hs _]; exact (Hs [] eq_refl).
  - split.
    + intros [Hs Ho]; split.
      * intros xs Hxs; destruct xs as [|x xs]; [discriminate|].
        apply (proj1 (proj1 (IH (fun ys => F (x::ys))) (Hs x))).
        simpl in Hxs; lia.
      * split.
        -- intro x; exact (proj2 (proj1 (IH (fun ys => F (x::ys))) (Hs x))).
        -- apply gaussian_integral_exists_ext with
             (f := fun x => gaussian_iterated_expectation (d+n) (fun ys => F (x::ys))).
           ++ intro x; apply gaussian_iterated_suffix_expectation.
           ++ exact Ho.
    + intros [Hsections [Hs Ho]]; split.
      * intro x; apply (proj2 (IH (fun ys => F (x::ys)))); split.
        -- intros xs Hxs; apply (Hsections (x::xs)); simpl; now rewrite Hxs.
        -- exact (Hs x).
      * apply gaussian_integral_exists_ext with
          (f := fun x => gaussian_iterated_expectation d
             (fun xs => gaussian_suffix_marginal n F (x::xs))).
        -- intro x; symmetry; apply gaussian_iterated_suffix_expectation.
        -- exact Ho.
Qed.

Lemma gaussian_iterated_majorant_bound d F G :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  (forall xs, length xs = d -> Rabs (F xs) <= G xs) ->
  Rabs (gaussian_iterated_expectation d F) <= gaussian_iterated_expectation d G.
Proof.
  intros HF HG Hb.
  destruct (gaussian_iterated_scale d F (-1) HF) as [HN HNE].
  assert (Hupper : gaussian_iterated_expectation d F <= gaussian_iterated_expectation d G).
  { apply gaussian_iterated_monotone; try assumption.
    intros xs Hxs; specialize (Hb xs Hxs); pose proof (Rle_abs (F xs)); lra. }
  assert (Hlower : gaussian_iterated_expectation d (fun xs => -1*F xs) <=
    gaussian_iterated_expectation d G).
  { apply gaussian_iterated_monotone; try assumption.
    intros xs Hxs; specialize (Hb xs Hxs).
    pose proof (Rle_abs (-F xs)); rewrite Rabs_Ropp in H; lra. }
  rewrite HNE in Hlower. apply Rabs_le; split; lra.
Qed.
