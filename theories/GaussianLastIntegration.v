(* Port of theories/GaussianLastIntegration.v from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order,
   and its text. The only change to the file is that the Coquelicot import is
   dropped: no statement or proof here names a Coquelicot notion. The
   iterated operators come from the ported GaussianProductDefinitions, the
   marginals from GaussianLastDefinitions (unchanged text), and
   gaussian_integral_exists from the ported GaussianDefinitions.

   The meaning of the statements follows the ported definitions. In
   gaussian_iterated_last_integrable, gaussian_integral_exists
   (fun t => F (xs ++ [t])) now says that t |-> F (xs ++ [t]) times the
   Gaussian kernel is Lebesgue integrable over the line, in place of the
   convergence of an improper Riemann integral (difference 4 of
   analysis/README.md). gaussian_iterated_integrable asks for the same
   Lebesgue integrability at each level. The equalities of expectations are
   definitional unfoldings and do not depend on which integral is used.

   The proofs are those of the original. They use gaussian_integral_exists_ext,
   gaussian_iterated_scale and gaussian_iterated_monotone of the ported
   GaussianProduct, and Stdlib's functional_extensionality, whose axiom
   functional_extensionality_dep is one of the seven of analysis/README.md.

   This module imports no MathComp module, so length, ++, Rabs and the
   operations on R are Stdlib's. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct GaussianLastDefinitions.
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
