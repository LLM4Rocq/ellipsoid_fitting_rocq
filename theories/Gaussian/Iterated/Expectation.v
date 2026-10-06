(* Basic properties of the iterated Gaussian expectation
   gaussian_iterated_expectation of Gaussian.Iterated.Definitions, which
   integrates a function of d coordinates against the standard Gaussian
   density, one coordinate at a time. It depends only on the values on
   lists of length d (gaussian_iterated_expectation_ext), and it is linear,
   monotone and equal to c on the constant c (gaussian_iterated_add,
   gaussian_iterated_scale, gaussian_iterated_monotone,
   gaussian_iterated_constant). The expectation of a product of functions
   of distinct coordinates is the product of their expectations
   (gaussian_separable_factorization). The integrals are Lebesgue integrals
   (gaussian_expectation_density_integral). *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Line.Kernel
  Gaussian.Line.Mass Gaussian.Line.Expectation Gaussian.Iterated.Definitions.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_integral_exists_ext f g :
  (forall x, f x = g x) ->
  gaussian_integral_exists f -> gaussian_integral_exists g.
Proof.
  intros He Hf.
  replace g with f by (apply functional_extensionality; exact He).
  exact Hf.
Qed.

Lemma gaussian_expectation_density_integral f :
  gaussian_integral_exists f ->
  whole_line_has_integral (fun x => f x * gaussian_density x)
    (gaussian_expectation f).
Proof.
  intro Hf.
  pose proof (gaussian_has_integral_scale f (gaussian_integral f) (/ gaussian_mass)
    (gaussian_integral_correct f Hf)) as H.
  unfold gaussian_has_integral in H.
  replace (fun x => f x * gaussian_density x) with
    (fun x => / gaussian_mass * f x * gaussian_kernel x).
  - replace (gaussian_expectation f) with (/ gaussian_mass * gaussian_integral f).
    + exact H.
    + unfold gaussian_expectation, Rdiv; ring.
  - apply functional_extensionality; intro x.
    unfold gaussian_density, Rdiv; ring.
Qed.

Lemma gaussian_iterated_expectation_ext d F G :
  (forall xs, length xs = d -> F xs = G xs) ->
  gaussian_iterated_expectation d F = gaussian_iterated_expectation d G.
Proof.
  revert F G; induction d as [|d IH]; intros F G He; simpl.
  - apply He; reflexivity.
  - f_equal; apply functional_extensionality; intro x.
    apply IH; intros xs Hxs; apply He; simpl; now rewrite Hxs.
Qed.

Lemma gaussian_iterated_integrable_ext d F G :
  (forall xs, length xs = d -> F xs = G xs) ->
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G.
Proof.
  revert F G; induction d as [|d IH]; intros F G He HI; simpl in *; [exact I |].
  destruct HI as [Hs Ho]; split.
  - intro x; apply (IH (fun xs => F (x::xs))); [|apply Hs].
    intros xs Hxs; apply He; simpl; now rewrite Hxs.
  - apply gaussian_integral_exists_ext with
      (f := fun x => gaussian_iterated_expectation d (fun xs => F (x::xs))); [|exact Ho].
    intro x; apply gaussian_iterated_expectation_ext.
    intros xs Hxs; apply He; simpl; now rewrite Hxs.
Qed.

Lemma gaussian_iterated_has_expectation_correct d F :
  gaussian_iterated_integrable d F ->
  gaussian_iterated_has_expectation d F (gaussian_iterated_expectation d F).
Proof.
  revert F; induction d as [|d IH]; intros F HI; simpl in *; [reflexivity |].
  destruct HI as [Hs Ho]; split.
  - intro x; apply IH, Hs.
  - apply gaussian_expectation_density_integral; exact Ho.
Qed.

Lemma gaussian_iterated_scale d F c :
  gaussian_iterated_integrable d F ->
  gaussian_iterated_integrable d (fun xs => c * F xs) /\
  gaussian_iterated_expectation d (fun xs => c * F xs) =
    c * gaussian_iterated_expectation d F.
Proof.
  revert F c; induction d as [|d IH]; intros F c HI; simpl in *.
  - split; [exact I | reflexivity].
  - destruct HI as [Hs Ho].
    assert (He : (fun x => gaussian_iterated_expectation d (fun xs => c * F (x::xs))) =
      (fun x => c * gaussian_iterated_expectation d (fun xs => F (x::xs)))).
    { apply functional_extensionality; intro x; exact (proj2 (IH _ c (Hs x))). }
    split.
    + split.
      * intro x; exact (proj1 (IH _ c (Hs x))).
      * rewrite He; apply gaussian_integral_exists_scale; exact Ho.
    + rewrite He; apply gaussian_expectation_scale; exact Ho.
Qed.

Theorem gaussian_iterated_constant d c :
  gaussian_iterated_integrable d (fun _ => c) /\
  gaussian_iterated_expectation d (fun _ => c) = c.
Proof.
  induction d as [|d [HI HE]]; simpl; [split; [exact I | reflexivity] |].
  rewrite HE; split.
  - split; [intro x; exact HI |].
    apply gaussian_integral_exists_constant.
  - apply gaussian_expectation_of_constant.
Qed.

Theorem gaussian_iterated_add d F G :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  gaussian_iterated_integrable d (fun xs => F xs + G xs) /\
  gaussian_iterated_expectation d (fun xs => F xs + G xs) =
    gaussian_iterated_expectation d F + gaussian_iterated_expectation d G.
Proof.
  revert F G; induction d as [|d IH]; intros F G HF HG; simpl in *.
  - split; [exact I | reflexivity].
  - destruct HF as [HF HFo]; destruct HG as [HG HGo].
    assert (He : (fun x => gaussian_iterated_expectation d (fun xs => F (x::xs) + G (x::xs))) =
      (fun x => gaussian_iterated_expectation d (fun xs => F (x::xs)) +
        gaussian_iterated_expectation d (fun xs => G (x::xs)))).
    { apply functional_extensionality; intro x; exact (proj2 (IH _ _ (HF x) (HG x))). }
    split.
    + split.
      * intro x; exact (proj1 (IH _ _ (HF x) (HG x))).
      * rewrite He; apply gaussian_integral_exists_add; assumption.
    + rewrite He; apply gaussian_expectation_add; assumption.
Qed.

Theorem gaussian_iterated_nonnegative d F :
  gaussian_iterated_integrable d F ->
  (forall xs, length xs = d -> 0 <= F xs) ->
  0 <= gaussian_iterated_expectation d F.
Proof.
  revert F; induction d as [|d IH]; intros F HI Hnonneg; simpl in *.
  - apply Hnonneg; reflexivity.
  - destruct HI as [Hs Ho]; apply gaussian_expectation_nonnegative; [exact Ho |].
    intro x; apply IH; [apply Hs |].
    intros xs Hxs; apply Hnonneg; simpl; now rewrite Hxs.
Qed.

Theorem gaussian_iterated_monotone d F G :
  gaussian_iterated_integrable d F -> gaussian_iterated_integrable d G ->
  (forall xs, length xs = d -> F xs <= G xs) ->
  gaussian_iterated_expectation d F <= gaussian_iterated_expectation d G.
Proof.
  revert F G; induction d as [|d IH]; intros F G HF HG Hle; simpl in *.
  - apply Hle; reflexivity.
  - destruct HF as [HF HFo]; destruct HG as [HG HGo].
    apply gaussian_expectation_monotone; [exact HFo |exact HGo |].
    intro x; apply IH; [apply HF |apply HG |].
    intros xs Hxs; apply Hle; simpl; now rewrite Hxs.
Qed.

Theorem gaussian_separable_factorization fs :
  List.Forall gaussian_integral_exists fs ->
  gaussian_iterated_integrable (length fs) (gaussian_separable_product fs) /\
  gaussian_iterated_expectation (length fs) (gaussian_separable_product fs) =
    gaussian_product_expectations fs.
Proof.
  intro H; induction H as [|f fs Hf Hfs [HI HE]].
  - simpl; split; [exact I | reflexivity].
  - simpl.
    assert (Hscale : forall x,
      gaussian_iterated_integrable (length fs) (fun xs => f x * gaussian_separable_product fs xs) /\
      gaussian_iterated_expectation (length fs) (fun xs => f x * gaussian_separable_product fs xs) =
        f x * gaussian_product_expectations fs).
    { intro x; pose proof (gaussian_iterated_scale (length fs) _ (f x) HI) as H.
      rewrite HE in H; exact H. }
    assert (He : (fun x => gaussian_iterated_expectation (length fs)
      (fun xs => f x * gaussian_separable_product fs xs)) =
      (fun x => gaussian_product_expectations fs * f x)).
    { apply functional_extensionality; intro x; rewrite (proj2 (Hscale x)); ring. }
    split.
    + split; [intro x; apply Hscale |].
      rewrite He; apply gaussian_integral_exists_scale; exact Hf.
    + rewrite He, gaussian_expectation_scale by exact Hf; ring.
Qed.

Lemma gaussian_separable_product_abs fs xs :
  Rabs (gaussian_separable_product fs xs) =
  gaussian_separable_product (List.map (fun f x => Rabs (f x)) fs) xs.
Proof.
  revert xs; induction fs as [|f fs IH]; intro xs; simpl.
  - apply Rabs_R1.
  - destruct xs as [|x xs]; simpl; [apply Rabs_R0 |].
    rewrite Rabs_mult, IH; reflexivity.
Qed.

Theorem gaussian_separable_absolute_integrable fs :
  List.Forall gaussian_absolutely_integrable fs ->
  gaussian_iterated_absolutely_integrable (length fs) (gaussian_separable_product fs).
Proof.
  intro Hfs.
  assert (Habs : List.Forall gaussian_integral_exists (List.map (fun f x => Rabs (f x)) fs)).
  { induction Hfs; simpl; constructor; assumption. }
  pose proof (proj1 (gaussian_separable_factorization _ Habs)) as HI.
  rewrite length_map in HI.
  unfold gaussian_iterated_absolutely_integrable.
  apply gaussian_iterated_integrable_ext with
    (F := gaussian_separable_product (List.map (fun f x => Rabs (f x)) fs)); [|exact HI].
  intros xs Hxs; symmetry; apply gaussian_separable_product_abs.
Qed.

Theorem gaussian_separable_product_integral fs :
  List.Forall gaussian_integral_exists fs ->
  List.Forall gaussian_absolutely_integrable fs ->
  gaussian_iterated_integrable (length fs) (gaussian_separable_product fs) /\
  gaussian_iterated_absolutely_integrable (length fs) (gaussian_separable_product fs) /\
  gaussian_iterated_has_expectation (length fs) (gaussian_separable_product fs)
    (gaussian_product_expectations fs) /\
  gaussian_iterated_expectation (length fs) (gaussian_separable_product fs) =
    gaussian_product_expectations fs.
Proof.
  intros Hf Habs; destruct (gaussian_separable_factorization fs Hf) as [HI HE].
  split; [exact HI |].
  split; [apply gaussian_separable_absolute_integrable; exact Habs |].
  split; [rewrite <- HE; apply gaussian_iterated_has_expectation_correct; exact HI |exact HE].
Qed.
