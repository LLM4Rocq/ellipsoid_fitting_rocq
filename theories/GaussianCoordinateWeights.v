(* Polynomial weights of the coordinates. gaussian_coordinate_weight p x is
   (1 + Rabs x) ^ p, and gaussian_coordinate_product_weight p xs is the
   product of the weights of the coordinates of xs. The weight is
   continuous, at least 1, at most 2 ^ p * (1 + Rabs x ^ p), and integrable
   against the Gaussian kernel (gaussian_coordinate_weight_integrable). The
   product weight on d coordinates has the iterated Gaussian expectation
   gaussian_coordinate_weight_moment p ^ d
   (gaussian_coordinate_product_weight_expectation). The module also proves
   that finite_polynomial_bound holds for constants and is preserved by
   sums, scalar multiples and products, and by multiplication by a
   coordinate x_i, by x_i * x_i - 1 or by x_i * x_j, which raise the degree.

   The statements write List.nth because MathComp's seq.nth takes its
   arguments in another order, (xs ++ ys)%list because ++ would be
   MathComp's cat, and %coq_nat for the order, sum and product on nat
   because %nat would give ssrnat's leq, ltn, addn and muln. *)

From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions GaussianMass
  GaussianExpectation GaussianMoments GaussianIntegration GaussianProductDefinitions
  GaussianProduct GaussianCoordinateWeightDefinitions.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_coordinate_weight_nonnegative p x :
  0 <= gaussian_coordinate_weight p x.
Proof. unfold gaussian_coordinate_weight; apply pow_le; pose proof (Rabs_pos x); lra. Qed.

Lemma gaussian_coordinate_weight_at_least_one p x :
  1 <= gaussian_coordinate_weight p x.
Proof. unfold gaussian_coordinate_weight; apply pow_R1_Rle; pose proof (Rabs_pos x); lra. Qed.

Lemma gaussian_coordinate_weight_continuous p (x : R) :
  {for x, continuous (gaussian_coordinate_weight p)}.
Proof.
  unfold gaussian_coordinate_weight.
  have H1 : {for x, continuous (fun y : R => 1 + Rabs y)}.
  { apply: continuous_plus; [apply: continuous_const | exact: continuous_Rabs]. }
  exact: (continuous_comp H1 (gaussian_power_continuous p (1 + Rabs x))).
Qed.

Lemma gaussian_coordinate_weight_polynomial_bound p x :
  gaussian_coordinate_weight p x <= 2^p * (1 + Rabs x^p).
Proof.
  unfold gaussian_coordinate_weight.
  pose proof (Rabs_pos x) as Hx.
  pose proof (pow_le (Rabs x) p Hx) as Hp.
  pose proof (pow_le 2 p ltac:(lra)) as H2.
  destruct (Rle_dec (Rabs x) 1) as [Hle|Hgt].
  - pose proof (pow_incr (1 + Rabs x) 2 p ltac:(split; lra)); nra.
  - pose proof (pow_incr (1 + Rabs x) (2*Rabs x) p ltac:(split; lra)) as H.
    rewrite Rpow_mult_distr in H; nra.
Qed.

Theorem gaussian_coordinate_weight_integrable p :
  gaussian_integral_exists (gaussian_coordinate_weight p) /\
  gaussian_absolutely_integrable (gaussian_coordinate_weight p).
Proof.
  apply (gaussian_polynomial_admissible _ (2^p) p).
  - exact (gaussian_coordinate_weight_continuous p).
  - intro x; rewrite (Rabs_pos_eq _ (gaussian_coordinate_weight_nonnegative p x)).
    apply gaussian_coordinate_weight_polynomial_bound.
Qed.

Lemma gaussian_coordinate_weight_moment_at_least_one p :
  1 <= gaussian_coordinate_weight_moment p.
Proof.
  unfold gaussian_coordinate_weight_moment.
  rewrite <- (gaussian_expectation_of_constant 1).
  apply gaussian_expectation_monotone.
  - exact (gaussian_integral_exists_constant 1).
  - exact (proj1 (gaussian_coordinate_weight_integrable p)).
  - apply gaussian_coordinate_weight_at_least_one.
Qed.

Lemma gaussian_coordinate_weight_degree_monotone p q x :
  (p <= q)%coq_nat -> gaussian_coordinate_weight p x <= gaussian_coordinate_weight q x.
Proof.
  intro H; induction H as [|q H IH]; [lra|].
  pose proof (gaussian_coordinate_weight_nonnegative q x).
  pose proof (Rabs_pos x).
  unfold gaussian_coordinate_weight in *; simpl; nra.
Qed.

Lemma gaussian_coordinate_weight_times_coordinate p x :
  Rabs x * gaussian_coordinate_weight p x <= gaussian_coordinate_weight (S p) x.
Proof.
  pose proof (gaussian_coordinate_weight_nonnegative p x).
  unfold gaussian_coordinate_weight in *; simpl; nra.
Qed.

Lemma gaussian_coordinate_weight_times_centered_square p x :
  Rabs (x*x - 1) * gaussian_coordinate_weight p x <=
  gaussian_coordinate_weight (S (S p)) x.
Proof.
  pose proof (gaussian_coordinate_weight_nonnegative p x) as Hp.
  pose proof (Rabs_pos x) as Hx.
  assert (Hsq : Rabs x * Rabs x = x*x).
  { rewrite <- Rabs_mult; apply Rabs_pos_eq; nra. }
  assert (H : Rabs (x*x-1) <= Rabs x * Rabs x + 1).
  { apply Rabs_le; split; nra. }
  unfold gaussian_coordinate_weight in *; simpl; nra.
Qed.

Lemma gaussian_coordinate_product_weight_append p xs ys :
  gaussian_coordinate_product_weight p (xs ++ ys)%list =
  gaussian_coordinate_product_weight p xs * gaussian_coordinate_product_weight p ys.
Proof. induction xs as [|x xs IH]; simpl; [ring|rewrite IH; ring]. Qed.

Lemma gaussian_coordinate_product_weight_at_least_one p xs :
  1 <= gaussian_coordinate_product_weight p xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lra|].
  pose proof (gaussian_coordinate_weight_at_least_one p x); nra.
Qed.

Lemma gaussian_coordinate_product_weight_nonnegative p xs :
  0 <= gaussian_coordinate_product_weight p xs.
Proof. pose proof (gaussian_coordinate_product_weight_at_least_one p xs); lra. Qed.

Lemma gaussian_coordinate_product_weight_degree_monotone p q xs :
  (p <= q)%coq_nat ->
  gaussian_coordinate_product_weight p xs <= gaussian_coordinate_product_weight q xs.
Proof.
  intro Hpq; induction xs as [|x xs IH]; simpl; [lra|].
  pose proof (gaussian_coordinate_weight_degree_monotone p q x Hpq).
  pose proof (gaussian_coordinate_weight_nonnegative p x).
  pose proof (gaussian_coordinate_product_weight_nonnegative q xs).
  nra.
Qed.

Lemma gaussian_coordinate_product_weight_box p xs R :
  0 <= R -> (forall x, In x xs -> Rabs x <= R) ->
  gaussian_coordinate_product_weight p xs <= (1 + R) ^ (p * length xs)%coq_nat.
Proof.
  intros HR Hbox; induction xs as [|x xs IH]; simpl.
  - rewrite Nat.mul_0_r; simpl; lra.
  - assert (Hx : Rabs x <= R) by (apply Hbox; now left).
    assert (Hxs : forall y, In y xs -> Rabs y <= R).
    { intros y Hy; apply Hbox; now right. }
    specialize (IH Hxs).
    rewrite Nat.mul_succ_r pow_add.
    unfold gaussian_coordinate_weight.
    pose proof (pow_incr (1+Rabs x) (1+R) p ltac:(pose proof (Rabs_pos x); split; lra)).
    pose proof (gaussian_coordinate_product_weight_nonnegative p xs).
    pose proof (pow_le (1+R) p ltac:(lra)).
    nra.
Qed.

Lemma gaussian_coordinate_product_weight_degree_add p q xs :
  gaussian_coordinate_product_weight (p+q)%coq_nat xs =
  gaussian_coordinate_product_weight p xs * gaussian_coordinate_product_weight q xs.
Proof.
  induction xs as [|x xs IH]; simpl; [ring|].
  unfold gaussian_coordinate_weight; rewrite pow_add IH; ring.
Qed.

Lemma gaussian_coordinate_product_weight_coordinate_bound p q h i xs :
  (p <= q)%coq_nat ->
  (forall x, Rabs (h x) * gaussian_coordinate_weight p x <=
    gaussian_coordinate_weight q x) ->
  (i < length xs)%coq_nat ->
  Rabs (h (List.nth i xs 0)) * gaussian_coordinate_product_weight p xs <=
  gaussian_coordinate_product_weight q xs.
Proof.
  intros Hpq Hh; revert i; induction xs as [|x xs IH]; intros i Hi; [simpl in Hi; lia|].
  destruct i as [|i]; simpl.
  - pose proof (Hh x).
    pose proof (gaussian_coordinate_product_weight_degree_monotone p q xs Hpq).
    pose proof (gaussian_coordinate_product_weight_nonnegative p xs).
    pose proof (gaussian_coordinate_weight_nonnegative q x).
    nra.
  - specialize (IH i ltac:(simpl in Hi; lia)).
    pose proof (gaussian_coordinate_weight_degree_monotone p q x Hpq).
    pose proof (gaussian_coordinate_weight_nonnegative p x).
    pose proof (gaussian_coordinate_product_weight_nonnegative q xs).
    nra.
Qed.

Lemma gaussian_coordinate_product_weight_times_coordinate p i xs :
  (i < length xs)%coq_nat ->
  Rabs (List.nth i xs 0) * gaussian_coordinate_product_weight p xs <=
  gaussian_coordinate_product_weight (S p) xs.
Proof.
  apply (gaussian_coordinate_product_weight_coordinate_bound p (S p) (fun x => x)).
  - lia.
  - apply gaussian_coordinate_weight_times_coordinate.
Qed.

Lemma gaussian_coordinate_product_weight_times_centered_square p i xs :
  (i < length xs)%coq_nat ->
  Rabs (List.nth i xs 0 * List.nth i xs 0 - 1) * gaussian_coordinate_product_weight p xs <=
  gaussian_coordinate_product_weight (S (S p)) xs.
Proof.
  apply (gaussian_coordinate_product_weight_coordinate_bound p (S (S p))
    (fun x => x*x-1)).
  - lia.
  - apply gaussian_coordinate_weight_times_centered_square.
Qed.

Lemma finite_polynomial_bound_constant d c :
  finite_polynomial_bound d (Rabs c) 0 (fun _ => c).
Proof.
  split; [apply Rabs_pos|].
  intros xs Hxs; pose proof (gaussian_coordinate_product_weight_at_least_one 0 xs).
  pose proof (Rabs_pos c); nra.
Qed.

Lemma finite_polynomial_bound_degree_monotone d C p q F :
  finite_polynomial_bound d C p F -> (p <= q)%coq_nat ->
  finite_polynomial_bound d C q F.
Proof.
  intros [HC HF] Hpq; split; [exact HC|].
  intros xs Hxs; specialize (HF xs Hxs).
  pose proof (gaussian_coordinate_product_weight_degree_monotone p q xs Hpq); nra.
Qed.

Lemma finite_polynomial_bound_scale d C p F a :
  finite_polynomial_bound d C p F ->
  finite_polynomial_bound d (Rabs a * C) p (fun xs => a * F xs).
Proof.
  intros [HC HF]; pose proof (Rabs_pos a); split; [nra|].
  intros xs Hxs; rewrite Rabs_mult; specialize (HF xs Hxs); nra.
Qed.

Lemma finite_polynomial_bound_add d C D p F G :
  finite_polynomial_bound d C p F -> finite_polynomial_bound d D p G ->
  finite_polynomial_bound d (C+D) p (fun xs => F xs + G xs).
Proof.
  intros [HC HF] [HD HG]; split; [lra|].
  intros xs Hxs; specialize (HF xs Hxs); specialize (HG xs Hxs).
  pose proof (Rabs_triang (F xs) (G xs)); nra.
Qed.

Lemma finite_polynomial_bound_mult d C D p q F G :
  finite_polynomial_bound d C p F -> finite_polynomial_bound d D q G ->
  finite_polynomial_bound d (C*D) (p+q)%coq_nat (fun xs => F xs * G xs).
Proof.
  intros [HC HF] [HD HG]; split; [nra|].
  intros xs Hxs; specialize (HF xs Hxs); specialize (HG xs Hxs).
  rewrite Rabs_mult gaussian_coordinate_product_weight_degree_add.
  pose proof (Rabs_pos (F xs)); pose proof (Rabs_pos (G xs)).
  pose proof (gaussian_coordinate_product_weight_nonnegative p xs).
  pose proof (gaussian_coordinate_product_weight_nonnegative q xs).
  apply Rle_trans with ((C * gaussian_coordinate_product_weight p xs) *
    (D * gaussian_coordinate_product_weight q xs)).
  - apply Rmult_le_compat; nra.
  - right; ring.
Qed.

Lemma finite_polynomial_bound_times_coordinate d C p F i :
  finite_polynomial_bound d C p F -> (i < d)%coq_nat ->
  finite_polynomial_bound d C (S p) (fun xs => List.nth i xs 0 * F xs).
Proof.
  intros [HC HF] Hi; split; [exact HC|].
  intros xs Hxs; specialize (HF xs Hxs); rewrite Rabs_mult.
  pose proof (gaussian_coordinate_product_weight_times_coordinate p i xs ltac:(lia)).
  pose proof (Rabs_pos (List.nth i xs 0)); nra.
Qed.

Lemma finite_polynomial_bound_times_centered_square d C p F i :
  finite_polynomial_bound d C p F -> (i < d)%coq_nat ->
  finite_polynomial_bound d C (S (S p))
    (fun xs => (List.nth i xs 0 * List.nth i xs 0 - 1) * F xs).
Proof.
  intros [HC HF] Hi; split; [exact HC|].
  intros xs Hxs; specialize (HF xs Hxs); rewrite Rabs_mult.
  pose proof (gaussian_coordinate_product_weight_times_centered_square p i xs ltac:(lia)).
  pose proof (Rabs_pos (List.nth i xs 0 * List.nth i xs 0 - 1)); nra.
Qed.

Lemma finite_polynomial_bound_times_two_coordinates d C p F i j :
  finite_polynomial_bound d C p F -> (i < d)%coq_nat -> (j < d)%coq_nat ->
  finite_polynomial_bound d C (S (S p))
    (fun xs => (List.nth i xs 0 * List.nth j xs 0) * F xs).
Proof.
  intros HF Hi Hj.
  destruct (finite_polynomial_bound_times_coordinate d C (S p)
    (fun xs => List.nth j xs 0 * F xs) i
    (finite_polynomial_bound_times_coordinate d C p F j HF Hj) Hi) as [HC H].
  split; [exact HC|]. intros xs Hxs; specialize (H xs Hxs).
  replace (List.nth i xs 0 * List.nth j xs 0 * F xs) with
    (List.nth i xs 0 * (List.nth j xs 0 * F xs)) by ring; exact H.
Qed.

Theorem gaussian_coordinate_product_weight_expectation p d :
  gaussian_iterated_integrable d (gaussian_coordinate_product_weight p) /\
  gaussian_iterated_expectation d (gaussian_coordinate_product_weight p) =
  gaussian_coordinate_weight_moment p ^ d.
Proof.
  induction d as [|d [HI HE]]; [simpl; split; [exact I|reflexivity]|].
  assert (Hfun : (fun x => gaussian_iterated_expectation d
      (fun xs => gaussian_coordinate_product_weight p (x::xs))) =
    (fun x => gaussian_coordinate_weight_moment p ^ d * gaussian_coordinate_weight p x)).
  { apply functional_extensionality; intro x; simpl gaussian_coordinate_product_weight.
    rewrite (proj2 (gaussian_iterated_scale d _ (gaussian_coordinate_weight p x) HI)) HE.
    ring. }
  split.
  - split.
    + intro x; exact (proj1 (gaussian_iterated_scale d _ (gaussian_coordinate_weight p x) HI)).
    + rewrite Hfun; apply gaussian_integral_exists_scale.
      exact (proj1 (gaussian_coordinate_weight_integrable p)).
  - change (gaussian_expectation (fun x => gaussian_iterated_expectation d
      (fun xs => gaussian_coordinate_product_weight p (x::xs))) =
      gaussian_coordinate_weight_moment p ^ S d).
    rewrite Hfun (gaussian_expectation_scale _ _
      (proj1 (gaussian_coordinate_weight_integrable p))).
    unfold gaussian_coordinate_weight_moment; simpl; ring.
Qed.
