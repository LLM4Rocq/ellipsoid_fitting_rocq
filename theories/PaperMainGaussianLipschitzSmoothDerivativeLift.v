(* Conditional lifting of a one-dimensional Gaussian shift-derivative
   formula to the coordinate derivatives of the Gaussian smoothing.

   Every theorem here that concludes a derivative takes the one-dimensional
   statement paper_main_gaussian_shift_derivative_interface eps as an
   explicit premise. paper_main_gaussian_shift_derivative_proved of
   PaperMainGaussianAffineIntegralSmoothing proves it for every eps > 0, by
   an affine substitution and the derivative of the weighted density.

   Route: the iterated Gaussian expectation is invariant under moving the
   first coordinate to position a (adjacent swaps), so the smoothing in
   coordinate a becomes E_1[z |-> h (t + eps z)] with h bounded and
   Lipschitz, and the one-dimensional formula applies. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import SoftDefinitions GaussianDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateSteinDomains GaussianCoordinateWeights
  GaussianCoordinatePolynomialContinuity GaussianExpectationContinuity
  GaussianCovarianceSums GaussianCovarianceLinear
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianPermutationContinuity GaussianPermutationWeights GaussianCoordinateSwap
  GaussianCoordinateDerivativeDefinitions PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGordonLipschitz
  PaperMainGaussianLipschitzGradient PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzSmooth PaperMainGaussianLipschitzSmoothDerivative.
Import ListNotations.
Open Scope R_scope.

(* The one-dimensional statement used as an explicit premise: for bounded
   Lipschitz h, the Gaussian shift expectation is differentiable, with the
   Hermite weights z (from the weight 1) and z^2 - 1 (from the weight z). *)
Definition paper_main_gaussian_shift_derivative_interface (eps : R) : Prop :=
  forall (h : R -> R) (K L s : R), 0 <= K -> 0 <= L ->
    (forall y, Rabs (h y) <= K) ->
    (forall y y', Rabs (h y - h y') <= L * Rabs (y - y')) ->
    @is_derive R R^o R^o s 1 (fun t => gaussian_expectation (fun z => h (t + eps * z)))
      (/ eps * gaussian_expectation (fun z => h (s + eps * z) * z)) /\
    @is_derive R R^o R^o s 1
      (fun t => gaussian_expectation (fun z => z * h (t + eps * z)))
      (/ eps * gaussian_expectation (fun z => (z * z - 1) * h (s + eps * z))).

(* Insert z at position a of ws; at the end if ws is shorter. *)
Fixpoint paper_main_gaussian_insert (a : nat) (z : R) (ws : list R) : list R :=
  match a, ws with
  | O, _ => z :: ws
  | S b, w :: rest => w :: paper_main_gaussian_insert b z rest
  | S _, [] => [z]
  end.

(* Move the first coordinate to position a. *)
Definition paper_main_gaussian_front (a : nat) (zs : list R) : list R :=
  match zs with
  | [] => []
  | z :: ws => paper_main_gaussian_insert a z ws
  end.

Lemma paper_main_gaussian_insert_length a z ws :
  List.length (paper_main_gaussian_insert a z ws) = S (List.length ws).
Proof.
revert ws; induction a as [|a IH]; intros [|w ws]; simpl; try reflexivity.
rewrite IH; reflexivity.
Qed.

Lemma paper_main_gaussian_insert_succ a z ws :
  paper_main_gaussian_insert (S a) z ws =
    swap_adjacent a (paper_main_gaussian_insert a z ws).
Proof.
revert ws; induction a as [|a IH]; intros [|w ws]; try reflexivity.
- simpl; destruct a; reflexivity.
- simpl; f_equal; exact (IH ws).
Qed.

Lemma paper_main_gaussian_front_succ a zs :
  paper_main_gaussian_front (S a) zs =
    swap_adjacent a (paper_main_gaussian_front a zs).
Proof.
destruct zs as [|z ws]; [destruct a; reflexivity|].
exact (paper_main_gaussian_insert_succ a z ws).
Qed.

Lemma paper_main_gaussian_front_zero zs : paper_main_gaussian_front 0 zs = zs.
Proof. destruct zs; reflexivity. Qed.

Lemma paper_main_gaussian_insert_nth_same a z ws :
  (a <= List.length ws)%coq_nat ->
  List.nth a (paper_main_gaussian_insert a z ws) 0 = z.
Proof.
revert ws; induction a as [|a IH]; intros [|w ws] Ha; simpl in *;
  try reflexivity; try lia.
apply IH; lia.
Qed.

Lemma paper_main_gaussian_insert_replace a v z ws :
  (a <= List.length ws)%coq_nat ->
  replace_coordinate a v (paper_main_gaussian_insert a z ws) =
    paper_main_gaussian_insert a v ws.
Proof.
revert ws; induction a as [|a IH]; intros [|w ws] Ha; simpl in Ha;
  try reflexivity; try lia.
change (w :: replace_coordinate a v (paper_main_gaussian_insert a z ws) =
  w :: paper_main_gaussian_insert a v ws).
f_equal; apply IH; lia.
Qed.

Lemma paper_main_gaussian_insert_forall2 (rel : R -> R -> Prop) a ws ws' :
  rel 0 0 -> List.Forall2 rel ws ws' ->
  List.Forall2 rel (paper_main_gaussian_insert a 0 ws)
    (paper_main_gaussian_insert a 0 ws').
Proof.
intros H0 Hf; revert a; induction Hf as [|w w' ws ws' Hw Hf IH]; intros a.
- destruct a; simpl; constructor; try exact H0; constructor.
- destruct a as [|a]; simpl.
  + constructor; [exact H0|constructor; [exact Hw|exact Hf]].
  + constructor; [exact Hw|apply IH].
Qed.

Lemma paper_main_gaussian_insert_continuous m a (F : list R -> R) :
  finite_joint_continuous (S m) F ->
  finite_joint_continuous m (fun ws => F (paper_main_gaussian_insert a 0 ws)).
Proof.
intros HF.
apply (finite_joint_continuous_list_map m (S m) (paper_main_gaussian_insert a 0) F).
- intros ws Hws; rewrite paper_main_gaussian_insert_length; rewrite Hws; reflexivity.
- intros e ws ws' _ _ Hf; apply paper_main_gaussian_insert_forall2; [|exact Hf].
  rewrite Rminus_0_r; rewrite Rabs_R0; apply cond_pos.
- exact HF.
Qed.

Lemma paper_main_gaussian_iterated_succ m (F : list R -> R) :
  gaussian_iterated_expectation (S m) F =
  gaussian_expectation (fun x => gaussian_iterated_expectation m (fun xs => F (x :: xs))).
Proof. reflexivity. Qed.

(* Moving the first coordinate to position a does not change the iterated
   expectation of a continuous, polynomially bounded integrand. *)
Lemma paper_main_gaussian_iterated_front d a F C p :
  (a < d)%coq_nat -> finite_joint_continuous d F ->
  finite_polynomial_bound d C p F ->
  gaussian_iterated_expectation d F =
  gaussian_iterated_expectation d (fun zs => F (paper_main_gaussian_front a zs)).
Proof.
revert F; induction a as [|a IH]; intros F Ha HC HB.
- apply gaussian_iterated_expectation_ext; intros zs _.
  rewrite paper_main_gaussian_front_zero; reflexivity.
- rewrite (gaussian_iterated_swap_adjacent d a F C p Ha HC HB).
  rewrite (IH (fun xs => F (swap_adjacent a xs)) ltac:(lia)
    (finite_joint_continuous_swap_adjacent d a F HC)
    (finite_polynomial_bound_swap_adjacent d C p F a HB)).
  apply gaussian_iterated_expectation_ext; intros zs _.
  rewrite paper_main_gaussian_front_succ; reflexivity.
Qed.

Lemma paper_main_gaussian_shift_insert n xs eps a t z ws :
  (a < n)%coq_nat -> List.length xs = n -> (a <= List.length ws)%coq_nat ->
  paper_main_gaussian_shift n (replace_coordinate a t xs) eps
    (paper_main_gaussian_insert a z ws) =
  paper_main_gaussian_shift n (replace_coordinate a (t + eps * z) xs) eps
    (paper_main_gaussian_insert a 0 ws).
Proof.
intros Ha Hxs Hws.
apply (nth_ext _ _ 0 0).
- rewrite paper_main_gaussian_shift_length; rewrite paper_main_gaussian_shift_length;
    reflexivity.
- intros k Hk; rewrite paper_main_gaussian_shift_length in Hk.
  rewrite (paper_main_gaussian_shift_nth n _ eps _ k Hk).
  rewrite (paper_main_gaussian_shift_nth n _ eps _ k Hk).
  destruct (Nat.eq_dec k a) as [Hka|Hka].
  + subst k.
    rewrite (replace_coordinate_nth_same a t xs ltac:(lia)).
    rewrite (replace_coordinate_nth_same a (t + eps * z) xs ltac:(lia)).
    rewrite (paper_main_gaussian_insert_nth_same a z ws Hws).
    rewrite (paper_main_gaussian_insert_nth_same a 0 ws Hws); ring.
  + rewrite (replace_coordinate_nth_other a k t xs ltac:(lia)).
    rewrite (replace_coordinate_nth_other a k (t + eps * z) xs ltac:(lia)).
    rewrite <- (paper_main_gaussian_insert_replace a 0 z ws Hws).
    rewrite (replace_coordinate_nth_other a k 0 _ ltac:(lia)); reflexivity.
Qed.

Lemma paper_main_gaussian_replace_distance n xs a y y' :
  (a < n)%coq_nat -> List.length xs = n ->
  paper_main_gordon_distance n (replace_coordinate a y xs)
    (replace_coordinate a y' xs) = Rabs (y - y').
Proof.
intros Ha Hxs; unfold paper_main_gordon_distance.
assert (Hpt : forall k, In k (List.seq 0 n) ->
  (List.nth k (replace_coordinate a y xs) 0 -
   List.nth k (replace_coordinate a y' xs) 0) ^ 2 =
  (if Nat.eqb k a then (y - y') ^ 2 else 0)).
{ intros k Hk; apply in_seq in Hk.
  destruct (Nat.eqb_spec k a) as [Hka|Hka].
  - subst k.
    rewrite (replace_coordinate_nth_same a y xs ltac:(lia)).
    rewrite (replace_coordinate_nth_same a y' xs ltac:(lia)); reflexivity.
  - rewrite (replace_coordinate_nth_other a k y xs ltac:(lia)).
    rewrite (replace_coordinate_nth_other a k y' xs ltac:(lia)); ring. }
rewrite (finite_sum_ext _ _ _ Hpt).
rewrite (finite_sum_delta n a ((y - y') ^ 2) Ha).
rewrite <- (pow2_abs (y - y')).
apply sqrt_pow2; apply Rabs_pos.
Qed.

(* Conditional on the one-dimensional interface: the first candidate is the
   actual coordinate derivative of the smoothing. *)
Theorem paper_main_gaussian_smoothing_first_derivative_conditional n K L eps G a :
  paper_main_gaussian_shift_derivative_interface eps ->
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = n -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = n -> List.length ys = n ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance n xs ys) ->
  (a < n)%coq_nat ->
  finite_coordinate_derivative n a (paper_main_gaussian_smoothing n eps G)
    (paper_main_gaussian_smoothing_first n eps G a).
Proof.
intros Hint HK HL Heps HG HLip Ha xs Hxs.
destruct n as [|m]; [lia|].
set (h := fun y => gaussian_iterated_expectation m (fun ws =>
  G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
       (paper_main_gaussian_insert a 0 ws)))).
assert (Hcont : forall y, finite_joint_continuous m (fun ws =>
  G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
       (paper_main_gaussian_insert a 0 ws)))).
{ intros y.
  apply (paper_main_gaussian_insert_continuous m a
    (fun zs => G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps zs))).
  exact (paper_main_gaussian_smoothing_integrand_continuous (S m) L eps G
    (replace_coordinate a y xs) HL HLip). }
assert (Hbnd : forall y, finite_polynomial_bound m K 0 (fun ws =>
  G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
       (paper_main_gaussian_insert a 0 ws)))).
{ intros y; apply (proj2 (paper_main_polynomial_zero_bound m K _)); split;
    [exact HK|].
  intros ws _; apply HG; apply paper_main_gaussian_shift_length. }
assert (Hiy : forall y, gaussian_iterated_integrable m (fun ws =>
  G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
       (paper_main_gaussian_insert a 0 ws)))).
{ intros y; exact (proj1 (gaussian_coordinate_polynomial_domain m _ K 0
    (Hcont y) (Hbnd y))). }
assert (HhK : forall y, Rabs (h y) <= K).
{ intros y; unfold h; apply paper_main_gaussian_iterated_abs_le;
    [exact (Hiy y)|].
  intros ws _; apply HG; apply paper_main_gaussian_shift_length. }
assert (HhL : forall y y', Rabs (h y - h y') <= L * Rabs (y - y')).
{ intros y y'; unfold h.
  destruct (gaussian_iterated_difference m _ _ (Hiy y) (Hiy y')) as [HI HE].
  rewrite <- HE; apply paper_main_gaussian_iterated_abs_le; [exact HI|].
  intros ws _.
  eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
  rewrite paper_main_gaussian_shift_distance.
  rewrite (paper_main_gaussian_replace_distance (S m) xs a y y' Ha Hxs).
  apply Rle_refl. }
assert (Hfun : forall t,
  gaussian_expectation (fun z => h (t + eps * z)) =
  paper_main_gaussian_smoothing (S m) eps G (replace_coordinate a t xs)).
{ intros t; unfold paper_main_gaussian_smoothing.
  rewrite (paper_main_gaussian_iterated_front (S m) a _ K 0 Ha
    (paper_main_gaussian_smoothing_integrand_continuous (S m) L eps G
      (replace_coordinate a t xs) HL HLip)
    (paper_main_gaussian_smoothing_integrand_bound (S m) K eps G
      (replace_coordinate a t xs) HK HG)).
  rewrite paper_main_gaussian_iterated_succ.
  f_equal; apply functional_extensionality; intros z; unfold h.
  apply gaussian_iterated_expectation_ext; intros ws Hws.
  change (paper_main_gaussian_front a (z :: ws)) with
    (paper_main_gaussian_insert a z ws).
  rewrite (paper_main_gaussian_shift_insert (S m) xs eps a t z ws Ha Hxs
    ltac:(lia)); reflexivity. }
destruct (Hint h K L (List.nth a xs 0) HK HL HhK HhL) as [Hd1 _].
assert (Hval : / eps * gaussian_expectation
    (fun z => h (List.nth a xs 0 + eps * z) * z) =
  paper_main_gaussian_smoothing_first (S m) eps G a xs).
{ unfold paper_main_gaussian_smoothing_first; f_equal.
  rewrite (paper_main_gaussian_iterated_front (S m) a _ K 1 Ha
    (paper_main_gaussian_first_integrand_continuous (S m) L eps G a xs HL HLip Ha)
    (paper_main_gaussian_first_integrand_bound (S m) K eps G a xs HK HG Ha)).
  rewrite paper_main_gaussian_iterated_succ.
  f_equal; apply functional_extensionality; intros z; unfold h.
  rewrite Rmult_comm.
  destruct (gaussian_iterated_scale m _ z (Hiy (List.nth a xs 0 + eps * z)))
    as [_ HEs].
  rewrite <- HEs.
  apply gaussian_iterated_expectation_ext; intros ws Hws.
  change (paper_main_gaussian_front a (z :: ws)) with
    (paper_main_gaussian_insert a z ws).
  rewrite (paper_main_gaussian_insert_nth_same a z ws ltac:(lia)).
  pose proof (paper_main_gaussian_shift_insert (S m) xs eps a (List.nth a xs 0)
    z ws Ha Hxs ltac:(lia)) as Hsh.
  rewrite (replace_coordinate_self a xs) in Hsh.
  rewrite Hsh; reflexivity. }
apply (is_derive_ext (fun t => gaussian_expectation (fun z => h (t + eps * z)))).
- exact Hfun.
- rewrite <- Hval; exact Hd1.
Qed.

(* Second order. Profiles of the smoothing along one coordinate. *)

Lemma paper_main_gaussian_iterated_insert m a F C p :
  (a < S m)%coq_nat -> finite_joint_continuous (S m) F ->
  finite_polynomial_bound (S m) C p F ->
  gaussian_iterated_expectation (S m) F =
  gaussian_expectation (fun z => gaussian_iterated_expectation m
    (fun ws => F (paper_main_gaussian_insert a z ws))).
Proof.
intros Ha HC HB.
rewrite (paper_main_gaussian_iterated_front (S m) a F C p Ha HC HB).
rewrite paper_main_gaussian_iterated_succ; reflexivity.
Qed.

Lemma paper_main_gaussian_weight_zero_coordinate p :
  gaussian_coordinate_weight p 0 = 1.
Proof.
unfold gaussian_coordinate_weight; rewrite Rabs_R0; rewrite Rplus_0_r; apply pow1.
Qed.

Lemma paper_main_gaussian_insert_weight p a ws :
  gaussian_coordinate_product_weight p (paper_main_gaussian_insert a 0 ws) =
  gaussian_coordinate_product_weight p ws.
Proof.
revert ws; induction a as [|a IH]; intros [|w ws];
  cbn [paper_main_gaussian_insert gaussian_coordinate_product_weight].
- rewrite paper_main_gaussian_weight_zero_coordinate; ring.
- rewrite paper_main_gaussian_weight_zero_coordinate; ring.
- rewrite paper_main_gaussian_weight_zero_coordinate; ring.
- rewrite IH; reflexivity.
Qed.

Lemma paper_main_gaussian_insert_polynomial_bound m a C p F :
  finite_polynomial_bound (S m) C p F ->
  finite_polynomial_bound m C p (fun ws => F (paper_main_gaussian_insert a 0 ws)).
Proof.
intros [HC HF]; split; [exact HC|].
intros ws Hws.
rewrite <- (paper_main_gaussian_insert_weight p a ws).
apply HF; rewrite paper_main_gaussian_insert_length; rewrite Hws; reflexivity.
Qed.

Lemma paper_main_gaussian_insert_nth_other a b z ws :
  a <> b -> (b <= List.length ws)%coq_nat ->
  List.nth a (paper_main_gaussian_insert b z ws) 0 =
    List.nth a (paper_main_gaussian_insert b 0 ws) 0.
Proof.
intros Hab Hb.
rewrite <- (paper_main_gaussian_insert_replace b 0 z ws Hb).
symmetry; apply replace_coordinate_nth_other; lia.
Qed.

Definition paper_main_gaussian_profile m eps (G : list R -> R) xs a (y : R) : R :=
  gaussian_iterated_expectation m (fun ws =>
    G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
         (paper_main_gaussian_insert a 0 ws))).

Definition paper_main_gaussian_weighted_profile m eps (G : list R -> R) xs a b
    (y : R) : R :=
  gaussian_iterated_expectation m (fun ws =>
    List.nth a (paper_main_gaussian_insert b 0 ws) 0 *
    G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps
         (paper_main_gaussian_insert b 0 ws))).

Lemma paper_main_gaussian_profile_integrable m K L eps G xs a y :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  gaussian_iterated_integrable m (fun ws =>
    G (paper_main_gaussian_shift (S m) (replace_coordinate a y xs) eps
         (paper_main_gaussian_insert a 0 ws))).
Proof.
intros HK HL HG HLip.
exact (proj1 (gaussian_coordinate_polynomial_domain m _ K 0
  (paper_main_gaussian_insert_continuous m a _
    (paper_main_gaussian_smoothing_integrand_continuous (S m) L eps G
      (replace_coordinate a y xs) HL HLip))
  (paper_main_gaussian_insert_polynomial_bound m a K 0 _
    (paper_main_gaussian_smoothing_integrand_bound (S m) K eps G
      (replace_coordinate a y xs) HK HG)))).
Qed.

Lemma paper_main_gaussian_profile_bound m K L eps G xs a y :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  Rabs (paper_main_gaussian_profile m eps G xs a y) <= K.
Proof.
intros HK HL HG HLip; unfold paper_main_gaussian_profile.
apply paper_main_gaussian_iterated_abs_le.
- exact (paper_main_gaussian_profile_integrable m K L eps G xs a y HK HL HG HLip).
- intros ws _; apply HG; apply paper_main_gaussian_shift_length.
Qed.

Lemma paper_main_gaussian_profile_lipschitz m K L eps G xs a y y' :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat -> List.length xs = S m ->
  Rabs (paper_main_gaussian_profile m eps G xs a y -
        paper_main_gaussian_profile m eps G xs a y') <= L * Rabs (y - y').
Proof.
intros HK HL HG HLip Ha Hxs; unfold paper_main_gaussian_profile.
destruct (gaussian_iterated_difference m _ _
  (paper_main_gaussian_profile_integrable m K L eps G xs a y HK HL HG HLip)
  (paper_main_gaussian_profile_integrable m K L eps G xs a y' HK HL HG HLip))
  as [HI HE].
rewrite <- HE; apply paper_main_gaussian_iterated_abs_le; [exact HI|].
intros ws _.
eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
rewrite paper_main_gaussian_shift_distance.
rewrite (paper_main_gaussian_replace_distance (S m) xs a y y' Ha Hxs).
apply Rle_refl.
Qed.

Lemma paper_main_gaussian_weighted_profile_integrable m K L eps G xs a b y :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat ->
  gaussian_iterated_integrable m (fun ws =>
    List.nth a (paper_main_gaussian_insert b 0 ws) 0 *
    G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps
         (paper_main_gaussian_insert b 0 ws))).
Proof.
intros HK HL HG HLip Ha.
exact (proj1 (gaussian_coordinate_polynomial_domain m _ K 1
  (paper_main_gaussian_insert_continuous m b
    (fun zs => List.nth a zs 0 *
       G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps zs))
    (paper_main_gaussian_first_integrand_continuous (S m) L eps G a
      (replace_coordinate b y xs) HL HLip Ha))
  (paper_main_gaussian_insert_polynomial_bound m b K 1
    (fun zs => List.nth a zs 0 *
       G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps zs))
    (paper_main_gaussian_first_integrand_bound (S m) K eps G a
      (replace_coordinate b y xs) HK HG Ha)))).
Qed.

Lemma paper_main_gaussian_weighted_profile_bound m K L eps G xs a b y :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat ->
  Rabs (paper_main_gaussian_weighted_profile m eps G xs a b y) <=
    K * gaussian_coordinate_weight_moment 1 ^ m.
Proof.
intros HK HL HG HLip Ha; unfold paper_main_gaussian_weighted_profile.
apply paper_main_gaussian_iterated_weighted_abs_le.
- exact (paper_main_gaussian_weighted_profile_integrable m K L eps G xs a b y
    HK HL HG HLip Ha).
- exact (paper_main_gaussian_insert_polynomial_bound m b K 1
    (fun zs => List.nth a zs 0 *
       G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps zs))
    (paper_main_gaussian_first_integrand_bound (S m) K eps G a
      (replace_coordinate b y xs) HK HG Ha)).
Qed.

Lemma paper_main_gaussian_weighted_profile_lipschitz m K L eps G xs a b y y' :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat -> (b < S m)%coq_nat -> List.length xs = S m ->
  Rabs (paper_main_gaussian_weighted_profile m eps G xs a b y -
        paper_main_gaussian_weighted_profile m eps G xs a b y') <=
    (L * gaussian_coordinate_weight_moment 1 ^ m) * Rabs (y - y').
Proof.
intros HK HL HG HLip Ha Hb Hxs; unfold paper_main_gaussian_weighted_profile.
assert (HH : finite_polynomial_bound (S m) (L * Rabs (y - y')) 0
  (fun zs => G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps zs) -
             G (paper_main_gaussian_shift (S m) (replace_coordinate b y' xs) eps zs))).
{ apply (proj2 (paper_main_polynomial_zero_bound (S m) _ _)); split.
  - apply Rmult_le_pos; [exact HL|apply Rabs_pos].
  - intros zs _.
    eapply Rle_trans; [apply HLip; apply paper_main_gaussian_shift_length|].
    rewrite paper_main_gaussian_shift_distance.
    rewrite (paper_main_gaussian_replace_distance (S m) xs b y y' Hb Hxs).
    apply Rle_refl. }
assert (HB : finite_polynomial_bound m (L * Rabs (y - y')) 1 (fun ws =>
    List.nth a (paper_main_gaussian_insert b 0 ws) 0 *
      G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps
           (paper_main_gaussian_insert b 0 ws)) -
    List.nth a (paper_main_gaussian_insert b 0 ws) 0 *
      G (paper_main_gaussian_shift (S m) (replace_coordinate b y' xs) eps
           (paper_main_gaussian_insert b 0 ws)))).
{ apply (paper_main_gaussian_polynomial_bound_ext m _ 1 (fun ws =>
    List.nth a (paper_main_gaussian_insert b 0 ws) 0 *
      (G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps
            (paper_main_gaussian_insert b 0 ws)) -
       G (paper_main_gaussian_shift (S m) (replace_coordinate b y' xs) eps
            (paper_main_gaussian_insert b 0 ws))))).
  - intros ws _; ring.
  - apply (paper_main_gaussian_insert_polynomial_bound m b _ 1 (fun zs =>
      List.nth a zs 0 *
        (G (paper_main_gaussian_shift (S m) (replace_coordinate b y xs) eps zs) -
         G (paper_main_gaussian_shift (S m) (replace_coordinate b y' xs) eps zs)))).
    exact (finite_polynomial_bound_times_coordinate (S m) _ 0 _ a HH Ha). }
pose proof (gaussian_iterated_difference_bound m _ _ _ 1
  (paper_main_gaussian_weighted_profile_integrable m K L eps G xs a b y HK HL HG HLip Ha)
  (paper_main_gaussian_weighted_profile_integrable m K L eps G xs a b y' HK HL HG HLip Ha)
  HB) as Hdiff.
eapply Rle_trans; [exact Hdiff|right; ring].
Qed.

Lemma paper_main_gaussian_first_profile m K L eps G xs a t :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat -> List.length xs = S m ->
  paper_main_gaussian_smoothing_first (S m) eps G a (replace_coordinate a t xs) =
  / eps * gaussian_expectation
    (fun z => z * paper_main_gaussian_profile m eps G xs a (t + eps * z)).
Proof.
intros HK HL HG HLip Ha Hxs; unfold paper_main_gaussian_smoothing_first.
f_equal.
rewrite (paper_main_gaussian_iterated_insert m a _ K 1 Ha
  (paper_main_gaussian_first_integrand_continuous (S m) L eps G a
    (replace_coordinate a t xs) HL HLip Ha)
  (paper_main_gaussian_first_integrand_bound (S m) K eps G a
    (replace_coordinate a t xs) HK HG Ha)).
f_equal; apply functional_extensionality; intros z.
unfold paper_main_gaussian_profile.
destruct (gaussian_iterated_scale m _ z
  (paper_main_gaussian_profile_integrable m K L eps G xs a (t + eps * z)
    HK HL HG HLip)) as [_ HEs].
rewrite <- HEs.
apply gaussian_iterated_expectation_ext; intros ws Hws.
rewrite (paper_main_gaussian_insert_nth_same a z ws ltac:(lia)).
rewrite (paper_main_gaussian_shift_insert (S m) xs eps a t z ws Ha Hxs ltac:(lia)).
reflexivity.
Qed.

Lemma paper_main_gaussian_first_weighted_profile m K L eps G xs a b t :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  a <> b -> (a < S m)%coq_nat -> (b < S m)%coq_nat -> List.length xs = S m ->
  paper_main_gaussian_smoothing_first (S m) eps G a (replace_coordinate b t xs) =
  / eps * gaussian_expectation
    (fun z => paper_main_gaussian_weighted_profile m eps G xs a b (t + eps * z)).
Proof.
intros HK HL HG HLip Hab Ha Hb Hxs; unfold paper_main_gaussian_smoothing_first.
f_equal.
rewrite (paper_main_gaussian_iterated_insert m b _ K 1 Hb
  (paper_main_gaussian_first_integrand_continuous (S m) L eps G a
    (replace_coordinate b t xs) HL HLip Ha)
  (paper_main_gaussian_first_integrand_bound (S m) K eps G a
    (replace_coordinate b t xs) HK HG Ha)).
f_equal; apply functional_extensionality; intros z.
unfold paper_main_gaussian_weighted_profile.
apply gaussian_iterated_expectation_ext; intros ws Hws.
rewrite (paper_main_gaussian_insert_nth_other a b z ws Hab ltac:(lia)).
rewrite (paper_main_gaussian_shift_insert (S m) xs eps b t z ws Hb Hxs ltac:(lia)).
reflexivity.
Qed.

Lemma paper_main_gaussian_second_diagonal_profile m K L eps G xs a :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  (a < S m)%coq_nat -> List.length xs = S m ->
  paper_main_gaussian_smoothing_second (S m) eps G a a xs =
  / eps ^ 2 * gaussian_expectation (fun z => (z * z - 1) *
    paper_main_gaussian_profile m eps G xs a (List.nth a xs 0 + eps * z)).
Proof.
intros HK HL HG HLip Ha Hxs; unfold paper_main_gaussian_smoothing_second.
f_equal.
rewrite (paper_main_gaussian_iterated_insert m a _ K 2 Ha
  (paper_main_gaussian_second_integrand_continuous (S m) L eps G a a xs HL HLip Ha Ha)
  (paper_main_gaussian_second_integrand_bound (S m) K eps G a a xs HK HG Ha Ha)).
f_equal; apply functional_extensionality; intros z.
unfold paper_main_gaussian_profile.
destruct (gaussian_iterated_scale m _ (z * z - 1)
  (paper_main_gaussian_profile_integrable m K L eps G xs a
    (List.nth a xs 0 + eps * z) HK HL HG HLip)) as [_ HEs].
rewrite <- HEs.
apply gaussian_iterated_expectation_ext; intros ws Hws.
unfold paper_main_gaussian_hermite_pair; rewrite Nat.eqb_refl.
rewrite (paper_main_gaussian_insert_nth_same a z ws ltac:(lia)).
pose proof (paper_main_gaussian_shift_insert (S m) xs eps a (List.nth a xs 0)
  z ws Ha Hxs ltac:(lia)) as Hsh.
rewrite (replace_coordinate_self a xs) in Hsh.
rewrite Hsh; reflexivity.
Qed.

Lemma paper_main_gaussian_second_offdiagonal_profile m K L eps G xs a b :
  0 <= K -> 0 <= L ->
  (forall xs, List.length xs = S m -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = S m -> List.length ys = S m ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance (S m) xs ys) ->
  a <> b -> (a < S m)%coq_nat -> (b < S m)%coq_nat -> List.length xs = S m ->
  paper_main_gaussian_smoothing_second (S m) eps G a b xs =
  / eps ^ 2 * gaussian_expectation (fun z =>
    paper_main_gaussian_weighted_profile m eps G xs a b (List.nth b xs 0 + eps * z) * z).
Proof.
intros HK HL HG HLip Hab Ha Hb Hxs; unfold paper_main_gaussian_smoothing_second.
f_equal.
rewrite (paper_main_gaussian_iterated_insert m b _ K 2 Hb
  (paper_main_gaussian_second_integrand_continuous (S m) L eps G a b xs HL HLip Ha Hb)
  (paper_main_gaussian_second_integrand_bound (S m) K eps G a b xs HK HG Ha Hb)).
f_equal; apply functional_extensionality; intros z.
unfold paper_main_gaussian_weighted_profile.
rewrite Rmult_comm.
destruct (gaussian_iterated_scale m _ z
  (paper_main_gaussian_weighted_profile_integrable m K L eps G xs a b
    (List.nth b xs 0 + eps * z) HK HL HG HLip Ha)) as [_ HEs].
rewrite <- HEs.
apply gaussian_iterated_expectation_ext; intros ws Hws.
unfold paper_main_gaussian_hermite_pair.
rewrite (proj2 (Nat.eqb_neq a b) Hab).
rewrite (paper_main_gaussian_insert_nth_other a b z ws Hab ltac:(lia)).
rewrite (paper_main_gaussian_insert_nth_same b z ws ltac:(lia)).
pose proof (paper_main_gaussian_shift_insert (S m) xs eps b (List.nth b xs 0)
  z ws Hb Hxs ltac:(lia)) as Hsh.
rewrite (replace_coordinate_self b xs) in Hsh.
rewrite Hsh; ring.
Qed.

(* Conditional on the one-dimensional interface: the second candidate is the
   coordinate-b derivative of the first candidate in coordinate a. *)
Theorem paper_main_gaussian_smoothing_second_derivative_conditional n K L eps G a b :
  paper_main_gaussian_shift_derivative_interface eps ->
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = n -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = n -> List.length ys = n ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance n xs ys) ->
  (a < n)%coq_nat -> (b < n)%coq_nat ->
  finite_coordinate_derivative n b (paper_main_gaussian_smoothing_first n eps G a)
    (paper_main_gaussian_smoothing_second n eps G a b).
Proof.
intros Hint HK HL Heps HG HLip Ha Hb xs Hxs.
destruct n as [|m]; [lia|].
assert (Hinv : / eps ^ 2 = / eps * / eps) by (field; lra).
destruct (Nat.eq_dec a b) as [Hab|Hab].
- subst b.
  destruct (Hint (paper_main_gaussian_profile m eps G xs a) K L (List.nth a xs 0)
    HK HL
    (fun y => paper_main_gaussian_profile_bound m K L eps G xs a y HK HL HG HLip)
    (fun y y' => paper_main_gaussian_profile_lipschitz m K L eps G xs a y y'
       HK HL HG HLip Ha Hxs)) as [_ Hd2].
  apply (is_derive_ext (fun t => / eps * gaussian_expectation
    (fun z => z * paper_main_gaussian_profile m eps G xs a (t + eps * z)))).
  + intros t; symmetry;
      exact (paper_main_gaussian_first_profile m K L eps G xs a t HK HL HG HLip Ha Hxs).
  + rewrite (paper_main_gaussian_second_diagonal_profile m K L eps G xs a
      HK HL HG HLip Ha Hxs).
    rewrite Hinv; rewrite Rmult_assoc.
    apply is_derive_scal; exact Hd2.
- assert (HK' : 0 <= K * gaussian_coordinate_weight_moment 1 ^ m)
    by (apply Rmult_le_pos; [exact HK|apply paper_main_gaussian_moment_power_nonnegative]).
  assert (HL' : 0 <= L * gaussian_coordinate_weight_moment 1 ^ m)
    by (apply Rmult_le_pos; [exact HL|apply paper_main_gaussian_moment_power_nonnegative]).
  destruct (Hint (paper_main_gaussian_weighted_profile m eps G xs a b)
    (K * gaussian_coordinate_weight_moment 1 ^ m)
    (L * gaussian_coordinate_weight_moment 1 ^ m) (List.nth b xs 0) HK' HL'
    (fun y => paper_main_gaussian_weighted_profile_bound m K L eps G xs a b y
       HK HL HG HLip Ha)
    (fun y y' => paper_main_gaussian_weighted_profile_lipschitz m K L eps G xs a b y y'
       HK HL HG HLip Ha Hb Hxs)) as [Hd1 _].
  apply (is_derive_ext (fun t => / eps * gaussian_expectation
    (fun z => paper_main_gaussian_weighted_profile m eps G xs a b (t + eps * z)))).
  + intros t; symmetry;
      exact (paper_main_gaussian_first_weighted_profile m K L eps G xs a b t
        HK HL HG HLip Hab Ha Hb Hxs).
  + rewrite (paper_main_gaussian_second_offdiagonal_profile m K L eps G xs a b
      HK HL HG HLip Hab Ha Hb Hxs).
    rewrite Hinv; rewrite Rmult_assoc.
    apply is_derive_scal; exact Hd1.
Qed.

(* Conditional assembly: given the one-dimensional interface, the Gaussian
   smoothing of a bounded Euclidean-Lipschitz test is a bounded C2 smooth
   test in the sense of paper_main_gaussian_smooth_test, with an explicit
   bound, and its squared gradient norm is at most L^2. These are exactly
   the hypotheses of the bounded smooth MGF and tail results. *)
Definition paper_main_gaussian_smoothing_constant n K eps : R :=
  Rmax K (Rmax (/ eps * (K * gaussian_coordinate_weight_moment 1 ^ n))
               (/ eps ^ 2 * (K * gaussian_coordinate_weight_moment 2 ^ n))).

Theorem paper_main_gaussian_smoothing_smooth_test_conditional n K L eps G :
  paper_main_gaussian_shift_derivative_interface eps ->
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = n -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = n -> List.length ys = n ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance n xs ys) ->
  paper_main_gaussian_smooth_test n (paper_main_gaussian_smoothing n eps G)
    (paper_main_gaussian_smoothing_first n eps G)
    (paper_main_gaussian_smoothing_second n eps G)
    (paper_main_gaussian_smoothing_constant n K eps) 0.
Proof.
intros Hint HK HL Heps HG HLip.
set (M := paper_main_gaussian_smoothing_constant n K eps).
assert (HKM : K <= M) by (unfold M, paper_main_gaussian_smoothing_constant; apply Rmax_l).
assert (H1M : / eps * (K * gaussian_coordinate_weight_moment 1 ^ n) <= M).
{ unfold M, paper_main_gaussian_smoothing_constant.
  eapply Rle_trans; [apply Rmax_l|apply Rmax_r]. }
assert (H2M : / eps ^ 2 * (K * gaussian_coordinate_weight_moment 2 ^ n) <= M).
{ unfold M, paper_main_gaussian_smoothing_constant.
  eapply Rle_trans; [apply Rmax_r|apply Rmax_r]. }
assert (HM : 0 <= M) by lra.
constructor.
- exact (paper_main_gaussian_smoothing_continuous n K L eps G HK HL HG HLip).
- intros a Ha.
  exact (paper_main_gaussian_smoothing_first_derivative_conditional n K L eps G a
    Hint HK HL Heps HG HLip Ha).
- intros a Ha.
  exact (paper_main_gaussian_smoothing_first_continuous n K L eps G a
    HK HL Heps HG HLip Ha).
- intros a b Ha Hb.
  exact (paper_main_gaussian_smoothing_second_derivative_conditional n K L eps G a b
    Hint HK HL Heps HG HLip Ha Hb).
- intros a b Ha Hb.
  exact (paper_main_gaussian_smoothing_second_continuous n K L eps G a b
    HK HL Heps HG HLip Ha Hb).
- apply (proj2 (paper_main_polynomial_zero_bound n M _)); split; [exact HM|].
  intros xs _.
  eapply Rle_trans;
    [exact (paper_main_gaussian_smoothing_bound n K L eps G xs HK HL HG HLip)|exact HKM].
- intros a Ha.
  apply (proj2 (paper_main_polynomial_zero_bound n M _)); split; [exact HM|].
  intros xs _.
  eapply Rle_trans;
    [exact (paper_main_gaussian_smoothing_first_bound n K L eps G a xs
       HK HL Heps HG HLip Ha)|exact H1M].
- intros a b Ha Hb.
  apply (proj2 (paper_main_polynomial_zero_bound n M _)); split; [exact HM|].
  intros xs _.
  eapply Rle_trans;
    [exact (paper_main_gaussian_smoothing_second_bound n K L eps G a b xs
       HK HL Heps HG HLip Ha Hb)|exact H2M].
Qed.

Theorem paper_main_gaussian_smoothing_gradient_conditional n K L eps G :
  paper_main_gaussian_shift_derivative_interface eps ->
  0 <= K -> 0 <= L -> 0 < eps ->
  (forall xs, List.length xs = n -> Rabs (G xs) <= K) ->
  (forall xs ys, List.length xs = n -> List.length ys = n ->
    Rabs (G xs - G ys) <= L * paper_main_gordon_distance n xs ys) ->
  forall xs, List.length xs = n ->
    finite_sum (fun a => paper_main_gaussian_smoothing_first n eps G a xs ^ 2)
      (List.seq 0 n) <= L ^ 2.
Proof.
intros Hint HK HL Heps HG HLip.
apply (paper_main_gaussian_lipschitz_gradient n
  (paper_main_gaussian_smoothing n eps G) (paper_main_gaussian_smoothing_first n eps G) L).
- intros a Ha.
  exact (paper_main_gaussian_smoothing_first_derivative_conditional n K L eps G a
    Hint HK HL Heps HG HLip Ha).
- intros a Ha.
  exact (paper_main_gaussian_smoothing_first_continuous n K L eps G a
    HK HL Heps HG HLip Ha).
- exact HL.
- exact (paper_main_gaussian_smoothing_lipschitz n K L eps G HK HL HG HLip).
Qed.
