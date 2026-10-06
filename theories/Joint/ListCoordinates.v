From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions Matrix.VectorListDefinitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Tuples
  Gaussian.Coordinate.Weights Matrix.VectorCoordinates
  Matrix.VectorCoordinateContinuity Gaussian.Vector.PolynomialGrowth
  Joint.Definitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Joint vectors (x, z), with x in vector m and z in vector n, as lists of
   S m + S n coordinates. A joint vector has type
   euclidean_product (vector_NormedModule m) (vector_NormedModule n), whose
   norm is the Euclidean norm of all its coordinates.
   - joint_vector_of_to_list and joint_vector_to_of_list:
     joint_vector_to_list and joint_vector_of_list are inverse to each
     other, on lists of length S m + S n.
   - joint_continuous_pullback: if (x, z) |-> F x z is continuous on joint
     vectors, its pullback gaussian_pair_pullback m n F to lists is jointly
     continuous (finite_joint_continuous).
   - joint_polynomial_pullback: a bound C * (1 + `|xz|) ^ p on joint vectors
     gives the polynomial bound finite_polynomial_bound with the same C and
     p for the pullback, since 1 + `|xz| is at most the product weight of
     degree 1 of the coordinates (joint_norm_product_weight). *)

Lemma joint_vector_to_list_length m n
    (xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n)) :
  length (joint_vector_to_list m n xz) = (S m + S n)%coq_nat.
Proof.
  unfold joint_vector_to_list.
  rewrite List.length_app !vector_to_list_length; reflexivity.
Qed.

Lemma joint_prefix_append m (xs ys : list R) :
  length xs = S m -> firstn (S m) (xs ++ ys)%list = xs.
Proof.
  intro H; rewrite List.firstn_app H Nat.sub_diag.
  have HL : (length xs <= S m)%coq_nat by lia.
  rewrite (List.firstn_all2 xs HL); simpl; apply List.app_nil_r.
Qed.

Lemma joint_suffix_append m (xs ys : list R) :
  length xs = S m -> skipn (S m) (xs ++ ys)%list = ys.
Proof.
  intro H; rewrite List.skipn_app H Nat.sub_diag.
  have HL : (length xs <= S m)%coq_nat by lia.
  rewrite (List.skipn_all2 xs HL); reflexivity.
Qed.

Lemma joint_vector_of_append m n (xs ys : list R) :
  length xs = S m ->
  joint_vector_of_list m n (xs ++ ys)%list = (vector_of_list m xs, vector_of_list n ys).
Proof.
  intro H; unfold joint_vector_of_list.
  rewrite (joint_prefix_append m xs ys H) (joint_suffix_append m xs ys H); reflexivity.
Qed.

Lemma joint_vector_of_to_list m n
    (xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n)) :
  joint_vector_of_list m n (joint_vector_to_list m n xz) = xz.
Proof.
  destruct xz as [x z]; unfold joint_vector_to_list; cbn [fst snd].
  rewrite (joint_vector_of_append m n _ _ (vector_to_list_length m x)).
  rewrite !vector_of_to_list; reflexivity.
Qed.

Lemma joint_list_section_lengths m n (xs : list R) :
  length xs = (S m + S n)%coq_nat ->
  length (firstn (S m) xs) = S m /\ length (skipn (S m) xs) = S n.
Proof.
  intro H; rewrite List.length_firstn List.length_skipn H; split; lia.
Qed.

Lemma joint_vector_to_of_list m n (xs : list R) :
  length xs = (S m + S n)%coq_nat ->
  joint_vector_to_list m n (joint_vector_of_list m n xs) = xs.
Proof.
  intro H; destruct (joint_list_section_lengths m n xs H) as [H1 H2].
  unfold joint_vector_to_list, joint_vector_of_list; cbn [fst snd].
  rewrite (vector_to_of_list m _ H1) (vector_to_of_list n _ H2).
  apply List.firstn_skipn.
Qed.

Lemma gaussian_pair_pullback_append m n (F : vector m -> vector n -> R)
    (xs ys : list R) :
  length xs = S m ->
  gaussian_pair_pullback m n F (xs ++ ys)%list = F (vector_of_list m xs) (vector_of_list n ys).
Proof.
  intro H; unfold gaussian_pair_pullback.
  rewrite (joint_vector_of_append m n xs ys H); reflexivity.
Qed.

(* If every coordinate of b is within e of the same coordinate of a, the
   joint vectors are within INR (S m + S n) * e for the Euclidean norm,
   which is at most the sum of the absolute values of the coordinates. A
   radius of e alone does not follow: for m = n = 0, the joint vector with
   both coordinates 3 * e / 4 is at distance (3 / 4) * sqrt 2 * e > e
   from 0. *)
Lemma joint_of_coordinates_ball m n (a b : Tn (S m + S n)%coq_nat R) e :
  close_n (S m + S n)%coq_nat e b a ->
  ball (joint_vector_of_list m n (coordinates_to_list (S m + S n)%coq_nat a))
    (Rmult (INR (S m + S n)%coq_nat) e)
    (joint_vector_of_list m n (coordinates_to_list (S m + S n)%coq_nat b)).
Proof.
  intro H.
  have Hc := proj1 (coordinates_close_iff (S m + S n)%coq_nat e b a) H.
  set xa := coordinates_to_list (S m + S n)%coq_nat a.
  set xb := coordinates_to_list (S m + S n)%coq_nat b.
  fold xa xb in Hc.
  assert (H1 : ball (vector_of_list m (firstn (S m) xa)) (Rmult (INR (S m)) e)
    (vector_of_list m (firstn (S m) xb))).
  { apply (proj2 (vector_ball_coordinates m _ _ e)); intros i Hi.
    rewrite (vector_entry_of_list m _ i Hi) (vector_entry_of_list m _ i Hi).
    rewrite !List.nth_firstn.
    assert (Hlt : Nat.ltb i (S m) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt; apply Hc; lia. }
  assert (H2 : ball (vector_of_list n (skipn (S m) xa)) (Rmult (INR (S n)) e)
    (vector_of_list n (skipn (S m) xb))).
  { apply (proj2 (vector_ball_coordinates n _ _ e)); intros i Hi.
    rewrite (vector_entry_of_list n _ i Hi) (vector_entry_of_list n _ i Hi).
    rewrite !List.nth_skipn.
    apply Hc; lia. }
  have HB := @euclidean_product_ball_add (vector_NormedModule m) (vector_NormedModule n)
    (joint_vector_of_list m n xa) (Rmult (INR (S m)) e) (Rmult (INR (S n)) e)
    (joint_vector_of_list m n xb) H1 H2.
  replace (Rmult (INR (S m + S n)%coq_nat) e) with
    (Rmult (INR (S m)) e + Rmult (INR (S n)) e)%R.
  - exact HB.
  - change (INR (S m) * e + INR (S n) * e = INR (S m + S n)%coq_nat * e).
    rewrite plus_INR; ring.
Qed.

Theorem joint_continuous_pullback m n (F : vector m -> vector n -> R) :
  (forall xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n),
    {for xz, continuous (fun yz : euclidean_product (vector_NormedModule m) (vector_NormedModule n) =>
      F (fst yz) (snd yz))}) ->
  finite_joint_continuous (S m + S n)%coq_nat (gaussian_pair_pullback m n F).
Proof.
  intros HC a eps.
  set x0 := joint_vector_of_list m n (coordinates_to_list (S m + S n)%coq_nat a).
  assert (Hout : nbhs (F (fst x0) (snd x0))
    (fun r : R => Rabs (r - F (fst x0) (snd x0)) < eps)).
  { apply/nbhs_ballP; exists (pos eps); [apply/RltP; exact (cond_pos eps)|].
    intros r Hr0.
    have /RltP Hr : is_true (`|F (fst x0) (snd x0) - r| < pos eps)%R by exact Hr0.
    change (Rabs (F (fst x0) (snd x0) - r) < eps) in Hr.
    rewrite Rabs_minus_sym; exact Hr. }
  have /nbhs_ballP [delta delta0 Hd] := HC x0 _ Hout.
  have Hdelta : 0 < delta by apply/RltP.
  have HS : 0 < INR (S m + S n)%coq_nat by apply lt_0_INR; lia.
  exists (mkposreal (delta / INR (S m + S n)%coq_nat) (Rdiv_lt_0_compat _ _ Hdelta HS)).
  intros b Hb; simpl in Hb.
  apply (Hd (joint_vector_of_list m n (coordinates_to_list (S m + S n)%coq_nat b))).
  have HB := joint_of_coordinates_ball m n a b _ Hb.
  replace delta with (Rmult (INR (S m + S n)%coq_nat) (delta / INR (S m + S n)%coq_nat)).
  - exact HB.
  - field; lra.
Qed.

Lemma joint_norm_product_weight m n
    (xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n)) :
  1 + (`|xz|)%R <= gaussian_coordinate_product_weight 1 (joint_vector_to_list m n xz).
Proof.
  destruct xz as [x z]; unfold joint_vector_to_list; cbn [fst snd].
  rewrite gaussian_coordinate_product_weight_append.
  assert (Hx : 0 <= (`|x|)%R) by (apply/RleP; apply normr_ge0).
  assert (Hz : 0 <= (`|z|)%R) by (apply/RleP; apply normr_ge0).
  eapply Rle_trans with ((1 + (`|x|)%R) * (1 + (`|z|)%R)).
  - pose proof (@vector_growth_pair_bound (vector_NormedModule m) (vector_NormedModule n) x z).
    nra.
  - apply Rmult_le_compat.
    + lra.
    + lra.
    + apply vector_norm_product_weight.
    + apply vector_norm_product_weight.
Qed.

Lemma joint_of_list_norm_product_weight m n (xs : list R) :
  length xs = (S m + S n)%coq_nat ->
  1 + (`|joint_vector_of_list m n xs|)%R <= gaussian_coordinate_product_weight 1 xs.
Proof.
  intro H; pose proof (joint_norm_product_weight m n (joint_vector_of_list m n xs)) as HB.
  rewrite (joint_vector_to_of_list m n xs H) in HB; exact HB.
Qed.

Theorem joint_polynomial_pullback m n (F : vector m -> vector n -> R) C p :
  0 <= C ->
  (forall xz : euclidean_product (vector_NormedModule m) (vector_NormedModule n),
    Rabs (F (fst xz) (snd xz)) <= C * (1 + (`|xz|)%R)^p) ->
  finite_polynomial_bound (S m + S n)%coq_nat C p (gaussian_pair_pullback m n F).
Proof.
  intros HC HF; split; [exact HC|]; intros xs Hxs.
  specialize (HF (joint_vector_of_list m n xs)).
  pose proof (joint_of_list_norm_product_weight m n xs Hxs) as HW.
  assert (HN : 0 <= 1 + (`|joint_vector_of_list m n xs|)%R).
  { assert (0 <= (`|joint_vector_of_list m n xs|)%R) by (apply/RleP; apply normr_ge0).
    lra. }
  pose proof (pow_incr (1 + (`|joint_vector_of_list m n xs|)%R)
    (gaussian_coordinate_product_weight 1 xs) p (conj HN HW)) as HP.
  rewrite -vector_growth_product_weight_power in HP.
  unfold gaussian_pair_pullback; nra.
Qed.
