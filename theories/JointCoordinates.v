From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions VectorCoordinateDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateBasics GaussianCoordinateWeights VectorCoordinates
  VectorCoordinateContinuity GaussianVectorGrowth JointDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Port of the inner module JointCoordinates of
   theories/InterpolationProofs.v (and of its identical copy in
   theories/JointProofs.v), extracted to
   build/agent2/unbundled/JointCoordinates.v, from Coquelicot to
   MathComp-Analysis, as a standalone module.

   The original imported the bundles GaussianCoordinateProofs and
   GaussianVectorProofs and named their inner modules GaussianCoordinateBasics,
   GaussianCoordinateWeights, VectorCoordinates, VectorCoordinateContinuity
   and GaussianVectorGrowth through them. The port imports these five
   standalone ported modules directly. It does not import Coquelicot's
   Compactness: Tn and close_n come from the ported
   GaussianCoordinateDefinitions, where they are copies of Coquelicot's.

   Every lemma and theorem keeps its name and its arguments in the same
   order. No item is added. The statements change form in the following
   ways.

   1. Joint vectors. Coquelicot's
        prod_NormedModule R_AbsRing (vector_NormedModule m) (vector_NormedModule n)
      becomes
        euclidean_product (vector_NormedModule m) (vector_NormedModule n),
      the type of joint vectors of the ported JointDefinitions. Its elements
      are the same pairs, and its norm is Coquelicot's product norm
      sqrt (norm (fst xz) ^ 2 + norm (snd xz) ^ 2), so Coquelicot's norm xz
      becomes MathComp's (`|xz|)%R with the same value. This concerns
      joint_vector_to_list_length, joint_vector_of_to_list,
      joint_norm_product_weight and joint_polynomial_pullback, which say the
      same thing as before.

   2. Pointwise continuity. In joint_continuous_pullback, Coquelicot's
      continuous (fun yz => F (fst yz) (snd yz)) xz becomes
      {for xz, continuous (fun yz : euclidean_product ... => F (fst yz) (snd yz))}
      (difference 5 of analysis/README.md). The bound variable is typed with
      the joint type, so that continuity refers to its topology, which is the
      product topology (euclidean_product_nbhsE), as in Coquelicot. The
      statement is the same.

   3. Naturals and lists. With ssreflect loaded, + on nat would mean ssrnat's
      addn and ++ MathComp's seq.cat. The statements write
      (S m + S n)%coq_nat and (xs ++ ys)%list, which are Stdlib's Nat.add and
      List.app of the original and of the ported JointDefinitions.

   The forms of 1, 2 and 3 are those of the four clauses of group 1 of the
   restated challenge ellipsoid_joint
   (analysis/challenges/ellipsoid_joint/Challenge.v), so that
   joint_vector_of_to_list, joint_vector_to_of_list,
   joint_continuous_pullback and joint_polynomial_pullback prove them with
   exact, as in theories/JointResults.v.

   One statement changes meaning.

   4. joint_of_coordinates_ball. In Coquelicot the ball of the product
      prod_NormedModule is the conjunction of the balls of its components,
      and so, by induction, the ball of joint vectors of radius e is
      closeness of all the S m + S n coordinates within e. The original
      concluded a ball of radius e from coordinates within e. In the port,
      the ball of euclidean_product, and of the vectors that nest it, is the
      ball of the Euclidean norm (blocker-notes.md, MatrixDefinitions), and
      a ball of radius e no longer follows: for m = n = 0, the joint vector
      with both coordinates e / 2 + e / 4 lies at distance
      (3 / 4) sqrt 2 e > e from 0. The port concludes a ball of radius
      INR (S m + S n) * e, since the norm is at most the sum of the absolute
      values of the coordinates (vector_ball_coordinates of the ported
      VectorCoordinateContinuity for each block, then
      euclidean_product_ball_add). The radius is written Rmult, Stdlib's
      product, because the radius argument of MathComp's ball is read in
      ring_scope. Its only user in this module is joint_continuous_pullback,
      whose proof now divides the radius of continuity by INR (S m + S n).
      Its only user in theories/ outside the bundles is gaussian_row_pair_ball
      of RowDecoderRegularity, which uses it to prove continuity and has to
      be restated with the same factor.

   The proofs follow the original ones. Coquelicot's norm_ge_0 becomes
   MathComp's normr_ge0 through RleP. Stdlib's "rewrite A, B by tac", which
   does not parse once ssreflect is loaded, is replaced by rewrites with
   explicit side conditions. *)

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

(* Changed meaning (item 4 of the header): the radius of the ball is
   INR (S m + S n) * e instead of e, because the ball on joint vectors is
   now the ball of the Euclidean norm, not the conjunction of the
   coordinate balls. *)
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
