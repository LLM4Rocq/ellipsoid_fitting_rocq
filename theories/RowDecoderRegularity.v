From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions GoeDefinitions JointDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateBasics GaussianCoordinateTopology GaussianCoordinateWeights
  GaussianPermutationContinuity GaussianBlockPermutation JointCoordinates JointContinuity
  GaussianVectorGrowth LowerDefinitions MatrixThirdContinuity
  RowCoordinateDefinitions RowCoordinates RowArrayDefinitions.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/RowDecoderRegularity.v from Coquelicot to
   MathComp-Analysis.

   Imports. The original imported the bundles GaussianCoordinateProofs,
   InterpolationFoundations and InterpolationProofs and named eight of their
   inner modules through them. The port imports the eight standalone ported
   modules directly: GaussianCoordinateBasics, GaussianCoordinateTopology,
   GaussianCoordinateWeights and GaussianPermutationContinuity (from
   GaussianCoordinateProofs), GaussianBlockPermutation, JointCoordinates and
   JointContinuity (from InterpolationProofs.JointProofs), and
   GaussianVectorGrowth (from InterpolationFoundations.GaussianVectorProofs).
   The other imports are those of the original.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. The statements change form in the following ways.

   1. Naturals. With ssreflect loaded, (i <= m)%nat means ssrnat's boolean
      leq, and + and * on nat mean ssrnat's addn and muln. The original means
      Stdlib's Peano order le and Nat.add, Nat.mul, so the statements write
      (i <= m)%coq_nat and (S m * (S n + S (goe_vector_index n)))%coq_nat,
      which denote these Stdlib functions. The dimension of the coordinate
      space is therefore the same term as in the original and in the ported
      RowArrayDefinitions and JointCoordinates.

   2. Pointwise continuity. Coquelicot's continuous f a becomes MathComp's
      {for a, continuous f} (difference 5 of analysis/README.md). The domain
      is coordinates_uniform_space of the ported GaussianCoordinateTopology, a
      type copy of Tn d R whose balls are close_n, as in the original, so its
      neighbourhoods are the same. The codomains are the joint vectors
      euclidean_product (vector_NormedModule n)
      (vector_NormedModule (goe_vector_index n)) of the ported JointDefinitions,
      matrix n, and the block arrays tuple_NormedModule (matrix_NormedModule n)
      m, with MathComp's norm topologies. These norms are Coquelicot's
      Euclidean and Frobenius norms (MatrixDefinitions), so the topologies are
      those of the original, where the product topology was used; for the
      joint vectors this is euclidean_product_nbhsE of MatrixEuclideanProduct.
      This concerns gaussian_row_pair_continuous,
      gaussian_row_matrix_continuous and gaussian_row_array_continuous, which
      say the same thing as before.

   3. Norms. Coquelicot's norm of a joint vector becomes MathComp's
      (`|...|)%R. The norm of euclidean_product is Coquelicot's product norm
      sqrt (norm (fst xz) ^ 2 + norm (snd xz) ^ 2), so the value is the same.
      This concerns gaussian_row_pair_norm_weight and
      gaussian_row_pair_squared_weight, which say the same thing as before.

   One statement changes meaning.

   4. gaussian_row_pair_ball. In Coquelicot the ball of joint vectors of
      radius e was closeness of all the coordinates within e, and the original
      concluded a ball of radius e. In the port the ball of euclidean_product,
      and of the vectors that nest it, is the ball of the Euclidean norm, and
      a ball of radius e no longer follows. As for joint_of_coordinates_ball
      of the ported JointCoordinates, from which it is proved, the conclusion
      is a ball of radius INR (S n + S (goe_vector_index n)) * e. The radius
      is written Rmult, Stdlib's product, because the radius argument of
      MathComp's ball is read in ring_scope. Its only user, here and in
      theories/, is gaussian_row_pair_continuous, whose proof now divides the
      radius of continuity by INR (S n + S (goe_vector_index n)).

   The proofs follow the original ones. Coquelicot's epsilon-delta unfolding
   of continuity becomes nbhs_ballP on both sides. Coquelicot's norm_ge_0
   becomes MathComp's normr_ge0 through RleP, and its continuous_comp becomes
   MathComp's continuous_comp, with the spaces given explicitly. Stdlib's
   "rewrite <- H at 1" and "rewrite A, B by tac", which do not parse once
   ssreflect is loaded, become ssreflect rewrites with explicit side
   conditions.

   Assumptions. Print Assumptions on the items of this module lists only
   axioms of analysis/README.md: the seven for every item except
   row_chunk_product_weight, which rests on two of them
   (ClassicalDedekindReals.sig_forall_dec and
   FunctionalExtensionality.functional_extensionality_dep, through Stdlib's
   reals). *)

Lemma row_chunk_product_weight p K i (xs : list R) :
  gaussian_coordinate_product_weight p (row_chunk K i xs) <=
  gaussian_coordinate_product_weight p xs.
Proof.
  pose proof (row_three_parts K i xs) as HE.
  pose proof (gaussian_coordinate_product_weight_at_least_one p (firstn (i*K)%coq_nat xs)) as HA.
  pose proof (gaussian_coordinate_product_weight_at_least_one p (row_chunk K i xs)) as HB.
  pose proof (gaussian_coordinate_product_weight_at_least_one p (skipn ((S i)*K)%coq_nat xs)) as HC.
  assert (HW : gaussian_coordinate_product_weight p xs =
    gaussian_coordinate_product_weight p (firstn (i*K)%coq_nat xs) *
    (gaussian_coordinate_product_weight p (row_chunk K i xs) *
     gaussian_coordinate_product_weight p (skipn ((S i)*K)%coq_nat xs))).
  { rewrite -{1}HE !gaussian_coordinate_product_weight_append; reflexivity. }
  rewrite HW.
  assert (HT : gaussian_coordinate_product_weight p (row_chunk K i xs) <=
    gaussian_coordinate_product_weight p (row_chunk K i xs) *
    gaussian_coordinate_product_weight p (skipn ((S i)*K)%coq_nat xs)) by nra.
  nra.
Qed.

(* Changed meaning (item 4 of the header): the radius of the ball is
   INR (S n + S (goe_vector_index n)) * e instead of e, because the ball on
   joint vectors is now the ball of the Euclidean norm. *)
Lemma gaussian_row_pair_ball n m i (e : posreal) xs ys :
  (i <= m)%coq_nat ->
  length xs = (S m * (S n + S (goe_vector_index n)))%coq_nat ->
  length ys = (S m * (S n + S (goe_vector_index n)))%coq_nat ->
  List.Forall2 (fun x y => Rabs (x-y)<e) ys xs ->
  ball (gaussian_row_pair n i xs) (Rmult (INR (S n + S (goe_vector_index n))%coq_nat) e)
    (gaussian_row_pair n i ys).
Proof.
  intros Hi HX HY HC.
  pose proof (row_chunk_length (S m) (S n+S(goe_vector_index n))%coq_nat i xs HX ltac:(lia)) as LX.
  pose proof (row_chunk_length (S m) (S n+S(goe_vector_index n))%coq_nat i ys HY ltac:(lia)) as LY.
  pose proof (joint_of_coordinates_ball n (goe_vector_index n)
    (coordinates_of_list _ (row_chunk (S n+S(goe_vector_index n))%coq_nat i xs))
    (coordinates_of_list _ (row_chunk (S n+S(goe_vector_index n))%coq_nat i ys)) e) as H.
  rewrite (coordinates_list_roundtrip _ _ LX) (coordinates_list_roundtrip _ _ LY) in H.
  apply H; apply coordinates_close_forall2.
  rewrite (coordinates_list_roundtrip _ _ LX) (coordinates_list_roundtrip _ _ LY).
  unfold row_chunk; apply block_firstn_forall2; apply block_skipn_forall2; exact HC.
Qed.

Theorem gaussian_row_pair_continuous n m i
    (a : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat) :
  (i <= m)%coq_nat ->
  {for a, continuous (fun q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat =>
    gaussian_row_pair n i (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q))}.
Proof.
  intros Hi P HP.
  move: HP => /nbhs_ballP [e e0 He].
  have He' : 0 < e by apply/RltP.
  have HK : 0 < INR (S n + S (goe_vector_index n))%coq_nat by apply lt_0_INR; lia.
  set eps := mkposreal _ (Rdiv_lt_0_compat _ _ He' HK).
  suff : nbhs a (fun q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat =>
    P (gaussian_row_pair n i (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q)))
    by [].
  apply/nbhs_ballP; exists (pos eps); [apply/RltP; exact (cond_pos eps)|].
  intros b Hb; apply He.
  have HB := gaussian_row_pair_ball n m i eps
    (coordinates_to_list _ a) (coordinates_to_list _ b) Hi
    (coordinates_to_list_length _ a) (coordinates_to_list_length _ b)
    (proj1 (coordinates_close_forall2 _ _ b a) Hb).
  replace e with (Rmult (INR (S n + S (goe_vector_index n))%coq_nat) eps).
  - exact HB.
  - change (Rmult (INR (S n + S (goe_vector_index n))%coq_nat)
      (e / INR (S n + S (goe_vector_index n))%coq_nat) = e).
    field; lra.
Qed.

Theorem gaussian_row_pair_norm_weight n m i xs :
  (i <= m)%coq_nat -> length xs = (S m * (S n + S (goe_vector_index n)))%coq_nat ->
  1 + (`|gaussian_row_pair n i xs|)%R <= gaussian_coordinate_product_weight 1 xs.
Proof.
  intros Hi HL; unfold gaussian_row_pair.
  eapply Rle_trans; [apply joint_of_list_norm_product_weight|apply row_chunk_product_weight].
  apply (row_chunk_length (S m)); [exact HL|lia].
Qed.

Theorem gaussian_row_pair_squared_weight n m i xs :
  (i <= m)%coq_nat -> length xs = (S m * (S n + S (goe_vector_index n)))%coq_nat ->
  (1 + (`|gaussian_row_pair n i xs|)%R)^2 <= gaussian_coordinate_product_weight 2 xs.
Proof.
  intros Hi HL.
  pose proof (gaussian_row_pair_norm_weight n m i xs Hi HL) as H.
  assert (HN : 0 <= (`|gaussian_row_pair n i xs|)%R) by (apply/RleP; apply normr_ge0).
  assert (HN1 : 0 <= 1 + (`|gaussian_row_pair n i xs|)%R) by lra.
  pose proof (pow_incr (1 + (`|gaussian_row_pair n i xs|)%R)
    (gaussian_coordinate_product_weight 1 xs) 2 (conj HN1 H)) as HP.
  rewrite -vector_growth_product_weight_power in HP; exact HP.
Qed.

Theorem gaussian_row_matrix_continuous n m t i
    (a : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat) :
  (i <= m)%coq_nat ->
  {for a, continuous (fun q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat =>
    gaussian_row_matrix n t i
      (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q))}.
Proof.
  intro Hi; unfold gaussian_row_matrix.
  apply (@continuous_comp
    (coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat)
    (euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n)))
    (matrix_NormedModule n)
    (fun q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat =>
      gaussian_row_pair n i (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q))
    (fun xz => joint_matrix n (matrix_zero n) t (fst xz) (snd xz)) a).
  - apply gaussian_row_pair_continuous; exact Hi.
  - apply joint_matrix_continuous.
Qed.

Theorem gaussian_row_array_continuous n m t
    (a : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat) :
  {for a, continuous (fun q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat =>
    gaussian_row_array n m t
      (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q))}.
Proof.
  unfold gaussian_row_array.
  apply (@tuple_build_continuous
    (coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat)
    (matrix_NormedModule n) m
    (fun i (q : coordinates_uniform_space (S m * (S n + S (goe_vector_index n)))%coq_nat) =>
      gaussian_row_matrix n t i
        (coordinates_to_list (S m * (S n + S (goe_vector_index n)))%coq_nat q)) a).
  intros i Hi; apply gaussian_row_matrix_continuous; exact Hi.
Qed.

