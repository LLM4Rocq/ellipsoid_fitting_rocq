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

(* Regularity of the decoding of a list of coordinates into an array of
   matrices (RowArrayDefinitions). Row i of the list is read as a joint
   vector (x, z) (gaussian_row_pair) and turned into the matrix
   joint_matrix n (matrix_zero n) t x z. The decoding is continuous for the
   coordinate topology (gaussian_row_pair_continuous,
   gaussian_row_array_continuous), and 1 + `|gaussian_row_pair n i xs| is
   at most gaussian_coordinate_product_weight 1 xs
   (gaussian_row_pair_norm_weight). As the ball of joint vectors is that of
   the Euclidean norm, coordinates within e give joint vectors within
   INR (S n + S (goe_vector_index n)) * e (gaussian_row_pair_ball). *)

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

(* The radius is INR (S n + S (goe_vector_index n)) * e, because the ball on
   joint vectors is the ball of the Euclidean norm. It is written Rmult,
   Stdlib's product, because the radius argument of MathComp's ball is read
   in ring_scope. *)
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

