(* Coordinate derivatives of the weighted centered Gaussian square
   Q d a xs = sum_(i < d) a_i (x_i^2 - 1): its first derivatives are
   2 a_i x_i (paper_main_gaussian_orthogonal_square_first,
   paper_main_gaussian_orthogonal_square_derivative) and its second
   derivatives 2 a_i [i = j] (paper_main_gaussian_orthogonal_square_second,
   paper_main_gaussian_orthogonal_square_second_derivative). They are
   continuous, and for |a_i| <= L they are bounded by the polynomial weight
   prod_k (1 + |x_k|) up to a constant
   (paper_main_gaussian_orthogonal_square_first_bound and
   paper_main_gaussian_orthogonal_square_second_bound). The chain rule
   paper_main_gaussian_orthogonal_coordinate_comp differentiates phi (F xs)
   along one coordinate. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.WeightDefinitions Gaussian.Coordinate.Weights
  Gaussian.Coordinate.DerivativeDefinitions
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Analysis.CoordinateTopology Gaussian.Coordinate.PolynomialContinuity
  Gaussian.Iterated.FiniteSums Analysis.FiniteSumAlgebra
  Gaussian.Covariance.LinearImages Gordon.Continuity Gaussian.Smooth.Calculus
  Gaussian.Orthogonal.WeightedSquare.
Import ListNotations.
Open Scope R_scope.

(* Real helpers. *)

Lemma paper_main_gaussian_orthogonal_derive_value (f : R -> R) (x l l' : R) :
  l = l' -> @is_derive R R^o R^o x 1 f l -> @is_derive R R^o R^o x 1 f l'.
Proof. intros <-; exact id. Qed.

(* The coordinate chain rule. *)

Lemma paper_main_gaussian_orthogonal_coordinate_comp d a (phi phi1 : R -> R) F DF :
  (forall y, @is_derive R R^o R^o y 1 phi (phi1 y)) ->
  finite_coordinate_derivative d a F DF ->
  finite_coordinate_derivative d a (fun xs => phi (F xs)) (fun xs => phi1 (F xs) * DF xs).
Proof.
intros Hphi HF xs Hxs.
assert (H0 : @is_derive R R^o R^o
    ((fun s => F (replace_coordinate a s xs)) (List.nth a xs 0)) 1 phi (phi1 (F xs))).
{ cbv beta; rewrite replace_coordinate_self; exact (Hphi (F xs)). }
pose proof (is_derive_comp phi (fun s => F (replace_coordinate a s xs))
  (List.nth a xs 0) (phi1 (F xs)) (DF xs) H0 (HF xs Hxs)) as H.
eapply paper_main_gaussian_orthogonal_derive_value; [|exact H].
ring.
Qed.

(* Coordinate derivatives of the weighted square. *)

Definition paper_main_gaussian_orthogonal_square_first (a : nat -> R) i (xs : list R) : R :=
  2 * a i * List.nth i xs 0.

Definition paper_main_gaussian_orthogonal_square_second (a : nat -> R) i j
    (xs : list R) : R :=
  if Nat.eqb i j then 2 * a i else 0.

Lemma paper_main_gaussian_orthogonal_square_replace d (a : nat -> R) k s xs :
  List.length xs = d -> (k < d)%coq_nat ->
  paper_main_weighted_square d a (replace_coordinate k s xs) =
  paper_main_weighted_square d a xs + a k * (s ^ 2 - List.nth k xs 0 ^ 2).
Proof.
intros Hxs Hk; unfold paper_main_weighted_square.
transitivity (finite_sum (fun i => a i * (List.nth i xs 0 ^ 2 - 1) +
  (if Nat.eqb i k then a k * (s ^ 2 - List.nth k xs 0 ^ 2) else 0)) (List.seq 0 d)).
- apply finite_sum_ext; intros i Hi.
  destruct (Nat.eqb_spec i k) as [->|Hik].
  + rewrite (replace_coordinate_nth_same k s xs ltac:(lia)); ring.
  + rewrite (replace_coordinate_nth_other k i s xs (fun H => Hik (esym H))); ring.
- rewrite finite_sum_plus (finite_sum_delta d k _ Hk); reflexivity.
Qed.

Lemma paper_main_gaussian_orthogonal_square_derivative d (a : nat -> R) k :
  (k < d)%coq_nat ->
  finite_coordinate_derivative d k (paper_main_weighted_square d a)
    (paper_main_gaussian_orthogonal_square_first a k).
Proof.
intros Hk xs Hxs.
apply (is_derive_ext (fun s => paper_main_weighted_square d a xs +
  a k * (s * s - List.nth k xs 0 ^ 2))).
- intros s; cbv beta.
  rewrite (paper_main_gaussian_orthogonal_square_replace d a k s xs Hxs Hk); ring.
- pose proof (is_derive_mult (fun s => s) (fun s => s) (List.nth k xs 0) 1 1
    (is_derive_id_R _) (is_derive_id_R _)) as H1.
  pose proof (is_derive_minus _ (fun _ => List.nth k xs 0 ^ 2) _ _ 0 H1
    (is_derive_const _ _)) as H2.
  pose proof (is_derive_plus (fun _ => paper_main_weighted_square d a xs) _ _ 0 _
    (is_derive_const _ _) (is_derive_scal (a k) _ _ _ H2)) as H3.
  eapply paper_main_gaussian_orthogonal_derive_value; [|exact H3].
  unfold paper_main_gaussian_orthogonal_square_first; cbv beta; ring.
Qed.

Lemma paper_main_gaussian_orthogonal_square_second_derivative d (a : nat -> R) i j :
  (j < d)%coq_nat ->
  finite_coordinate_derivative d j (paper_main_gaussian_orthogonal_square_first a i)
    (paper_main_gaussian_orthogonal_square_second a i j).
Proof.
intros Hj xs Hxs.
unfold paper_main_gaussian_orthogonal_square_first,
  paper_main_gaussian_orthogonal_square_second.
destruct (Nat.eqb_spec i j) as [->|Hij].
- apply (is_derive_ext (fun s => 2 * a j * s)).
  + intros s; cbv beta.
    rewrite (replace_coordinate_nth_same j s xs ltac:(lia)); reflexivity.
  + eapply paper_main_gaussian_orthogonal_derive_value;
      [|exact (is_derive_scal (2 * a j) (fun s => s) _ _ (is_derive_id_R _))].
    ring.
- apply (is_derive_ext (fun _ => 2 * a i * List.nth i xs 0)).
  + intros s; cbv beta.
    rewrite (replace_coordinate_nth_other j i s xs (fun H => Hij (esym H))); reflexivity.
  + apply is_derive_const.
Qed.

Lemma paper_main_gaussian_orthogonal_square_first_continuous d (a : nat -> R) i :
  (i < d)%coq_nat ->
  finite_joint_continuous d (paper_main_gaussian_orthogonal_square_first a i).
Proof.
intros Hi; unfold paper_main_gaussian_orthogonal_square_first.
apply finite_joint_continuous_scale, finite_joint_continuous_nth; exact Hi.
Qed.

Lemma paper_main_gaussian_orthogonal_square_second_continuous d (a : nat -> R) i j :
  finite_joint_continuous d (paper_main_gaussian_orthogonal_square_second a i j).
Proof.
unfold paper_main_gaussian_orthogonal_square_second.
apply finite_joint_continuous_constant.
Qed.

(* Bounds on the derivatives for |a_i| <= L. *)

Lemma paper_main_gaussian_orthogonal_square_first_bound (a : nat -> R) L i xs :
  Rabs (a i) <= L -> (i < List.length xs)%coq_nat ->
  Rabs (paper_main_gaussian_orthogonal_square_first a i xs) <=
    2 * L * gaussian_coordinate_product_weight 1 xs.
Proof.
intros Ha Hi; unfold paper_main_gaussian_orthogonal_square_first.
pose proof (coordinate_le_weight_one xs i Hi) as Hx.
pose proof (Rabs_pos (a i)) as Ha0.
pose proof (Rabs_pos (List.nth i xs 0)) as Hx0.
rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)).
nra.
Qed.

Lemma paper_main_gaussian_orthogonal_square_second_bound (a : nat -> R) L i j xs :
  Rabs (a i) <= L -> 0 <= L ->
  Rabs (paper_main_gaussian_orthogonal_square_second a i j xs) <= 2 * L.
Proof.
intros Ha HL; unfold paper_main_gaussian_orthogonal_square_second.
destruct (Nat.eqb i j).
- rewrite Rabs_mult (Rabs_pos_eq 2 ltac:(lra)); lra.
- rewrite Rabs_R0; lra.
Qed.
