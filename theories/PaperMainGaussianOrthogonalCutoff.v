(* A bounded smooth majorant of the indicator of [u, oo) and its
   composition with the weighted centered Gaussian square. For e > 0,
   t >= 0 and u, let
     E(y) = exp (t (y - u)),   S(y) = e E(y) / (1 + e E(y)),
     psi(y) = (1 + e)/e S(y) = (1 + e) E(y) / (1 + e E(y)).
   S is a logistic function with S' = t S (1 - S), so
     psi' = (1 + e)/e t S (1 - S),   psi'' = (1 + e)/e t^2 S (1 - S) (1 - 2 S),
   and |psi|, |psi'|, |psi''| are at most (1 + e)/e, (1 + e)/e t and
   (1 + e)/e t^2. Also psi >= 0, psi(y) >= 1 for y >= u, and
   psi(y) <= (1 + e) E(y). For the weighted square
   Q d a xs = sum_(i < d) a_i (x_i^2 - 1) with |a_i| <= L, the composition
   psi(Q) is a C2 test: its coordinate derivatives are psi'(Q) 2 a_i x_i and
   psi''(Q) (2 a_j x_j) (2 a_i x_i) + psi'(Q) 2 a_i [i = j], all continuous,
   with the polynomial bound C prod_k (1 + |x_k|)^2,
   C = (1 + e)/e (1 + 2 t L)^2. So psi(Q) satisfies
   paper_main_gaussian_smooth_test d _ _ _ C 2. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCoordinateDerivativeDefinitions GaussianCoordinatePermutationDefinitions
  GaussianCoordinatePermutations GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianFiniteSums
  GaussianCovarianceSums GaussianCovarianceLinear
  PaperMainGordonContinuity PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainGaussianWeightedSquare
  PaperMainGaussianWeightedSquareLaw.
Import ListNotations.
Open Scope R_scope.

(* Real helpers. *)

Lemma paper_main_gaussian_orthogonal_derive_value (f : R -> R) (x l l' : R) :
  l = l' -> @is_derive R R^o R^o x 1 f l -> @is_derive R R^o R^o x 1 f l'.
Proof. intros <-; exact id. Qed.

Lemma paper_main_gaussian_orthogonal_div_le a b c :
  0 < b -> a <= c * b -> a / b <= c.
Proof.
intros Hb H.
replace c with (c * b / b) by (field; lra).
unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hb|exact H].
Qed.

Lemma paper_main_gaussian_orthogonal_div_ge a b c :
  0 < b -> c * b <= a -> c <= a / b.
Proof.
intros Hb H.
replace c with (c * b / b) by (field; lra).
unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact Hb|exact H].
Qed.

Lemma paper_main_gaussian_orthogonal_exp_ge1 x : 0 <= x -> 1 <= exp x.
Proof.
intros Hx; destruct (Rle_lt_or_eq_dec 0 x Hx) as [Hlt|<-].
- rewrite <- exp_0; left; apply exp_increasing; exact Hlt.
- rewrite exp_0; lra.
Qed.

(* The scalar majorant. *)

Definition paper_main_gaussian_orthogonal_logistic t u e (y : R) : R :=
  e * exp (t * (y - u)) / (1 + e * exp (t * (y - u))).

Definition paper_main_gaussian_orthogonal_cutoff t u e (y : R) : R :=
  (1 + e) / e * paper_main_gaussian_orthogonal_logistic t u e y.

Definition paper_main_gaussian_orthogonal_cutoff1 t u e (y : R) : R :=
  (1 + e) / e * (t * (paper_main_gaussian_orthogonal_logistic t u e y *
    (1 - paper_main_gaussian_orthogonal_logistic t u e y))).

Definition paper_main_gaussian_orthogonal_cutoff2 t u e (y : R) : R :=
  (1 + e) / e * (t * (t * (paper_main_gaussian_orthogonal_logistic t u e y *
    (1 - paper_main_gaussian_orthogonal_logistic t u e y) *
    (1 - 2 * paper_main_gaussian_orthogonal_logistic t u e y)))).

Lemma paper_main_gaussian_orthogonal_logistic_bounds t u e y :
  0 < e -> 0 < paper_main_gaussian_orthogonal_logistic t u e y < 1.
Proof.
intros He; unfold paper_main_gaussian_orthogonal_logistic.
pose proof (exp_pos (t * (y - u))) as HE.
assert (Hp : 0 < e * exp (t * (y - u))) by (apply Rmult_lt_0_compat; lra).
split.
- apply Rdiv_lt_0_compat; lra.
- assert (H := paper_main_gaussian_orthogonal_div_le (e * exp (t * (y - u)))
    (1 + e * exp (t * (y - u))) (e * exp (t * (y - u)) / (1 + e * exp (t * (y - u))))
    ltac:(lra)).
  apply (Rmult_lt_reg_r (1 + e * exp (t * (y - u)))); [lra|].
  replace (e * exp (t * (y - u)) / (1 + e * exp (t * (y - u))) *
    (1 + e * exp (t * (y - u)))) with (e * exp (t * (y - u))) by (field; lra).
  lra.
Qed.

Lemma paper_main_gaussian_orthogonal_logistic_derive t u e y :
  0 < e ->
  @is_derive R R^o R^o y 1 (paper_main_gaussian_orthogonal_logistic t u e)
    (t * (paper_main_gaussian_orthogonal_logistic t u e y *
      (1 - paper_main_gaussian_orthogonal_logistic t u e y))).
Proof.
intros He.
pose proof (exp_pos (t * (y - u))) as HE.
assert (Hpos : 0 < 1 + e * exp (t * (y - u))) by nra.
assert (HD : @is_derive R R^o R^o y 1 (fun z => exp (t * (z - u)))
    (exp (t * (y - u)) * (t * (1 - 0)))).
{ apply (is_derive_exp_comp (fun z => t * (z - u)) y (t * (1 - 0))).
  apply (is_derive_scal t (fun z => z - u) y (1 - 0)).
  apply (is_derive_minus (fun z => z) (fun _ => u) y 1 0);
    [apply is_derive_id_R|apply is_derive_const]. }
pose proof (is_derive_scal e _ y _ HD) as Hf.
pose proof (is_derive_plus (fun _ => 1) _ y 0 _ (is_derive_const 1 y) Hf) as Hg.
pose proof (is_derive_div _ _ y _ _ Hf Hg ltac:(cbv beta; lra)) as H.
eapply paper_main_gaussian_orthogonal_derive_value; [|exact H].
cbv beta; unfold paper_main_gaussian_orthogonal_logistic; field; lra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_derive t u e y :
  0 < e ->
  @is_derive R R^o R^o y 1 (paper_main_gaussian_orthogonal_cutoff t u e)
    (paper_main_gaussian_orthogonal_cutoff1 t u e y).
Proof.
intros He.
exact (is_derive_scal ((1 + e) / e) _ y _
  (paper_main_gaussian_orthogonal_logistic_derive t u e y He)).
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff1_derive t u e y :
  0 < e ->
  @is_derive R R^o R^o y 1 (paper_main_gaussian_orthogonal_cutoff1 t u e)
    (paper_main_gaussian_orthogonal_cutoff2 t u e y).
Proof.
intros He.
pose proof (paper_main_gaussian_orthogonal_logistic_derive t u e y He) as HS.
pose proof (is_derive_minus (fun _ => 1) _ y 0 _ (is_derive_const 1 y) HS) as H1.
pose proof (is_derive_mult _ _ y _ _ HS H1) as H2.
pose proof (is_derive_scal ((1 + e) / e) _ y _ (is_derive_scal t _ y _ H2)) as H3.
eapply paper_main_gaussian_orthogonal_derive_value; [|exact H3].
unfold paper_main_gaussian_orthogonal_cutoff2; cbv beta; ring.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_continuous t u e y :
  0 < e -> {for y, continuous (paper_main_gaussian_orthogonal_cutoff t u e)}.
Proof.
intros He; exact (is_derive_continuous _ _ _
  (paper_main_gaussian_orthogonal_cutoff_derive t u e y He)).
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff1_continuous t u e y :
  0 < e -> {for y, continuous (paper_main_gaussian_orthogonal_cutoff1 t u e)}.
Proof.
intros He; exact (is_derive_continuous _ _ _
  (paper_main_gaussian_orthogonal_cutoff1_derive t u e y He)).
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff2_continuous t u e y :
  0 < e -> {for y, continuous (paper_main_gaussian_orthogonal_cutoff2 t u e)}.
Proof.
intros He.
pose proof (paper_main_gaussian_orthogonal_logistic_derive t u e y He) as HS.
pose proof (is_derive_minus (fun _ => 1) _ y 0 _ (is_derive_const 1 y) HS) as H1.
pose proof (is_derive_mult _ _ y _ _ HS H1) as H2.
pose proof (is_derive_minus (fun _ => 1) _ y 0 _ (is_derive_const 1 y)
  (is_derive_scal 2 _ y _ HS)) as H4.
pose proof (is_derive_mult _ _ y _ _ H2 H4) as H5.
pose proof (is_derive_scal ((1 + e) / e) _ y _
  (is_derive_scal t _ y _ (is_derive_scal t _ y _ H5))) as H6.
exact (is_derive_continuous _ _ _ H6).
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_nonneg t u e y :
  0 < e -> 0 <= paper_main_gaussian_orthogonal_cutoff t u e y.
Proof.
intros He; unfold paper_main_gaussian_orthogonal_cutoff.
pose proof (paper_main_gaussian_orthogonal_logistic_bounds t u e y He) as HS.
assert (Hc : 0 < (1 + e) / e) by (apply Rdiv_lt_0_compat; lra).
nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_bound t u e y :
  0 < e -> Rabs (paper_main_gaussian_orthogonal_cutoff t u e y) <= (1 + e) / e.
Proof.
intros He.
rewrite (Rabs_pos_eq _ (paper_main_gaussian_orthogonal_cutoff_nonneg t u e y He)).
unfold paper_main_gaussian_orthogonal_cutoff.
pose proof (paper_main_gaussian_orthogonal_logistic_bounds t u e y He) as HS.
assert (Hc : 0 < (1 + e) / e) by (apply Rdiv_lt_0_compat; lra).
nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff1_bound t u e y :
  0 < e -> 0 <= t ->
  Rabs (paper_main_gaussian_orthogonal_cutoff1 t u e y) <= (1 + e) / e * t.
Proof.
intros He Ht; unfold paper_main_gaussian_orthogonal_cutoff1.
pose proof (paper_main_gaussian_orthogonal_logistic_bounds t u e y He) as HS.
set (S := paper_main_gaussian_orthogonal_logistic t u e y) in *; clearbody S.
assert (Hc : 0 < (1 + e) / e) by (apply Rdiv_lt_0_compat; lra).
assert (H0 : 0 <= (1 + e) / e * (t * (S * (1 - S)))).
{ apply Rmult_le_pos; [lra|apply Rmult_le_pos; [lra|nra]]. }
rewrite (Rabs_pos_eq _ H0).
apply Rmult_le_compat_l; [lra|].
assert (HSS : S * (1 - S) <= 1) by nra.
nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff2_bound t u e y :
  0 < e ->
  Rabs (paper_main_gaussian_orthogonal_cutoff2 t u e y) <= (1 + e) / e * t ^ 2.
Proof.
intros He; unfold paper_main_gaussian_orthogonal_cutoff2.
pose proof (paper_main_gaussian_orthogonal_logistic_bounds t u e y He) as HS.
set (S := paper_main_gaussian_orthogonal_logistic t u e y) in *; clearbody S.
assert (Hc : 0 < (1 + e) / e) by (apply Rdiv_lt_0_compat; lra).
assert (HX : Rabs (S * (1 - S) * (1 - 2 * S)) <= 1).
{ rewrite !Rabs_mult (Rabs_pos_eq S ltac:(lra)) (Rabs_pos_eq (1 - S) ltac:(lra)).
  assert (H2 : Rabs (1 - 2 * S) <= 1) by (apply Rabs_le; lra).
  assert (H3 : 0 <= Rabs (1 - 2 * S)) by apply Rabs_pos.
  assert (H4 : S * (1 - S) <= 1) by nra.
  assert (H5 : 0 <= S * (1 - S)) by nra.
  nra. }
set (X := S * (1 - S) * (1 - 2 * S)) in *; clearbody X.
set (c := (1 + e) / e) in *; clearbody c.
rewrite !Rabs_mult (Rabs_pos_eq c ltac:(lra)).
apply Rmult_le_compat_l; [lra|].
assert (Ht2 : Rabs t * Rabs t = t ^ 2).
{ destruct (Rle_or_lt 0 t) as [Hp|Hn];
    [rewrite (Rabs_pos_eq t Hp)|rewrite (Rabs_left t Hn)]; ring. }
rewrite -Ht2.
assert (Ht0 : 0 <= Rabs t) by apply Rabs_pos.
assert (HX0 : 0 <= Rabs X) by apply Rabs_pos.
nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_value t u e y :
  0 < e ->
  paper_main_gaussian_orthogonal_cutoff t u e y =
  (1 + e) * exp (t * (y - u)) / (1 + e * exp (t * (y - u))).
Proof.
intros He; unfold paper_main_gaussian_orthogonal_cutoff,
  paper_main_gaussian_orthogonal_logistic.
pose proof (exp_pos (t * (y - u))) as HE.
field; split; nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_ge1 t u e y :
  0 < e -> 0 <= t -> u <= y -> 1 <= paper_main_gaussian_orthogonal_cutoff t u e y.
Proof.
intros He Ht Hy.
rewrite (paper_main_gaussian_orthogonal_cutoff_value t u e y He).
assert (HE : 1 <= exp (t * (y - u))).
{ apply paper_main_gaussian_orthogonal_exp_ge1; apply Rmult_le_pos; lra. }
apply paper_main_gaussian_orthogonal_div_ge; nra.
Qed.

Lemma paper_main_gaussian_orthogonal_cutoff_exp_bound t u e y :
  0 < e ->
  paper_main_gaussian_orthogonal_cutoff t u e y <= (1 + e) * exp (t * (y - u)).
Proof.
intros He.
rewrite (paper_main_gaussian_orthogonal_cutoff_value t u e y He).
pose proof (exp_pos (t * (y - u))) as HE.
apply paper_main_gaussian_orthogonal_div_le; nra.
Qed.

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

(* The composite test and its derivatives. *)

Definition paper_main_gaussian_orthogonal_test d (a : nat -> R) t u e (xs : list R) : R :=
  paper_main_gaussian_orthogonal_cutoff t u e (paper_main_weighted_square d a xs).

Definition paper_main_gaussian_orthogonal_test1 d (a : nat -> R) t u e i
    (xs : list R) : R :=
  paper_main_gaussian_orthogonal_cutoff1 t u e (paper_main_weighted_square d a xs) *
  paper_main_gaussian_orthogonal_square_first a i xs.

Definition paper_main_gaussian_orthogonal_test2 d (a : nat -> R) t u e i j
    (xs : list R) : R :=
  paper_main_gaussian_orthogonal_cutoff2 t u e (paper_main_weighted_square d a xs) *
    paper_main_gaussian_orthogonal_square_first a j xs *
    paper_main_gaussian_orthogonal_square_first a i xs +
  paper_main_gaussian_orthogonal_cutoff1 t u e (paper_main_weighted_square d a xs) *
    paper_main_gaussian_orthogonal_square_second a i j xs.

Lemma paper_main_gaussian_orthogonal_test_derivative d (a : nat -> R) t u e i :
  0 < e -> (i < d)%coq_nat ->
  finite_coordinate_derivative d i (paper_main_gaussian_orthogonal_test d a t u e)
    (paper_main_gaussian_orthogonal_test1 d a t u e i).
Proof.
intros He Hi.
exact (paper_main_gaussian_orthogonal_coordinate_comp d i
  (paper_main_gaussian_orthogonal_cutoff t u e)
  (paper_main_gaussian_orthogonal_cutoff1 t u e) _ _
  (fun y => paper_main_gaussian_orthogonal_cutoff_derive t u e y He)
  (paper_main_gaussian_orthogonal_square_derivative d a i Hi)).
Qed.

Lemma paper_main_gaussian_orthogonal_test1_derivative d (a : nat -> R) t u e i j :
  0 < e -> (j < d)%coq_nat ->
  finite_coordinate_derivative d j (paper_main_gaussian_orthogonal_test1 d a t u e i)
    (paper_main_gaussian_orthogonal_test2 d a t u e i j).
Proof.
intros He Hj.
exact (paper_main_coordinate_derivative_mult d j _ _ _ _
  (paper_main_gaussian_orthogonal_coordinate_comp d j
    (paper_main_gaussian_orthogonal_cutoff1 t u e)
    (paper_main_gaussian_orthogonal_cutoff2 t u e) _ _
    (fun y => paper_main_gaussian_orthogonal_cutoff1_derive t u e y He)
    (paper_main_gaussian_orthogonal_square_derivative d a j Hj))
  (paper_main_gaussian_orthogonal_square_second_derivative d a i j Hj)).
Qed.

Lemma paper_main_gaussian_orthogonal_test_continuous d (a : nat -> R) t u e :
  0 < e -> finite_joint_continuous d (paper_main_gaussian_orthogonal_test d a t u e).
Proof.
intros He.
apply (paper_main_gordon_joint_comp d (paper_main_weighted_square d a)
  (paper_main_gaussian_orthogonal_cutoff t u e)).
- exact (paper_main_weighted_square_continuous d a).
- intros xs _; exact (paper_main_gaussian_orthogonal_cutoff_continuous t u e _ He).
Qed.

Lemma paper_main_gaussian_orthogonal_test1_continuous d (a : nat -> R) t u e i :
  0 < e -> (i < d)%coq_nat ->
  finite_joint_continuous d (paper_main_gaussian_orthogonal_test1 d a t u e i).
Proof.
intros He Hi; unfold paper_main_gaussian_orthogonal_test1.
apply finite_joint_continuous_mult.
- apply (paper_main_gordon_joint_comp d (paper_main_weighted_square d a)
    (paper_main_gaussian_orthogonal_cutoff1 t u e)).
  + exact (paper_main_weighted_square_continuous d a).
  + intros xs _; exact (paper_main_gaussian_orthogonal_cutoff1_continuous t u e _ He).
- exact (paper_main_gaussian_orthogonal_square_first_continuous d a i Hi).
Qed.

Lemma paper_main_gaussian_orthogonal_test2_continuous d (a : nat -> R) t u e i j :
  0 < e -> (i < d)%coq_nat -> (j < d)%coq_nat ->
  finite_joint_continuous d (paper_main_gaussian_orthogonal_test2 d a t u e i j).
Proof.
intros He Hi Hj; unfold paper_main_gaussian_orthogonal_test2.
apply finite_joint_continuous_add; apply finite_joint_continuous_mult.
- apply finite_joint_continuous_mult.
  + apply (paper_main_gordon_joint_comp d (paper_main_weighted_square d a)
      (paper_main_gaussian_orthogonal_cutoff2 t u e)).
    * exact (paper_main_weighted_square_continuous d a).
    * intros xs _; exact (paper_main_gaussian_orthogonal_cutoff2_continuous t u e _ He).
  + exact (paper_main_gaussian_orthogonal_square_first_continuous d a j Hj).
- exact (paper_main_gaussian_orthogonal_square_first_continuous d a i Hi).
- apply (paper_main_gordon_joint_comp d (paper_main_weighted_square d a)
    (paper_main_gaussian_orthogonal_cutoff1 t u e)).
  + exact (paper_main_weighted_square_continuous d a).
  + intros xs _; exact (paper_main_gaussian_orthogonal_cutoff1_continuous t u e _ He).
- exact (paper_main_gaussian_orthogonal_square_second_continuous d a i j).
Qed.

(* Polynomial bounds with weight prod_k (1 + |x_k|)^2. *)

Lemma paper_main_gaussian_orthogonal_weight_facts xs :
  1 <= gaussian_coordinate_product_weight 1 xs /\
  gaussian_coordinate_product_weight 2 xs =
    gaussian_coordinate_product_weight 1 xs * gaussian_coordinate_product_weight 1 xs.
Proof.
split; [apply gaussian_coordinate_product_weight_at_least_one|].
rewrite <- (product_weight_one_pow 2 xs); simpl; ring.
Qed.

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

Theorem paper_main_gaussian_orthogonal_test_smooth d (a : nat -> R) L t u e :
  0 < e -> 0 <= t -> 0 <= L -> (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) ->
  paper_main_gaussian_smooth_test d (paper_main_gaussian_orthogonal_test d a t u e)
    (paper_main_gaussian_orthogonal_test1 d a t u e)
    (paper_main_gaussian_orthogonal_test2 d a t u e)
    ((1 + e) / e * (1 + 2 * t * L) ^ 2) 2.
Proof.
intros He Ht HL Ha.
assert (Hc : 0 < (1 + e) / e) by (apply Rdiv_lt_0_compat; lra).
assert (HC : 0 <= (1 + e) / e * (1 + 2 * t * L) ^ 2).
{ apply Rmult_le_pos; [lra|apply pow2_ge_0]. }
assert (HtL : 0 <= t * L) by (apply Rmult_le_pos; lra).
split.
- exact (paper_main_gaussian_orthogonal_test_continuous d a t u e He).
- intros i Hi; exact (paper_main_gaussian_orthogonal_test_derivative d a t u e i He Hi).
- intros i Hi; exact (paper_main_gaussian_orthogonal_test1_continuous d a t u e i He Hi).
- intros i j Hi Hj; exact (paper_main_gaussian_orthogonal_test1_derivative d a t u e i j He Hj).
- intros i j Hi Hj; exact (paper_main_gaussian_orthogonal_test2_continuous d a t u e i j He Hi Hj).
- split; [exact HC|]; intros xs Hxs.
  destruct (paper_main_gaussian_orthogonal_weight_facts xs) as [HW1 HW2]; rewrite HW2.
  unfold paper_main_gaussian_orthogonal_test.
  pose proof (paper_main_gaussian_orthogonal_cutoff_bound t u e
    (paper_main_weighted_square d a xs) He) as Hb.
  set (W := gaussian_coordinate_product_weight 1 xs) in *.
  assert (H1 : 1 <= (1 + 2 * t * L) ^ 2) by nra.
  assert (HWW : 1 <= W * W) by nra.
  nra.
- intros i Hi; split; [exact HC|]; intros xs Hxs.
  destruct (paper_main_gaussian_orthogonal_weight_facts xs) as [HW1 HW2]; rewrite HW2.
  unfold paper_main_gaussian_orthogonal_test1; rewrite Rabs_mult.
  pose proof (paper_main_gaussian_orthogonal_cutoff1_bound t u e
    (paper_main_weighted_square d a xs) He Ht) as Hb.
  pose proof (paper_main_gaussian_orthogonal_square_first_bound a L i xs (Ha i Hi)
    ltac:(lia)) as Hq.
  set (W := gaussian_coordinate_product_weight 1 xs) in *.
  set (P := Rabs (paper_main_gaussian_orthogonal_cutoff1 t u e
    (paper_main_weighted_square d a xs))) in *.
  set (D := Rabs (paper_main_gaussian_orthogonal_square_first a i xs)) in *.
  assert (HP : 0 <= P) by apply Rabs_pos.
  assert (HD : 0 <= D) by apply Rabs_pos.
  assert (Hstep : P * D <= (1 + e) / e * t * (2 * L * W)).
  { apply Rmult_le_compat; assumption. }
  assert (Hfin : (1 + e) / e * t * (2 * L * W) <=
      (1 + e) / e * (1 + 2 * t * L) ^ 2 * (W * W)).
  { replace ((1 + e) / e * t * (2 * L * W)) with ((1 + e) / e * (2 * (t * L) * W)) by ring.
    replace ((1 + e) / e * (1 + 2 * t * L) ^ 2 * (W * W)) with
      ((1 + e) / e * ((1 + 2 * t * L) ^ 2 * (W * W))) by ring.
    apply Rmult_le_compat_l; [lra|].
    assert (HWW : W <= W * W) by nra.
    nra. }
  lra.
- intros i j Hi Hj; split; [exact HC|]; intros xs Hxs.
  destruct (paper_main_gaussian_orthogonal_weight_facts xs) as [HW1 HW2]; rewrite HW2.
  unfold paper_main_gaussian_orthogonal_test2.
  pose proof (paper_main_gaussian_orthogonal_cutoff2_bound t u e
    (paper_main_weighted_square d a xs) He) as Hb2.
  pose proof (paper_main_gaussian_orthogonal_cutoff1_bound t u e
    (paper_main_weighted_square d a xs) He Ht) as Hb1.
  pose proof (paper_main_gaussian_orthogonal_square_first_bound a L i xs (Ha i Hi)
    ltac:(lia)) as Hqi.
  pose proof (paper_main_gaussian_orthogonal_square_first_bound a L j xs (Ha j Hj)
    ltac:(lia)) as Hqj.
  pose proof (paper_main_gaussian_orthogonal_square_second_bound a L i j xs (Ha i Hi) HL)
    as Hs.
  set (W := gaussian_coordinate_product_weight 1 xs) in *; clearbody W.
  set (A2 := paper_main_gaussian_orthogonal_cutoff2 t u e
    (paper_main_weighted_square d a xs)) in *; clearbody A2.
  set (A1 := paper_main_gaussian_orthogonal_cutoff1 t u e
    (paper_main_weighted_square d a xs)) in *; clearbody A1.
  set (Bi := paper_main_gaussian_orthogonal_square_first a i xs) in *; clearbody Bi.
  set (Bj := paper_main_gaussian_orthogonal_square_first a j xs) in *; clearbody Bj.
  set (B2 := paper_main_gaussian_orthogonal_square_second a i j xs) in *; clearbody B2.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite !Rabs_mult.
  pose proof (Rabs_pos A2) as HP2; pose proof (Rabs_pos A1) as HP1.
  pose proof (Rabs_pos Bi) as HDi; pose proof (Rabs_pos Bj) as HDj.
  pose proof (Rabs_pos B2) as HD2.
  assert (HA : Rabs A2 * Rabs Bj * Rabs Bi <=
      (1 + e) / e * t ^ 2 * (2 * L * W) * (2 * L * W)).
  { apply Rmult_le_compat; [nra|exact HDi| |exact Hqi].
    apply Rmult_le_compat; assumption. }
  assert (HB : Rabs A1 * Rabs B2 <= (1 + e) / e * t * (2 * L)).
  { apply Rmult_le_compat; assumption. }
  assert (HFin : (1 + e) / e * t ^ 2 * (2 * L * W) * (2 * L * W) +
      (1 + e) / e * t * (2 * L) <= (1 + e) / e * (1 + 2 * t * L) ^ 2 * (W * W)).
  { replace ((1 + e) / e * t ^ 2 * (2 * L * W) * (2 * L * W) +
      (1 + e) / e * t * (2 * L)) with
      ((1 + e) / e * (4 * (t * L) ^ 2 * (W * W) + 2 * (t * L))) by ring.
    replace ((1 + e) / e * (1 + 2 * t * L) ^ 2 * (W * W)) with
      ((1 + e) / e * ((1 + 2 * t * L) ^ 2 * (W * W))) by ring.
    apply Rmult_le_compat_l; [lra|].
    assert (HWW : 1 <= W * W) by nra.
    nra. }
  lra.
Qed.

(* The majorant properties of the composite test. *)

Lemma paper_main_gaussian_orthogonal_test_nonneg d (a : nat -> R) t u e xs :
  0 < e -> 0 <= paper_main_gaussian_orthogonal_test d a t u e xs.
Proof.
intros He; exact (paper_main_gaussian_orthogonal_cutoff_nonneg t u e _ He).
Qed.

Lemma paper_main_gaussian_orthogonal_test_ge1 d (a : nat -> R) t u e xs :
  0 < e -> 0 <= t -> u <= paper_main_weighted_square d a xs ->
  1 <= paper_main_gaussian_orthogonal_test d a t u e xs.
Proof.
intros He Ht Hu; exact (paper_main_gaussian_orthogonal_cutoff_ge1 t u e _ He Ht Hu).
Qed.

Lemma paper_main_gaussian_orthogonal_test_exp_bound d (a : nat -> R) t u e xs :
  0 < e ->
  paper_main_gaussian_orthogonal_test d a t u e xs <=
    (1 + e) * exp (- (t * u)) * exp (t * paper_main_weighted_square d a xs).
Proof.
intros He.
pose proof (paper_main_gaussian_orthogonal_cutoff_exp_bound t u e
  (paper_main_weighted_square d a xs) He) as H.
unfold paper_main_gaussian_orthogonal_test.
replace ((1 + e) * exp (- (t * u)) * exp (t * paper_main_weighted_square d a xs)) with
  ((1 + e) * exp (t * (paper_main_weighted_square d a xs - u))); [exact H|].
rewrite Rmult_assoc -exp_plus; f_equal; f_equal; ring.
Qed.
