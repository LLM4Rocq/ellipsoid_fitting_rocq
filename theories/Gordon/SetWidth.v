(* Support and Gaussian width of a nonempty subset of the unit sphere.
   The support is a genuine least upper bound, not a finite surrogate. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.Iterated.Definitions Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.Tuples Gaussian.Coordinate.WeightDefinitions
  Gaussian.Iterated.PolynomialDomain Gaussian.Covariance.Definitions
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.Lipschitz
  Gaussian.Lipschitz.EuclideanNorm.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_set_support d (T : (nat -> R) -> Prop) xs :=
  epsilon (inhabits 0) (fun b => is_lub
    (fun a => exists u, T u /\ a = paper_main_gordon_dot d u (fun i => List.nth i xs 0)) b).

Definition paper_main_gordon_set_width d T :=
  gaussian_iterated_expectation d (paper_main_gordon_set_support d T).

Lemma paper_main_gordon_coefficient_dot_bound d u xs B :
  List.length xs = d -> 0 <= B -> paper_main_gordon_dot d u u <= B^2 ->
  Rabs (paper_main_gordon_dot d u (fun i => List.nth i xs 0)) <= B * paper_main_gaussian_norm xs.
Proof.
intros Hxs HB Hu.
pose proof (paper_main_gordon_sum_cauchy u (fun i => List.nth i xs 0) (List.seq 0 d)) as HC.
assert (HE : finite_sum (fun i => (u i)^2) (List.seq 0 d) = paper_main_gordon_dot d u u).
{ unfold paper_main_gordon_dot; apply finite_sum_ext; intros; ring. }
rewrite HE, (paper_main_gaussian_squares_coordinates d xs Hxs) in HC.
fold (paper_main_gordon_dot d u (fun i => List.nth i xs 0)) in HC.
pose proof (paper_main_gaussian_norm_squared xs) as HN.
pose proof (paper_main_gaussian_norm_nonnegative xs) as HNP.
pose proof (Rmult_le_compat_r ((paper_main_gaussian_norm xs)^2)
  (paper_main_gordon_dot d u u) (B^2) (pow2_ge_0 _) Hu) as Hmul.
pose proof (Rsqr_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as HA.
pose proof (Rabs_pos (paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as HAP.
assert (Hprod : 0 <= B * paper_main_gaussian_norm xs) by (apply Rmult_le_pos; assumption).
unfold Rsqr in HA; nra.
Qed.

Lemma paper_main_gordon_unit_dot_lipschitz d u xs ys :
  paper_main_gordon_dot d u u = 1 ->
  Rabs (paper_main_gordon_dot d u (fun i => List.nth i xs 0) -
    paper_main_gordon_dot d u (fun i => List.nth i ys 0)) <=
  paper_main_gordon_distance d xs ys.
Proof.
intro Hu.
pose proof (paper_main_gordon_row_lipschitz d (fun _ => u) 0 xs ys 1 ltac:(lra)
  ltac:(change (paper_main_gordon_dot d u u <= 1^2); rewrite Hu; lra)) as H.
rewrite Rmult_1_l in H; exact H.
Qed.

Lemma paper_main_gordon_set_support_lub d T xs :
  List.length xs = d -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  is_lub (fun a => exists u, T u /\ a = paper_main_gordon_dot d u (fun i => List.nth i xs 0))
    (paper_main_gordon_set_support d T xs).
Proof.
intros Hxs HT HU; unfold paper_main_gordon_set_support.
apply epsilon_spec.
assert (HB : bound (fun a => exists u, T u /\ a = paper_main_gordon_dot d u (fun i => List.nth i xs 0))).
{ exists (paper_main_gaussian_norm xs).
  intros a [u [Hu ->]].
  pose proof (paper_main_gaussian_unit_dot_bound d u xs Hxs (HU u Hu)) as H.
  pose proof (Rle_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0))); lra. }
assert (HN : exists a, exists u, T u /\ a = paper_main_gordon_dot d u (fun i => List.nth i xs 0)).
{ destruct HT as [u Hu].
  exists (paper_main_gordon_dot d u (fun i => List.nth i xs 0)); exists u; auto. }
destruct (completeness _ HB HN) as [b Hb]; exists b; exact Hb.
Qed.

Lemma paper_main_gordon_set_support_member d T xs u :
  List.length xs = d -> T u ->
  (forall v, T v -> paper_main_gordon_dot d v v = 1) ->
  paper_main_gordon_dot d u (fun i => List.nth i xs 0) <= paper_main_gordon_set_support d T xs.
Proof.
intros Hxs Hu HU.
apply (proj1 (paper_main_gordon_set_support_lub d T xs Hxs (ex_intro _ u Hu) HU)).
exists u; auto.
Qed.

Lemma paper_main_gordon_set_support_le d T xs b :
  List.length xs = d -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  (forall u, T u -> paper_main_gordon_dot d u (fun i => List.nth i xs 0) <= b) ->
  paper_main_gordon_set_support d T xs <= b.
Proof.
intros Hxs HT HU Hb.
apply (proj2 (paper_main_gordon_set_support_lub d T xs Hxs HT HU)).
intros a [u [Hu ->]]; apply Hb; exact Hu.
Qed.

Lemma paper_main_gordon_set_support_abs d T xs :
  List.length xs = d -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  Rabs (paper_main_gordon_set_support d T xs) <= paper_main_gaussian_norm xs.
Proof.
intros Hxs HT HU; apply Rabs_le; split.
- destruct HT as [u Hu].
  pose proof (paper_main_gordon_set_support_member d T xs u Hxs Hu HU) as H.
  pose proof (paper_main_gaussian_unit_dot_bound d u xs Hxs (HU u Hu)) as HB.
  pose proof (Rle_abs (- paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as Hneg.
  rewrite Rabs_Ropp in Hneg; lra.
- apply paper_main_gordon_set_support_le; try assumption.
  intros u Hu.
  pose proof (paper_main_gaussian_unit_dot_bound d u xs Hxs (HU u Hu)) as HB.
  pose proof (Rle_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0))); lra.
Qed.

Lemma paper_main_gordon_set_support_lipschitz d T xs ys :
  List.length xs = d -> List.length ys = d -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  Rabs (paper_main_gordon_set_support d T xs - paper_main_gordon_set_support d T ys) <=
  paper_main_gordon_distance d xs ys.
Proof.
intros Hxs Hys HT HU.
assert (Hxy : paper_main_gordon_set_support d T xs <=
  paper_main_gordon_set_support d T ys + paper_main_gordon_distance d xs ys).
{ apply paper_main_gordon_set_support_le; try assumption.
  intros u Hu.
  pose proof (paper_main_gordon_set_support_member d T ys u Hys Hu HU) as H.
  pose proof (paper_main_gordon_unit_dot_lipschitz d u xs ys (HU u Hu)) as HL.
  pose proof (Rle_abs (paper_main_gordon_dot d u (fun i => List.nth i xs 0) -
    paper_main_gordon_dot d u (fun i => List.nth i ys 0))); lra. }
assert (Hyx : paper_main_gordon_set_support d T ys <=
  paper_main_gordon_set_support d T xs + paper_main_gordon_distance d xs ys).
{ apply paper_main_gordon_set_support_le; try assumption.
  intros u Hu.
  pose proof (paper_main_gordon_set_support_member d T xs u Hxs Hu HU) as H.
  pose proof (paper_main_gordon_unit_dot_lipschitz d u xs ys (HU u Hu)) as HL.
  pose proof (Rle_abs (paper_main_gordon_dot d u (fun i => List.nth i ys 0) -
    paper_main_gordon_dot d u (fun i => List.nth i xs 0))) as Hneg.
  rewrite Rabs_minus_sym in Hneg; lra. }
apply Rabs_le; lra.
Qed.

Lemma paper_main_gordon_distance_coordinate_bound d xs ys delta :
  0 <= delta -> (forall i, (i < d)%nat -> Rabs (List.nth i xs 0 - List.nth i ys 0) <= delta) ->
  paper_main_gordon_distance d xs ys <= sqrt (INR d) * delta.
Proof.
intros Hd HB.
assert (HS : finite_sum (fun i => (List.nth i xs 0 - List.nth i ys 0)^2) (List.seq 0 d) <=
  INR d * delta^2).
{ rewrite <- (length_seq d 0), <- finite_sum_const.
rewrite length_seq.
  apply finite_sum_le; intros i Hi.
  pose proof (HB i (in_seq_lt i d Hi)) as H.
  pose proof (Rabs_pos (List.nth i xs 0 - List.nth i ys 0)) as HP.
  pose proof (Rsqr_abs (List.nth i xs 0 - List.nth i ys 0)) as HE.
  unfold Rsqr in HE; nra. }
pose proof (paper_main_gordon_distance_squared d xs ys) as HE.
pose proof (paper_main_gordon_distance_nonnegative d xs ys) as HP.
pose proof (pow2_sqrt (INR d) (pos_INR d)) as Hr.
pose proof (sqrt_pos (INR d)) as Hrp.
assert (Hprod : 0 <= sqrt (INR d) * delta) by (apply Rmult_le_pos; assumption).
nra.
Qed.

Lemma paper_main_gordon_set_support_continuous d T :
  (exists u, T u) -> (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  finite_joint_continuous d (paper_main_gordon_set_support d T).
Proof.
intros HT HU z eps.
set (a := sqrt (INR d)).
assert (Ha : 0 <= a) by (unfold a; apply sqrt_pos).
set (delta := eps / (a+1)).
assert (Hd : 0 < delta) by (unfold delta; apply Rdiv_lt_0_compat; [apply cond_pos|lra]).
exists (mkposreal delta Hd); intros w Hw.
pose proof (paper_main_gordon_set_support_lipschitz d T
  (coordinates_to_list d w) (coordinates_to_list d z)
  (coordinates_to_list_length d w) (coordinates_to_list_length d z) HT HU) as HL.
assert (HB : paper_main_gordon_distance d (coordinates_to_list d w) (coordinates_to_list d z) <= a*delta).
{ unfold a; apply paper_main_gordon_distance_coordinate_bound; [lra|].
  intros i Hi.
  pose proof (proj1 (coordinates_close_iff d (mkposreal delta Hd) w z) Hw i Hi) as H.
  simpl in H; lra. }
assert (HE : (a+1)*delta = eps) by (unfold delta; field; lra).
lra.
Qed.

Theorem paper_main_gordon_set_support_domain d T :
  (exists u, T u) -> (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  gaussian_covariance_domain d (paper_main_gordon_set_support d T).
Proof.
intros HT HU.
apply (gaussian_coordinate_polynomial_domain d (paper_main_gordon_set_support d T) (1+INR d) 2).
- apply paper_main_gordon_set_support_continuous; assumption.
- destruct (paper_main_gaussian_norm_polynomial d) as [HC HB]; split; [exact HC|].
  intros xs Hxs.
  pose proof (paper_main_gordon_set_support_abs d T xs Hxs HT HU) as HS.
  specialize (HB xs Hxs); rewrite Rabs_pos_eq in HB by apply paper_main_gaussian_norm_nonnegative.
  lra.
Qed.
