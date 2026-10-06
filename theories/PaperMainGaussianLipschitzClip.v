(* Deterministic clipping at a level K >= 0 for Euclidean-Lipschitz tests.
   The clip Rmax (-K) (Rmin K z) is 1-Lipschitz, bounded by K and equal to
   z when |z| <= K. Composed with a test, it keeps the Euclidean Lipschitz
   constant and joint continuity and gives the bounded (degree 0)
   polynomial bound of the smooth-test interface. A Euclidean-Lipschitz
   test is itself jointly continuous. This prepares smoothing; it is not a
   concentration statement. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateBasics GaussianCoordinateWeightDefinitions
  GaussianCovarianceSums PaperMainGaussianSmoothCalculus PaperMainGordonLipschitz.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_clip (K z : R) : R := Rmax (- K) (Rmin K z).

Lemma paper_main_gaussian_clip_bound K z :
  0 <= K -> Rabs (paper_main_gaussian_clip K z) <= K.
Proof.
intros HK; unfold paper_main_gaussian_clip, Rmax, Rmin.
repeat match goal with |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  unfold Rabs; destruct Rcase_abs; lra.
Qed.

Lemma paper_main_gaussian_clip_eq K z :
  Rabs z <= K -> paper_main_gaussian_clip K z = z.
Proof.
intros Hz; unfold paper_main_gaussian_clip, Rmax, Rmin.
pose proof (Rle_abs z) as H1.
pose proof (Rle_abs (- z)) as H2; rewrite Rabs_Ropp in H2.
destruct (Rle_dec K z) as [h1|h1];
  repeat match goal with |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  repeat match goal with H : ~ (_ <= _) |- _ => apply Rnot_le_lt in H end;
  lra.
Qed.

Lemma paper_main_gaussian_clip_lipschitz K z w :
  Rabs (paper_main_gaussian_clip K z - paper_main_gaussian_clip K w) <=
    Rabs (z - w).
Proof.
unfold paper_main_gaussian_clip, Rmax, Rmin.
destruct (Rle_dec K z) as [h1|h1]; destruct (Rle_dec K w) as [h2|h2];
  repeat match goal with |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  repeat match goal with H : ~ (_ <= _) |- _ => apply Rnot_le_lt in H end;
  unfold Rabs; repeat destruct Rcase_abs; lra.
Qed.

Theorem paper_main_gaussian_lipschitz_continuous d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  finite_joint_continuous d F.
Proof.
intros HL HF z eps.
pose proof (cond_pos eps) as Heps.
pose proof (sqrt_pos (INR d)) as Hsd.
set (c := L * sqrt (INR d) + 1).
assert (Hc : 0 < c) by (unfold c; nra).
assert (Hdel : 0 < eps / c) by (apply Rdiv_lt_0_compat; [exact Heps|exact Hc]).
exists (mkposreal _ Hdel); intros w Hw; simpl in Hw.
pose proof (proj1 (coordinates_close_iff d _ w z) Hw) as Hcoord.
assert (Hsum : finite_sum (fun k => (List.nth k (coordinates_to_list d w) 0 -
    List.nth k (coordinates_to_list d z) 0) ^ 2) (List.seq 0 d) <=
  INR d * (eps / c) ^ 2).
{ replace (INR d * (eps / c) ^ 2) with
    (finite_sum (fun _ => (eps / c) ^ 2) (List.seq 0 d))
    by (rewrite finite_sum_const length_seq; reflexivity).
  apply finite_sum_le; intros k Hk; apply in_seq in Hk.
  specialize (Hcoord k ltac:(lia)).
  set (t := List.nth k (coordinates_to_list d w) 0 -
    List.nth k (coordinates_to_list d z) 0) in *.
  pose proof (Rabs_pos t) as Ht.
  rewrite <- (pow2_abs t).
  apply pow_incr; lra. }
assert (Hdist : paper_main_gordon_distance d (coordinates_to_list d w)
    (coordinates_to_list d z) <= sqrt (INR d) * (eps / c)).
{ unfold paper_main_gordon_distance.
  apply Rle_trans with (sqrt (INR d * (eps / c) ^ 2));
    [apply sqrt_le_1_alt; exact Hsum|].
  rewrite (sqrt_mult_alt _ _ (pos_INR d)).
  rewrite (sqrt_pow2 _ (Rlt_le _ _ Hdel)); apply Rle_refl. }
apply Rle_lt_trans with (L * (sqrt (INR d) * (eps / c))).
- eapply Rle_trans;
    [apply HF; apply coordinates_to_list_length|].
  apply Rmult_le_compat_l; [exact HL|exact Hdist].
- apply (Rmult_lt_reg_r c); [exact Hc|].
  replace (L * (sqrt (INR d) * (eps / c)) * c) with (L * sqrt (INR d) * eps)
    by (field; apply Rgt_not_eq; exact Hc).
  unfold c; nra.
Qed.
