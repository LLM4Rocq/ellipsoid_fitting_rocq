(* Gradient bounds for smooth Euclidean-Lipschitz tests on finitely many
   coordinates. If F has continuous coordinate derivatives DF on lists of
   length d and |F xs - F ys| <= L * dist(xs, ys) for the Euclidean
   distance of PaperMainGordonLipschitz, then the squared Euclidean norm
   of the gradient (DF a xs)_a is at most L^2. The proof follows F along
   the line through xs in the gradient direction: by the finite chain
   rule its derivative there is the squared gradient norm, while the
   Lipschitz bound limits that derivative by L times the gradient norm. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateBasics GaussianCoordinatePermutationDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCovarianceSums
  GaussianCovarianceChainRule PaperMainGordonLipschitz.
Import ListNotations.
Open Scope R_scope.

(* A derivative at 0 is bounded by any Lipschitz constant at 0. *)
Lemma paper_main_derivative_abs_le (h : R -> R) l C :
  @is_derive R R^o R^o 0 1 h l ->
  (forall s, Rabs (h s - h 0) <= C * Rabs s) ->
  Rabs l <= C.
Proof.
intros Hd Hb.
pose proof (Reals_of_is_derive Hd) as Hlim.
apply Rnot_lt_le; intros Hlt.
assert (Heps : 0 < (Rabs l - C) / 2) by lra.
destruct (Hlim _ Heps) as [delta Hdelta].
pose proof (cond_pos delta) as Hdpos.
assert (Hs0 : delta / 2 <> 0) by lra.
assert (Hsd : Rabs (delta / 2) < delta) by (rewrite Rabs_pos_eq; lra).
specialize (Hdelta _ Hs0 Hsd).
rewrite Rplus_0_l in Hdelta.
set (q := (h (delta / 2) - h 0) / (delta / 2)) in Hdelta.
assert (Hq : Rabs q <= C).
{ assert (Hspos : 0 < Rabs (delta / 2)) by (apply Rabs_pos_lt; exact Hs0).
  apply (Rmult_le_reg_r (Rabs (delta / 2))); [exact Hspos|].
  rewrite <- Rabs_mult.
  replace (q * (delta / 2)) with (h (delta / 2) - h 0)
    by (unfold q; field; lra).
  exact (Hb (delta / 2)). }
assert (Htri : Rabs l <= Rabs q + Rabs (q - l)).
{ replace l with (q - (q - l)) at 1 by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp; apply Rle_refl. }
lra.
Qed.

(* The line through xs in direction v, as a list of length d. *)
Definition paper_main_gaussian_line d (xs : list R) (v : nat -> R) (s : R) :
    list R :=
  map (fun a => List.nth a xs 0 + v a * s) (List.seq 0 d).

Lemma paper_main_gaussian_line_length d xs v s :
  List.length (paper_main_gaussian_line d xs v s) = d.
Proof. unfold paper_main_gaussian_line; apply length_map_seq. Qed.

Lemma paper_main_gaussian_line_nth d xs v s a :
  (a < d)%coq_nat ->
  List.nth a (paper_main_gaussian_line d xs v s) 0 = List.nth a xs 0 + v a * s.
Proof.
intros Ha; unfold paper_main_gaussian_line.
exact (nth_map_seq (fun a => List.nth a xs 0 + v a * s) d a Ha).
Qed.

Lemma paper_main_gaussian_line_zero d xs v :
  List.length xs = d -> paper_main_gaussian_line d xs v 0 = xs.
Proof.
intros Hxs.
apply (nth_ext _ _ 0 0).
- rewrite paper_main_gaussian_line_length; symmetry; exact Hxs.
- intros a Ha; rewrite paper_main_gaussian_line_length in Ha.
  rewrite (paper_main_gaussian_line_nth d xs v 0 a Ha); ring.
Qed.

Lemma paper_main_gaussian_line_derivative d xs v s a :
  (a < d)%coq_nat ->
  @is_derive R R^o R^o s 1
    (fun t => List.nth a (paper_main_gaussian_line d xs v t) 0) (v a).
Proof.
intros Ha.
apply (is_derive_ext (fun t => List.nth a xs 0 + v a * t)).
- intros t; symmetry; exact (paper_main_gaussian_line_nth d xs v t a Ha).
- assert (H : @is_derive R R^o R^o s 1 (fun t => List.nth a xs 0 + v a * t)
    (0 + v a * 1)).
  { apply is_derive_plus; [apply is_derive_const|].
    apply is_derive_scal; apply is_derive_id_R. }
  replace (0 + v a * 1) with (v a) in H by ring; exact H.
Qed.

Lemma paper_main_gaussian_line_distance d xs v s :
  List.length xs = d ->
  paper_main_gordon_distance d (paper_main_gaussian_line d xs v s) xs =
  Rabs s * sqrt (finite_sum (fun a => v a ^ 2) (List.seq 0 d)).
Proof.
intros Hxs; unfold paper_main_gordon_distance.
assert (Hsum : finite_sum (fun k =>
    (List.nth k (paper_main_gaussian_line d xs v s) 0 - List.nth k xs 0) ^ 2)
    (List.seq 0 d) =
  s ^ 2 * finite_sum (fun a => v a ^ 2) (List.seq 0 d)).
{ rewrite <- finite_sum_scale; apply finite_sum_ext; intros k Hk.
  apply in_seq in Hk.
  rewrite (paper_main_gaussian_line_nth d xs v s k ltac:(lia)); ring. }
rewrite Hsum.
assert (HT : 0 <= finite_sum (fun a => v a ^ 2) (List.seq 0 d))
  by (apply finite_sum_nonneg; intros; apply pow2_ge_0).
rewrite (sqrt_mult _ _ (pow2_ge_0 s) HT).
f_equal; rewrite <- sqrt_Rsqr_abs; f_equal; unfold Rsqr; ring.
Qed.

Theorem paper_main_gaussian_lipschitz_gradient d F DF L :
  (forall a, (a < d)%coq_nat -> finite_coordinate_derivative d a F (DF a)) ->
  (forall a, (a < d)%coq_nat -> finite_joint_continuous d (DF a)) ->
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  forall xs, List.length xs = d ->
    finite_sum (fun a => DF a xs ^ 2) (List.seq 0 d) <= L ^ 2.
Proof.
intros HD HC HL HLip xs Hxs.
set (g := fun a => DF a xs).
set (S := finite_sum (fun a => DF a xs ^ 2) (List.seq 0 d)).
assert (HS0 : 0 <= S)
  by (apply finite_sum_nonneg; intros; apply pow2_ge_0).
assert (HSg : finite_sum (fun a => g a ^ 2) (List.seq 0 d) = S) by reflexivity.
assert (Hder : @is_derive R R^o R^o 0 1
  (fun s => F (paper_main_gaussian_line d xs g s)) S).
{ pose proof (finite_chain_rule d F DF (paper_main_gaussian_line d xs g) g 0
    HD HC (fun s => paper_main_gaussian_line_length d xs g s)
    (fun a Ha => paper_main_gaussian_line_derivative d xs g 0 a Ha)) as H.
  rewrite (paper_main_gaussian_line_zero d xs g Hxs) in H.
  replace S with (finite_sum (fun a => DF a xs * g a) (List.seq 0 d));
    [exact H|].
  unfold S, g; apply finite_sum_ext; intros a _; ring. }
assert (Hb : forall s,
  Rabs (F (paper_main_gaussian_line d xs g s) -
        F (paper_main_gaussian_line d xs g 0)) <= (L * sqrt S) * Rabs s).
{ intros s; rewrite (paper_main_gaussian_line_zero d xs g Hxs).
  eapply Rle_trans.
  - apply HLip; [apply paper_main_gaussian_line_length|exact Hxs].
  - rewrite (paper_main_gaussian_line_distance d xs g s Hxs) HSg.
    right; ring. }
pose proof (paper_main_derivative_abs_le _ _ _ Hder Hb) as Habs.
rewrite (Rabs_pos_eq _ HS0) in Habs.
pose proof (sqrt_pos S) as Hsq0.
pose proof (sqrt_sqrt S HS0) as Hsq.
pose proof (pow2_ge_0 (L - sqrt S)) as Hsq2.
nra.
Qed.
