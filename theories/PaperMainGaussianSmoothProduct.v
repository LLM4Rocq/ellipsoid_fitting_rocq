(* C2 product tests on two independent coordinate blocks. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge2
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinatePolynomialContinuity
  PaperMainGaussianSmoothCalculus PaperMainGaussianBlockTestCalculus
  PaperMainGaussianSmoothCovariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gaussian_product_test d (f g : list R -> R) zs :=
  f (List.firstn d zs) * g (List.skipn d zs).
Definition paper_main_gaussian_product_first d (f g : list R -> R)
    (Df Dg : nat -> list R -> R) a zs :=
  if Nat.ltb a d then Df a (List.firstn d zs) * g (List.skipn d zs)
  else f (List.firstn d zs) * Dg (Nat.sub a d) (List.skipn d zs).
Definition paper_main_gaussian_product_second d (f g : list R -> R)
    (Df Dg : nat -> list R -> R) (D2f D2g : nat -> nat -> list R -> R) a b zs :=
  if Nat.ltb a d then
    if Nat.ltb b d then D2f a b (List.firstn d zs) * g (List.skipn d zs)
    else Df a (List.firstn d zs) * Dg (Nat.sub b d) (List.skipn d zs)
  else
    if Nat.ltb b d then Df b (List.firstn d zs) * Dg (Nat.sub a d) (List.skipn d zs)
    else f (List.firstn d zs) * D2g (Nat.sub a d) (Nat.sub b d) (List.skipn d zs).

Lemma paper_main_gaussian_product_continuous d f g :
  finite_joint_continuous d f -> finite_joint_continuous d g ->
  finite_joint_continuous (Nat.add d d) (paper_main_gaussian_product_test d f g).
Proof.
intros Hf Hg; unfold paper_main_gaussian_product_test.
apply finite_joint_continuous_mult; [apply paper_main_gaussian_left_continuous|apply paper_main_gaussian_right_continuous]; assumption.
Qed.

Lemma paper_main_gaussian_product_left_derivative d a f g Df :
  Nat.lt a d -> finite_coordinate_derivative d a f Df ->
  finite_coordinate_derivative (Nat.add d d) a (paper_main_gaussian_product_test d f g)
    (paper_main_gaussian_product_test d Df g).
Proof.
intros Ha HD; unfold paper_main_gaussian_product_test.
apply (paper_main_coordinate_derivative_value_ext (Nat.add d d) a _
  (fun zs => Df (List.firstn d zs) * g (List.skipn d zs) + f (List.firstn d zs) * 0)).
- apply paper_main_coordinate_derivative_mult.
  + apply paper_main_gaussian_left_derivative; assumption.
  + apply paper_main_gaussian_right_derivative_zero; exact Ha.
- intros zs Hzs; ring.
Qed.

Lemma paper_main_gaussian_product_right_derivative d a f g Dg :
  Nat.le d a -> finite_coordinate_derivative d (Nat.sub a d) g Dg ->
  finite_coordinate_derivative (Nat.add d d) a (paper_main_gaussian_product_test d f g)
    (paper_main_gaussian_product_test d f Dg).
Proof.
intros Ha HD; unfold paper_main_gaussian_product_test.
apply (paper_main_coordinate_derivative_value_ext (Nat.add d d) a _
  (fun zs => 0 * g (List.skipn d zs) + f (List.firstn d zs) * Dg (List.skipn d zs))).
- apply paper_main_coordinate_derivative_mult.
  + apply paper_main_gaussian_left_derivative_zero; exact Ha.
  + apply paper_main_gaussian_right_derivative; assumption.
- intros zs Hzs; ring.
Qed.

Lemma paper_main_gaussian_product_bound d f g M N :
  finite_polynomial_bound d M 0 f -> finite_polynomial_bound d N 0 g ->
  finite_polynomial_bound (Nat.add d d) (M * N) 0 (paper_main_gaussian_product_test d f g).
Proof.
intros Hf Hg; apply paper_main_polynomial_zero_bound in Hf; apply paper_main_polynomial_zero_bound in Hg.
destruct Hf as [HM Hf]; destruct Hg as [HN Hg].
apply paper_main_polynomial_zero_bound; split; [apply Rmult_le_pos; assumption|].
intros zs Hzs; unfold paper_main_gaussian_product_test; rewrite Rabs_mult.
destruct (paper_main_gaussian_block_lengths d zs Hzs) as [Hl Hr].
apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|apply Hf; exact Hl|apply Hg; exact Hr].
Qed.

Lemma paper_main_gaussian_product_derivative d a f g Df Dg :
  Nat.lt a (Nat.add d d) ->
  (forall i, Nat.lt i d -> finite_coordinate_derivative d i f (Df i)) ->
  (forall i, Nat.lt i d -> finite_coordinate_derivative d i g (Dg i)) ->
  finite_coordinate_derivative (Nat.add d d) a (paper_main_gaussian_product_test d f g)
    (paper_main_gaussian_product_first d f g Df Dg a).
Proof.
intros Ha HDf HDg; unfold paper_main_gaussian_product_first.
destruct (Nat.ltb a d) eqn:E.
- apply Nat.ltb_lt in E; apply paper_main_gaussian_product_left_derivative; [exact E|apply HDf; exact E].
- apply Nat.ltb_ge in E; apply paper_main_gaussian_product_right_derivative; [exact E|apply HDg; lia].
Qed.

Lemma paper_main_gaussian_product_second_derivative d a b f g Df Dg D2f D2g :
  Nat.lt a (Nat.add d d) -> Nat.lt b (Nat.add d d) ->
  (forall i, Nat.lt i d -> finite_coordinate_derivative d i f (Df i)) ->
  (forall i, Nat.lt i d -> finite_coordinate_derivative d i g (Dg i)) ->
  (forall i j, Nat.lt i d -> Nat.lt j d -> finite_coordinate_derivative d j (Df i) (D2f i j)) ->
  (forall i j, Nat.lt i d -> Nat.lt j d -> finite_coordinate_derivative d j (Dg i) (D2g i j)) ->
  finite_coordinate_derivative (Nat.add d d) b (paper_main_gaussian_product_first d f g Df Dg a)
    (paper_main_gaussian_product_second d f g Df Dg D2f D2g a b).
Proof.
intros Ha Hb HDf HDg HD2f HD2g.
unfold paper_main_gaussian_product_first, paper_main_gaussian_product_second.
destruct (Nat.ltb a d) eqn:Ea; destruct (Nat.ltb b d) eqn:Eb.
- apply Nat.ltb_lt in Ea; apply Nat.ltb_lt in Eb.
  apply paper_main_gaussian_product_left_derivative; [exact Eb|apply HD2f; assumption].
- apply Nat.ltb_lt in Ea; apply Nat.ltb_ge in Eb.
  apply paper_main_gaussian_product_right_derivative; [exact Eb|apply HDg; lia].
- apply Nat.ltb_ge in Ea; apply Nat.ltb_lt in Eb.
  apply paper_main_gaussian_product_left_derivative; [exact Eb|apply HDf; exact Eb].
- apply Nat.ltb_ge in Ea; apply Nat.ltb_ge in Eb.
  apply paper_main_gaussian_product_right_derivative; [exact Eb|apply HD2g; lia].
Qed.

Theorem paper_main_gaussian_product_smooth d f g Df Dg D2f D2g M N :
  paper_main_gaussian_smooth_test d f Df D2f M 0 ->
  paper_main_gaussian_smooth_test d g Dg D2g N 0 ->
  paper_main_gaussian_smooth_test (Nat.add d d) (paper_main_gaussian_product_test d f g)
    (paper_main_gaussian_product_first d f g Df Dg)
    (paper_main_gaussian_product_second d f g Df Dg D2f D2g) (M * N) 0.
Proof.
intros [Hf HDf HDfc HD2f HD2fc Hfb HDfb HD2fb]
  [Hg HDg HDgc HD2g HD2gc Hgb HDgb HD2gb].
constructor.
- apply paper_main_gaussian_product_continuous; assumption.
- intros a Ha; apply paper_main_gaussian_product_derivative; assumption.
- intros a Ha; unfold paper_main_gaussian_product_first; destruct (Nat.ltb a d) eqn:E.
  + apply Nat.ltb_lt in E; apply paper_main_gaussian_product_continuous; [apply HDfc; exact E|exact Hg].
  + apply Nat.ltb_ge in E; apply paper_main_gaussian_product_continuous; [exact Hf|apply HDgc; lia].
- intros a b Ha Hb; apply paper_main_gaussian_product_second_derivative; assumption.
- intros a b Ha Hb; unfold paper_main_gaussian_product_second.
  destruct (Nat.ltb a d) eqn:Ea; destruct (Nat.ltb b d) eqn:Eb.
  + apply Nat.ltb_lt in Ea; apply Nat.ltb_lt in Eb.
    apply paper_main_gaussian_product_continuous; [apply HD2fc; assumption|exact Hg].
  + apply Nat.ltb_lt in Ea; apply Nat.ltb_ge in Eb.
    apply paper_main_gaussian_product_continuous; [apply HDfc; exact Ea|apply HDgc; lia].
  + apply Nat.ltb_ge in Ea; apply Nat.ltb_lt in Eb.
    apply paper_main_gaussian_product_continuous; [apply HDfc; exact Eb|apply HDgc; lia].
  + apply Nat.ltb_ge in Ea; apply Nat.ltb_ge in Eb.
    apply paper_main_gaussian_product_continuous; [exact Hf|apply HD2gc; lia].
- apply paper_main_gaussian_product_bound; assumption.
- intros a Ha; unfold paper_main_gaussian_product_first; destruct (Nat.ltb a d) eqn:E.
  + apply Nat.ltb_lt in E; apply paper_main_gaussian_product_bound; [apply HDfb; exact E|exact Hgb].
  + apply Nat.ltb_ge in E; apply paper_main_gaussian_product_bound; [exact Hfb|apply HDgb; lia].
- intros a b Ha Hb; unfold paper_main_gaussian_product_second.
  destruct (Nat.ltb a d) eqn:Ea; destruct (Nat.ltb b d) eqn:Eb.
  + apply Nat.ltb_lt in Ea; apply Nat.ltb_lt in Eb.
    apply paper_main_gaussian_product_bound; [apply HD2fb; assumption|exact Hgb].
  + apply Nat.ltb_lt in Ea; apply Nat.ltb_ge in Eb.
    apply paper_main_gaussian_product_bound; [apply HDfb; exact Ea|apply HDgb; lia].
  + apply Nat.ltb_ge in Ea; apply Nat.ltb_lt in Eb.
    apply paper_main_gaussian_product_bound; [apply HDfb; exact Eb|apply HDgb; lia].
  + apply Nat.ltb_ge in Ea; apply Nat.ltb_ge in Eb.
    apply paper_main_gaussian_product_bound; [exact Hfb|apply HD2gb; lia].
Qed.
