(* The loss factor 1 - exp(-beta l(a + t)) as a smooth test function for
   Gaussian comparison.

   With l = paper_main_loss of Loss.Translated, the factor
   paper_main_loss_factor beta a t = 1 - exp(-beta l(a + t)) lies in
   [0, 1], and its first and second derivatives in t are at most 4 beta and
   6 beta + 16 beta^2 in absolute value (paper_main_loss_factor_bounds).
   paper_main_loss_coordinate_smooth: if F is twice differentiable with F''
   continuous and F, F', F'' bounded by C, then the function F(x_j) of one
   coordinate, with its first and second partial derivatives, satisfies
   paper_main_gaussian_smooth_test with the constant bound C (degree 0).
   paper_main_loss_factor_smooth applies this to the loss factor with
   C = 1 + 10 beta + 16 beta^2 (paper_main_loss_factor_constant). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Extrema
  Loss.Translated Analysis.CoordinateContinuityDefinitions
  Gaussian.Coordinate.DerivativeDefinitions
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Analysis.CoordinateTopology Gaussian.Coordinate.PolynomialContinuity
  Gordon.Continuity Gaussian.Smooth.Calculus Gaussian.Smooth.Test.
Open Scope R_scope.

Definition paper_main_loss_factor beta a t := 1-exp(-beta*paper_main_loss(a+t)).
Definition paper_main_loss_factor1 beta a t :=
  beta*paper_main_loss_first(a+t)*exp(-beta*paper_main_loss(a+t)).
Definition paper_main_loss_factor2 beta a t :=
  (beta*paper_main_loss_second(a+t)-beta^2*paper_main_loss_first(a+t)^2)*
    exp(-beta*paper_main_loss(a+t)).
Definition paper_main_loss_factor_constant beta := 1+10*beta+16*beta^2.

Lemma paper_main_loss_factor_bounds beta a t : 0 <= beta ->
  0 <= paper_main_loss_factor beta a t <= 1 /\
  Rabs(paper_main_loss_factor1 beta a t) <= 4*beta /\
  Rabs(paper_main_loss_factor2 beta a t) <= 6*beta+16*beta^2.
Proof.
intro Hb; pose proof (paper_main_loss_bounds(a+t)) as [HL HU].
pose proof (paper_main_loss_derivative_bounds(a+t)) as [H1 [H2 H3]].
assert (HE : 0 <= exp(-beta*paper_main_loss(a+t)) <= 1).
{ split; [apply Rlt_le,exp_pos|rewrite <- exp_0; apply exp_monotone; nra]. }
split.
- unfold paper_main_loss_factor; lra.
- split.
  + unfold paper_main_loss_factor1.
    rewrite (Rabs_mult (beta*paper_main_loss_first(a+t)) (exp(-beta*paper_main_loss(a+t))))
      (Rabs_mult beta (paper_main_loss_first(a+t)))
      (Rabs_pos_eq beta Hb) (Rabs_pos_eq _ (proj1 HE)).
    pose proof (Rabs_pos(paper_main_loss_first(a+t))) as HP.
    pose proof (Rmult_le_compat_l beta _ _ Hb H1) as HH.
    rewrite [beta*4]Rmult_comm in HH.
    pose proof (Rmult_le_compat (beta*Rabs(paper_main_loss_first(a+t)))
      (4*beta) (exp(-beta*paper_main_loss(a+t))) 1 ltac:(nra)
      (proj1 HE) HH (proj2 HE)) as HX; nra.
  + unfold paper_main_loss_factor2.
    rewrite Rabs_mult (Rabs_pos_eq _ (proj1 HE)).
    assert (HB : Rabs(beta*paper_main_loss_second(a+t)-
      beta^2*paper_main_loss_first(a+t)^2) <= 6*beta+16*beta^2).
    { eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_Ropp (Rabs_mult beta (paper_main_loss_second(a+t)))
        (Rabs_mult (beta^2) (paper_main_loss_first(a+t)^2)) (Rabs_pos_eq beta Hb)
        (Rabs_pos_eq (beta^2) ltac:(nra))
        (Rabs_pos_eq (paper_main_loss_first(a+t)^2) ltac:(nra)).
      pose proof (Rsqr_abs(paper_main_loss_first(a+t))) as HS; unfold Rsqr in HS.
      pose proof (Rabs_pos(paper_main_loss_first(a+t))) as HA1.
      assert (HS1 : paper_main_loss_first(a+t)^2 <= 16) by nra.
      pose proof (Rmult_le_compat_l beta _ _ Hb H2).
      pose proof (Rmult_le_compat_l (beta^2) _ _ ltac:(nra) HS1); nra. }
    pose proof (Rabs_pos(beta*paper_main_loss_second(a+t)-
      beta^2*paper_main_loss_first(a+t)^2)); nra.
Qed.

Lemma paper_main_loss_factor_derive beta a t :
  @is_derive R R^o R^o t 1 (paper_main_loss_factor beta a) (paper_main_loss_factor1 beta a t).
Proof.
unfold paper_main_loss_factor,paper_main_loss_factor1,paper_main_loss,paper_main_loss_first.
auto_derive; simpl; ring.
Qed.
Lemma paper_main_loss_factor1_derive beta a t :
  @is_derive R R^o R^o t 1 (paper_main_loss_factor1 beta a) (paper_main_loss_factor2 beta a t).
Proof.
unfold paper_main_loss_factor1,paper_main_loss_factor2,paper_main_loss,
  paper_main_loss_first,paper_main_loss_second.
auto_derive; simpl; ring.
Qed.
Lemma paper_main_loss_factor2_continuous beta a t :
  {for t, continuous (paper_main_loss_factor2 beta a)}.
Proof.
apply ex_derive_continuous.
unfold paper_main_loss_factor2,paper_main_loss,paper_main_loss_first,paper_main_loss_second.
auto_derive.
Qed.

Definition paper_main_loss_coordinate (F : R -> R) (j : nat) (xs : list R) := F(List.nth j xs 0).
Definition paper_main_loss_coordinate1 (F1 : R -> R) j i xs :=
  if Nat.eqb i j then paper_main_loss_coordinate F1 j xs else 0.
Definition paper_main_loss_coordinate2 (F2 : R -> R) j i k xs :=
  if Nat.eqb i j then paper_main_loss_coordinate1 F2 j k xs else 0.

Lemma paper_main_loss_coordinate_continuous d j F : (j < d)%coq_nat ->
  (forall t, {for t, continuous F}) -> finite_joint_continuous d (paper_main_loss_coordinate F j).
Proof.
intros Hj HF; unfold paper_main_loss_coordinate.
apply paper_main_gordon_joint_comp; [apply finite_joint_continuous_nth; exact Hj|].
intros xs Hxs; apply HF.
Qed.

Lemma paper_main_loss_coordinate_derivative d j F F1 i : (j < d)%coq_nat ->
  (forall t, @is_derive R R^o R^o t 1 F (F1 t)) ->
  finite_coordinate_derivative d i (paper_main_loss_coordinate F j) (paper_main_loss_coordinate1 F1 j i).
Proof.
intros Hj HD xs Hxs; unfold paper_main_loss_coordinate1,paper_main_loss_coordinate.
destruct (Nat.eqb i j) eqn:E.
- apply Nat.eqb_eq in E; subst i.
  apply (is_derive_ext (fun t => F t)).
  + intro t; rewrite (replace_coordinate_nth_same j t xs ltac:(lia)); reflexivity.
  + apply HD.
- apply Nat.eqb_neq in E.
  apply (is_derive_ext (fun _ => F(List.nth j xs 0))).
  + intro t; rewrite (replace_coordinate_nth_other i j t xs E); reflexivity.
  + apply is_derive_const.
Qed.

Theorem paper_main_loss_coordinate_smooth d j F F1 F2 C :
  (j < d)%coq_nat -> 0 <= C ->
  (forall t, @is_derive R R^o R^o t 1 F (F1 t)) ->
  (forall t, @is_derive R R^o R^o t 1 F1 (F2 t)) ->
  (forall t, {for t, continuous F2}) ->
  (forall t, Rabs(F t) <= C /\ Rabs(F1 t) <= C /\ Rabs(F2 t) <= C) ->
  paper_main_gaussian_smooth_test d (paper_main_loss_coordinate F j)
    (paper_main_loss_coordinate1 F1 j) (paper_main_loss_coordinate2 F2 j) C 0.
Proof.
intros Hj HC HD HD1 HC2 HB; constructor.
- apply paper_main_loss_coordinate_continuous; [exact Hj|].
  intro t; exact (is_derive_continuous _ _ _ (HD t)).
- intros i Hi; apply paper_main_loss_coordinate_derivative; assumption.
- intros i Hi; unfold paper_main_loss_coordinate1; destruct (Nat.eqb i j).
  + apply paper_main_loss_coordinate_continuous; [exact Hj|].
    intro t; exact (is_derive_continuous _ _ _ (HD1 t)).
  + apply finite_joint_continuous_constant.
- intros i k Hi Hk; unfold paper_main_loss_coordinate2,paper_main_loss_coordinate1.
  destruct (Nat.eqb i j).
  + apply paper_main_loss_coordinate_derivative; assumption.
  + apply paper_main_coordinate_derivative_const.
- intros i k Hi Hk; unfold paper_main_loss_coordinate2,paper_main_loss_coordinate1.
  destruct (Nat.eqb i j); [destruct (Nat.eqb k j)|];
    try apply finite_joint_continuous_constant.
  apply paper_main_loss_coordinate_continuous; assumption.
- apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; exact (proj1(HB(List.nth j xs 0))).
- intros i Hi; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; unfold paper_main_loss_coordinate1,paper_main_loss_coordinate.
  destruct (Nat.eqb i j); [exact(proj1(proj2(HB(List.nth j xs 0))))|rewrite Rabs_R0; exact HC].
- intros i k Hi Hk; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; unfold paper_main_loss_coordinate2,paper_main_loss_coordinate1,paper_main_loss_coordinate.
  destruct (Nat.eqb i j); [destruct (Nat.eqb k j)|]; try (rewrite Rabs_R0; exact HC).
  exact(proj2(proj2(HB(List.nth j xs 0)))).
Qed.

Corollary paper_main_loss_factor_smooth d j beta a : (j < d)%coq_nat -> 0 <= beta ->
  paper_main_gaussian_smooth_test d
    (paper_main_loss_coordinate (paper_main_loss_factor beta a) j)
    (paper_main_loss_coordinate1 (paper_main_loss_factor1 beta a) j)
    (paper_main_loss_coordinate2 (paper_main_loss_factor2 beta a) j)
    (paper_main_loss_factor_constant beta) 0.
Proof.
intros Hj Hb; apply paper_main_loss_coordinate_smooth; try assumption.
- unfold paper_main_loss_factor_constant; nra.
- apply paper_main_loss_factor_derive.
- apply paper_main_loss_factor1_derive.
- apply paper_main_loss_factor2_continuous.
- intro t; pose proof (paper_main_loss_factor_bounds beta a t Hb) as [[HL HU] [H1 H2]].
  rewrite (Rabs_pos_eq _ HL); unfold paper_main_loss_factor_constant; repeat split; nra.
Qed.
