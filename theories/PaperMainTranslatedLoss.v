(* The bounded smooth empirical loss used for the supercritical phase. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftExtrema PaperMainClippingRates.
Open Scope R_scope.

Definition paper_main_loss (t : R) := 1-exp(-t^2).
Definition paper_main_loss_first (t : R) := 2*t*exp(-t^2).
Definition paper_main_loss_second (t : R) := (2-4*t^2)*exp(-t^2).
Definition paper_main_loss_third (t : R) := (-12*t+8*t^3)*exp(-t^2).

Lemma paper_main_loss_bounds t : 0 <= paper_main_loss t <= 1.
Proof.
pose proof (exp_pos(-t^2)) as Hp.
assert (HE : exp(-t^2) <= 1).
{ rewrite <- exp_0; apply exp_monotone; nra. }
unfold paper_main_loss; lra.
Qed.

Lemma paper_main_loss_zero t : paper_main_loss t = 0 <-> t = 0.
Proof.
split.
- intro H; unfold paper_main_loss in H.
  assert (HE : exp(-t^2)=exp 0) by (rewrite exp_0; lra).
  assert (Ht : t^2 <= 0).
  { apply Rnot_lt_le; intro Hp.
    pose proof (exp_increasing (-t^2) 0 ltac:(nra)); lra. }
  nra.
- intro H; subst t; unfold paper_main_loss.
  replace (-0^2) with 0 by ring; rewrite exp_0; lra.
Qed.

Lemma paper_main_loss_damping t :
  t^2*exp(-t^2) <= 1 /\ t^4*exp(-t^2) <= 4.
Proof.
pose proof (paper_main_exp_polynomial_bound 1 (2*t^2) ltac:(lia) ltac:(nra)) as H1.
pose proof (paper_main_exp_polynomial_bound 2 (2*t^2) ltac:(lia) ltac:(nra)) as H2.
replace (- (2*t^2)/2) with (-t^2) in H1,H2 by field.
cbn [INR] in H1, H2.
split; nra.
Qed.

Lemma paper_main_loss_abs_damping t :
  Rabs t*exp(-t^2) <= 2 /\ Rabs(t^3)*exp(-t^2) <= 5.
Proof.
pose proof (paper_main_loss_damping t) as [H2 H4].
pose proof (exp_pos(-t^2)) as HE0.
assert (HE1 : exp(-t^2) <= 1).
{ rewrite <- exp_0; apply exp_monotone; nra. }
pose proof (Rabs_pos t) as Ha.
assert (Ha2 : (Rabs t)^2=t^2).
{ rewrite <- !Rsqr_pow2; symmetry; apply Rsqr_abs. }
assert (H1 : Rabs t <= 1+t^2) by nra.
assert (H3 : Rabs(t^3) <= 1+t^4).
{ replace (Rabs(t^3)) with ((Rabs t)^3).
  2: { simpl; rewrite !Rabs_mult Rabs_R1; ring. }
  assert (Ha4 : (Rabs t)^4=t^4).
  { replace ((Rabs t)^4) with (((Rabs t)^2)^2) by ring.
    rewrite Ha2; ring. }
  destruct (Rle_dec (Rabs t) 1) as [Hle|Hle].
  - assert (Hsq : (Rabs t)^2 <= 1) by nra.
    assert (Hcb : (Rabs t)^3 <= 1) by nra.
    nra.
  - assert (Hpow : (Rabs t)^3 <= (Rabs t)^4) by nra.
    nra. }
pose proof (Rmult_le_compat_r (exp(-t^2)) _ _ (Rlt_le _ _ HE0) H1) as HH1.
pose proof (Rmult_le_compat_r (exp(-t^2)) _ _ (Rlt_le _ _ HE0) H3) as HH3.
split; nra.
Qed.

Lemma paper_main_loss_derivative_bounds t :
  Rabs(paper_main_loss_first t) <= 4 /\
  Rabs(paper_main_loss_second t) <= 6 /\
  Rabs(paper_main_loss_third t) <= 64.
Proof.
pose proof (paper_main_loss_damping t) as [H2 H4].
pose proof (paper_main_loss_abs_damping t) as [H1 H3].
pose proof (exp_pos(-t^2)) as HE0.
assert (HE1 : exp(-t^2) <= 1).
{ rewrite <- exp_0; apply exp_monotone; nra. }
split.
- unfold paper_main_loss_first; rewrite !Rabs_mult (Rabs_pos_eq (exp(-t^2)) (Rlt_le _ _ HE0)).
  rewrite (Rabs_pos_eq 2 ltac:(lra)); nra.
split.
- unfold paper_main_loss_second; rewrite Rabs_mult (Rabs_pos_eq (exp(-t^2)) (Rlt_le _ _ HE0)).
  assert (HB : Rabs(2-4*t^2) <= 2+4*t^2) by (apply Rabs_le; nra).
  pose proof (Rmult_le_compat_r (exp(-t^2)) _ _ (Rlt_le _ _ HE0) HB); nra.
- unfold paper_main_loss_third; rewrite Rabs_mult (Rabs_pos_eq (exp(-t^2)) (Rlt_le _ _ HE0)).
  assert (HB : Rabs(-12*t+8*t^3) <= 12*Rabs t+8*Rabs(t^3)).
  { eapply Rle_trans; [apply Rabs_triang|].
    rewrite (Rabs_mult (-12) t) (Rabs_mult 8 (t^3))
      (Rabs_left (-12) ltac:(lra)) (Rabs_pos_eq 8 ltac:(lra)); lra. }
  pose proof (Rmult_le_compat_r (exp(-t^2)) _ _ (Rlt_le _ _ HE0) HB); nra.
Qed.

Lemma paper_main_loss_first_derive a t :
  derivable_pt_lim (fun u => paper_main_loss (a+u)) t (paper_main_loss_first (a+t)).
Proof. unfold paper_main_loss,paper_main_loss_first; auto_derive; simpl; ring. Qed.
Lemma paper_main_loss_second_derive a t :
  derivable_pt_lim (fun u => paper_main_loss_first (a+u)) t (paper_main_loss_second (a+t)).
Proof. unfold paper_main_loss_first,paper_main_loss_second; auto_derive; simpl; ring. Qed.
Lemma paper_main_loss_third_derive a t :
  derivable_pt_lim (fun u => paper_main_loss_second (a+u)) t (paper_main_loss_third (a+t)).
Proof. unfold paper_main_loss_second,paper_main_loss_third; auto_derive; simpl; ring. Qed.

Theorem paper_main_loss_sandwich t :
  exp(-1)*Rmin (t^2) 1 <= paper_main_loss t <= Rmin (t^2) 1.
Proof.
pose proof (paper_main_loss_bounds t) as [H0 H1].
pose proof (exp_ineq1_le (-t^2)) as HU.
pose proof (exp_ineq1_le (t^2)) as HL.
pose proof (exp_pos(-t^2)) as HE0.
assert (Hprod : exp(t^2)*exp(-t^2)= 1).
{ rewrite <- exp_plus; replace (t^2 + -t^2) with 0 by ring; apply exp_0. }
pose proof (Rmult_le_compat_r (exp(-t^2)) _ _ (Rlt_le _ _ HE0) HL) as HLL.
rewrite Hprod in HLL.
assert (HC : 2*exp(-1) <= 1).
{ pose proof (exp_ineq1_le 1) as HX.
  pose proof (Rmult_le_compat_r (exp(-1)) _ _ (Rlt_le _ _ (exp_pos _)) HX) as HH.
  rewrite <- exp_plus in HH; replace (1 + -1) with 0 in HH by ring.
  rewrite exp_0 in HH; lra. }
unfold paper_main_loss in *.
split.
- destruct (Rle_dec (t^2) 1) as [Ht|Ht].
  + rewrite (Rmin_left _ _ Ht).
    assert (HE : exp(-1) <= exp(-t^2)) by (apply exp_monotone; lra).
    assert (HH := Rmult_le_compat_l (t^2) _ _ ltac:(nra) HE); nra.
  + rewrite (Rmin_right (t^2) 1 ltac:(lra)).
    assert (HE : exp(-t^2) <= exp(-1)) by (apply exp_monotone; lra).
    lra.
- apply Rmin_glb; lra.
Qed.

Theorem paper_main_loss_lipschitz x y :
  Rabs(paper_main_loss x-paper_main_loss y) <= 4*Rabs(x-y).
Proof.
assert (HD : forall t, @is_derive R R^o R^o t 1 paper_main_loss (paper_main_loss_first t)).
{ intro t; unfold paper_main_loss,paper_main_loss_first; auto_derive; simpl; ring. }
destruct (MVT_cor4 paper_main_loss paper_main_loss_first x (Rabs(y-x))
  (fun t _ => HD t) y (Rle_refl _)) as [c [HE HC]].
replace (paper_main_loss x-paper_main_loss y) with
  (-(paper_main_loss y-paper_main_loss x)) by ring.
rewrite Rabs_Ropp HE Rabs_mult Rabs_minus_sym.
apply Rmult_le_compat_r; [apply Rabs_pos|].
exact (proj1 (paper_main_loss_derivative_bounds c)).
Qed.
