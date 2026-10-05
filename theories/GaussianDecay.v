(* Decay of the Gaussian kernel against polynomials. From the bound
   |x| ^ p * gaussian_kernel x <= exp (p |x| - x * x / 2), the product
   |x| ^ p * gaussian_kernel x tends to 0 at +oo and at -oo
   (gaussian_abs_power_decay_pos, gaussian_abs_power_decay_neg). Hence
   f x * gaussian_kernel x tends to 0 at both infinities when
   |f x| <= C * (1 + |x| ^ p) (gaussian_polynomial_envelope_decay_pos and
   gaussian_polynomial_envelope_decay_neg).

   gaussian_polynomial_majorant_limit and gaussian_polynomial_envelope_decay
   state the same along any filter z on R along which gaussian_kernel x and
   |x| ^ p * gaussian_kernel x tend to 0: for example z := a^' (the
   punctured neighbourhoods of a point a), +oo%R or -oo%R. Their filter
   instance is an implicit argument; Stdlib's apply may leave it as a
   subgoal, which exact _ closes.

   The arithmetic in every statement is Stdlib's. *)

From Stdlib Require Import Reals Lia Lra Psatz Classical_Prop.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel.
Open Scope R_scope.

Lemma gaussian_power_exp_majorant (p : nat) (a : R) :
  0 <= a -> a ^ p <= exp (INR p * a).
Proof.
  intros Ha; induction p as [|p IH].
  - simpl; rewrite Rmult_0_l exp_0; apply Rle_refl.
  - rewrite S_INR.
    replace (exp ((INR p + 1) * a)) with (exp a * exp (INR p * a)).
    + simpl pow; apply Rmult_le_compat; try assumption.
      * apply pow_le; exact Ha.
      * have H1 : 1 + a <= exp a.
        { rewrite RexpE; apply/RleP; exact: expR_ge1Dx. }
        lra.
    + rewrite <- exp_plus; f_equal; ring.
Qed.

Lemma gaussian_abs_power_majorant p x :
  0 <= Rabs x ^ p * gaussian_kernel x <=
    exp (INR p * Rabs x - x * x / 2).
Proof.
  split.
  - apply Rmult_le_pos; [apply pow_le; apply Rabs_pos|].
    apply Rlt_le; apply gaussian_kernel_positive.
  - eapply Rle_trans with (exp (INR p * Rabs x) * gaussian_kernel x).
    + apply Rmult_le_compat_r.
      * apply Rlt_le; apply gaussian_kernel_positive.
      * apply gaussian_power_exp_majorant; apply Rabs_pos.
    + right; unfold gaussian_kernel; rewrite <- exp_plus.
      apply f_equal; field.
Qed.

Lemma gaussian_linear_exponent_limit_positive a :
  ((a * Rabs x - x * x / 2) @[x --> +oo%R] --> -oo%R)%classic.
Proof.
  apply/cvgrNyPle => M.
  exists (Rmax 1 (Rmax (2*a+2) (-M))); split; first exact: num_real.
  move=> x /RltP Hx; apply/RleP.
  pose proof (Rmax_l 1 (Rmax (2*a+2) (-M))).
  pose proof (Rmax_r 1 (Rmax (2*a+2) (-M))).
  pose proof (Rmax_l (2*a+2) (-M)); pose proof (Rmax_r (2*a+2) (-M)).
  have Hx0 : 0 <= x by lra.
  rewrite (Rabs_pos_eq x Hx0).
  assert (0 <= x * (x - (2*a+2))) by (apply Rmult_le_pos; lra).
  nra.
Qed.

Lemma gaussian_linear_exponent_limit_negative a :
  ((a * Rabs x - x * x / 2) @[x --> -oo%R] --> -oo%R)%classic.
Proof.
  apply/cvgrNyPle => M.
  exists (Rmin (-1) (Rmin (-(2*a+2)) M)); split; first exact: num_real.
  move=> x /RltP Hx; apply/RleP.
  pose proof (Rmin_l (-1) (Rmin (-(2*a+2)) M)).
  pose proof (Rmin_r (-1) (Rmin (-(2*a+2)) M)).
  pose proof (Rmin_l (-(2*a+2)) M); pose proof (Rmin_r (-(2*a+2)) M).
  have Hx0 : x < 0 by lra.
  rewrite (Rabs_left x Hx0).
  assert (0 <= (-x) * ((-x) - (2*a+2))) by (apply Rmult_le_pos; lra).
  nra.
Qed.

Theorem gaussian_abs_power_decay_pos p :
  (Rabs x ^ p * gaussian_kernel x @[x --> +oo%R] --> 0)%classic.
Proof.
  have Hlo : ((fun _ : R => 0) @ +oo%R --> 0)%classic by exact: cvg_cst.
  have Hhi : (exp (INR p * Rabs x - x * x / 2) @[x --> +oo%R] --> 0)%classic.
  { exact: (cvg_comp _ _
      (gaussian_linear_exponent_limit_positive (INR p)) is_lim_exp_m). }
  apply: (squeeze_cvgr _ Hlo Hhi).
  apply: nearW => x.
  have [H1 H2] := gaussian_abs_power_majorant p x.
  apply/andP; split; apply/RleP; assumption.
Qed.

Theorem gaussian_abs_power_decay_neg p :
  (Rabs x ^ p * gaussian_kernel x @[x --> -oo%R] --> 0)%classic.
Proof.
  have Hlo : ((fun _ : R => 0) @ -oo%R --> 0)%classic by exact: cvg_cst.
  have Hhi : (exp (INR p * Rabs x - x * x / 2) @[x --> -oo%R] --> 0)%classic.
  { exact: (cvg_comp _ _
      (gaussian_linear_exponent_limit_negative (INR p)) is_lim_exp_m). }
  apply: (squeeze_cvgr _ Hlo Hhi).
  apply: nearW => x.
  have [H1 H2] := gaussian_abs_power_majorant p x.
  apply/andP; split; apply/RleP; assumption.
Qed.

Lemma gaussian_polynomial_majorant_limit C p (z : set_system R)
    {Fz : Filter z} :
  (gaussian_kernel x @[x --> z] --> 0)%classic ->
  (Rabs x ^ p * gaussian_kernel x @[x --> z] --> 0)%classic ->
  (C * (1 + Rabs x ^ p) * gaussian_kernel x @[x --> z] --> 0)%classic.
Proof.
  move=> Hk Hp.
  have Hs : (gaussian_kernel x + Rabs x ^ p * gaussian_kernel x
      @[x --> z] --> 0)%classic.
  { have H := @cvgD R R^o R z Fz _ _ 0 0 Hk Hp.
    rewrite addr0 in H; exact H. }
  have HC : (C * (gaussian_kernel x + Rabs x ^ p * gaussian_kernel x)
      @[x --> z] --> 0)%classic.
  { have H := @cvgMl_tmp _ _ _ Fz
      (fun x => gaussian_kernel x + Rabs x ^ p * gaussian_kernel x) C 0 Hs.
    rewrite mulr0 in H; exact H. }
  have E : (fun x => C * (1 + Rabs x ^ p) * gaussian_kernel x) =1
      (fun x => C * (gaussian_kernel x + Rabs x ^ p * gaussian_kernel x)).
  { move=> x; ring. }
  rewrite (eq_cvg _ _ E).
  exact: HC.
Qed.

Lemma gaussian_polynomial_envelope_decay (f : R -> R) C p (z : set_system R)
    {Fz : Filter z} :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (gaussian_kernel x @[x --> z] --> 0)%classic ->
  (Rabs x ^ p * gaussian_kernel x @[x --> z] --> 0)%classic ->
  (f x * gaussian_kernel x @[x --> z] --> 0)%classic.
Proof.
  move=> Hf Hk Hp.
  assert (HE : forall x, Rabs (f x * gaussian_kernel x) <=
    C * (1 + Rabs x ^ p) * gaussian_kernel x).
  { intros x; rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (gaussian_kernel x)
      (Rlt_le _ _ (gaussian_kernel_positive x))).
    apply Rmult_le_compat_r;
      [apply Rlt_le; apply gaussian_kernel_positive|apply Hf]. }
  have Hhi := @gaussian_polynomial_majorant_limit C p z Fz Hk Hp.
  have Hlo : (- (C * (1 + Rabs x ^ p) * gaussian_kernel x)
      @[x --> z] --> 0)%classic.
  { have H := @cvgN R R^o R z Fz _ 0 Hhi.
    rewrite oppr0 in H; exact H. }
  apply: (squeeze_cvgr _ Hlo Hhi).
  apply: nearW => x.
  pose proof (Rle_abs (f x * gaussian_kernel x)).
  pose proof (Rle_abs (-(f x * gaussian_kernel x))) as Ho.
  rewrite Rabs_Ropp in Ho; specialize (HE x).
  apply/andP; split; apply/RleP; lra.
Qed.

Theorem gaussian_polynomial_envelope_decay_pos (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (f x * gaussian_kernel x @[x --> +oo%R] --> 0)%classic.
Proof.
  intros Hf.
  apply (gaussian_polynomial_envelope_decay f C p (+oo%R)).
  - exact Hf.
  - exact gaussian_kernel_limit_positive.
  - exact (gaussian_abs_power_decay_pos p).
Qed.

Theorem gaussian_polynomial_envelope_decay_neg (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (f x * gaussian_kernel x @[x --> -oo%R] --> 0)%classic.
Proof.
  intros Hf.
  apply (gaussian_polynomial_envelope_decay f C p (-oo%R)).
  - exact Hf.
  - exact gaussian_kernel_limit_negative.
  - exact (gaussian_abs_power_decay_neg p).
Qed.
