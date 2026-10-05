(* Port of theories/GaussianDecay.v from Coquelicot to MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements use the vocabulary of the bridge and of the port of
   GaussianKernel: Coquelicot's is_lim f p_infty l and is_lim f m_infty l,
   for a finite l, become (f x @[x --> +oo%R] --> l)%classic and
   (f x @[x --> -oo%R] --> l)%classic, and is_lim f p_infty m_infty and
   is_lim f m_infty m_infty become (f x @[x --> +oo%R] --> -oo%R)%classic
   and (f x @[x --> -oo%R] --> -oo%R)%classic. Coquelicot's neighbourhoods
   of p_infty and m_infty are the sets that contain a half line
   ]M, +oo[ or ]-oo, M[, and so are MathComp's +oo%R and -oo%R on R; the
   neighbourhoods of a finite limit are the usual ones in both libraries.
   These statements therefore say the same as the originals.

   Statements that change form.

   1. gaussian_polynomial_majorant_limit and
      gaussian_polynomial_envelope_decay. The point z : Rbar of the
      original, a finite point or an infinity, becomes any filter z on R,
      as in gaussian_bounded_product_limit of the port of GaussianKernel.
      Coquelicot's is_lim f (Finite a) l is the limit along the punctured
      neighbourhoods of a, which is z := a^' here, and is_lim f p_infty l and
      is_lim f m_infty l are z := +oo%R and z := -oo%R. The two lemmas are
      thus generalizations of the originals. The filter instance is an
      implicit argument, so the arguments keep their order and a call
      gaussian_polynomial_envelope_decay f C p (+oo%R) Hf Hk Hp has the
      shape of the original one. The original proofs call it with
      apply gaussian_polynomial_envelope_decay with (C := C) (p := p);
      that tactic now leaves the instance Filter z as a first subgoal,
      which exact _ closes, while the ssreflect form
      apply: (gaussian_polynomial_envelope_decay f C p) resolves it.

   The arithmetic in every statement is Stdlib's, as in the original.

   Axioms. The original proof of gaussian_power_exp_majorant used Stdlib's
   exp_ineq1_le, whose proof rests on Classical_Prop.classic. The port
   proves 1 + a <= exp a with MathComp's expR_ge1Dx instead, so that no
   lemma of this module needs more than the seven axioms of
   analysis/README.md. *)

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

(* The point z : Rbar of the original becomes any filter z on R (header,
   item 1). *)
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

(* The point z : Rbar of the original becomes any filter z on R (header,
   item 1). *)
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
