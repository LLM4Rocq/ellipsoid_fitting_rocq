(* Decay of the Gaussian kernel against polynomials: f x * gaussian_kernel x
   tends to 0 at +oo and at -oo when |f x| <= C * (1 + |x| ^ p)
   (gaussian_polynomial_envelope_decay_pos,
   gaussian_polynomial_envelope_decay_neg). The bound
   |x| ^ p <= p! 4^p exp (x^2 / 4) of the library (exprn_le_expR of
   GaussianAnalysis.normal_integral) gives
   |x| ^ p * gaussian_kernel x <= p! 4^p sqrt (gaussian_kernel x)
   (gaussian_abs_power_kernel_le), so f x * gaussian_kernel x tends to 0
   along every filter z on R along which the kernel does
   (gaussian_polynomial_envelope_decay): z := +oo%R, z := -oo%R, or the
   punctured neighbourhoods a^' of a point a. The filter instance is an
   implicit argument; Stdlib's apply may leave it as a subgoal, which
   exact _ closes.

   The arithmetic in every statement is Stdlib's. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import GaussianDefinitions Gaussian.Kernel.
From GaussianAnalysis Require Import normal_integral.
Open Scope R_scope.

Lemma gaussian_abs_power_kernel_le p x :
  Rabs x ^ p * gaussian_kernel x <=
  INR (p`! * 4 ^ p) * sqrt (gaussian_kernel x).
Proof.
have I4 : INR 4 = 4 by simpl; lra.
have Hb : Rabs x ^ p <= INR (p`! * 4 ^ p) * exp (x * x / 4).
  have := exprn_le_expR x p.
  by rewrite expr2 -RabsE -RpowE -!INRE -RexpE -RdivE -!RmultE I4 => /RleP.
have Hs : sqrt (gaussian_kernel x) = exp (- (x * x) / 4).
  rewrite -[RHS](sqrt_square (exp _) (Rlt_le _ _ (exp_pos _))).
  by rewrite -exp_plus /gaussian_kernel; congr (sqrt (exp _)); field.
rewrite Hs /gaussian_kernel.
apply: Rle_trans (Rmult_le_compat_r _ _ _ (Rlt_le _ _ (exp_pos _)) Hb) _.
by rewrite Rmult_assoc -exp_plus; right; congr (_ * exp _); field.
Qed.

Lemma gaussian_polynomial_envelope_decay (f : R -> R) C p (z : set_system R)
    {Fz : Filter z} :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (gaussian_kernel x @[x --> z] --> 0)%classic ->
  (f x * gaussian_kernel x @[x --> z] --> 0)%classic.
Proof.
move=> Hf Hk.
have HC : 0 <= C.
  have := Hf 0; have := Rabs_pos (f 0).
  have := pow_le (Rabs 0) p (Rabs_pos 0); nra.
set K := INR (p`! * 4 ^ p).
have Hs : (sqrt (gaussian_kernel x) @[x --> z] --> 0)%classic.
  by have := cvg_comp _ _ Hk (continuous_Rsqrt 0 (Rle_refl 0)); rewrite sqrt_0.
have HB : ((C * gaussian_kernel x + C * K * sqrt (gaussian_kernel x))
    @[x --> z] --> 0)%classic.
  have H1 := @cvgMl_tmp _ _ _ Fz gaussian_kernel C 0 Hk.
  have H2 := @cvgMl_tmp _ _ _ Fz (fun x => sqrt (gaussian_kernel x)) (C * K) 0 Hs.
  by have := @cvgD R R^o R z Fz _ _ _ _ H1 H2; rewrite !mulr0 addr0.
have HBN : ((- (C * gaussian_kernel x + C * K * sqrt (gaussian_kernel x)))
    @[x --> z] --> 0)%classic.
  by have := @cvgN R R^o R z Fz _ 0 HB; rewrite oppr0.
apply: (squeeze_cvgr _ HBN HB); apply: nearW => x.
have HE : Rabs (f x * gaussian_kernel x) <=
    C * gaussian_kernel x + C * K * sqrt (gaussian_kernel x).
  rewrite Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ (gaussian_kernel_positive x))).
  have H1 := Rmult_le_compat_r _ _ _
    (Rlt_le _ _ (gaussian_kernel_positive x)) (Hf x).
  have H2 := Rmult_le_compat_l _ _ _ HC (gaussian_abs_power_kernel_le p x).
  rewrite -/K in H2; lra.
have [L U] := proj1 (Rabs_le_between _ _) HE.
by apply/andP; split; apply/RleP.
Qed.

Theorem gaussian_polynomial_envelope_decay_pos (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (f x * gaussian_kernel x @[x --> +oo%R] --> 0)%classic.
Proof.
move=> Hf.
exact: (gaussian_polynomial_envelope_decay f C p (+oo%R) Hf
  gaussian_kernel_limit_positive).
Qed.

Theorem gaussian_polynomial_envelope_decay_neg (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (f x * gaussian_kernel x @[x --> -oo%R] --> 0)%classic.
Proof.
move=> Hf.
exact: (gaussian_polynomial_envelope_decay f C p (-oo%R) Hf
  gaussian_kernel_limit_negative).
Qed.
