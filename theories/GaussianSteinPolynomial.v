(* Gaussian integration by parts for functions of polynomial growth, with
   the kernel gaussian_kernel x = exp (- x ^ 2 / 2), not normalized.
   gaussian_stein_polynomial_split: if f has a continuous derivative df,
   |f x| <= C * (1 + |x| ^ p), and df * gaussian_kernel has integral l on
   the line, then x |-> x * f x * gaussian_kernel x has integral l too.
   gaussian_stein_second_polynomial_split: if f and its derivative df have
   polynomial growth, df has a continuous derivative ddf, and
   ddf * gaussian_kernel has integral l, then
   x |-> (x * x - 1) * f x * gaussian_kernel x has integral l. Integrals
   over the line are Lebesgue integrals, so the hypotheses include the
   absolute integrability of the term with the highest derivative. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions GaussianDefinitions.
From EllipsoidFitting Require Import GaussianKernel GaussianStein GaussianDecay.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Lemma gaussian_abs_linear_polynomial_bound x p :
  Rabs x <= 1 + Rabs x ^ S p.
Proof.
  pose proof (Rabs_pos x) as Hx.
  destruct (Rle_dec (Rabs x) 1) as [Hle | Hgt].
  - pose proof (pow_le (Rabs x) (S p) Hx); lra.
  - pose proof (pow_R1_Rle (Rabs x) p (Rlt_le _ _ (Rnot_le_lt _ _ Hgt))) as Hp.
    simpl; nra.
Qed.

Lemma gaussian_polynomial_times_identity (f : R -> R) C p :
  0 <= C ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  forall x, Rabs (x * f x) <= (2*C) * (1 + Rabs x ^ S p).
Proof.
  intros HC Hb x.
  rewrite Rabs_mult.
  pose proof (Rabs_pos x) as Hx.
  pose proof (Rabs_pos (f x)) as Hf.
  specialize (Hb x).
  pose proof (gaussian_abs_linear_polynomial_bound x p) as Hp.
  pose proof (pow_le (Rabs x) (S p) Hx) as Hpow.
  simpl in Hp, Hpow |- *.
  nra.
Qed.

Lemma gaussian_polynomial_constant_nonnegative (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) -> 0 <= C.
Proof.
  intro Hb; specialize (Hb 0).
  pose proof (Rabs_pos (f 0)).
  pose proof (pow_le (Rabs 0) p (Rabs_pos 0)).
  nra.
Qed.

Theorem gaussian_stein_polynomial_split (f df : R -> R) C p l :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_has_integral (fun t => df t * gaussian_kernel t) l ->
  whole_line_has_integral (fun t => t * f t * gaussian_kernel t) l.
Proof.
  intros Hd Hc Hb Hl.
  apply gaussian_stein_split_decay with (df := df);
    [exact Hd | exact Hc | | | exact Hl].
  - exact (gaussian_polynomial_envelope_decay_neg f C p Hb).
  - exact (gaussian_polynomial_envelope_decay_pos f C p Hb).
Qed.

Theorem gaussian_stein_second_polynomial_split (f df ddf : R -> R) C p D q l :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, @is_derive R R^o R^o t 1 df (ddf t)) ->
  (forall t, {for t, continuous ddf}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (forall x, Rabs (df x) <= D * (1 + Rabs x ^ q)) ->
  whole_line_has_integral (fun x => ddf x * gaussian_kernel x) l ->
  whole_line_has_integral (fun x => (x*x - 1) * f x * gaussian_kernel x) l.
Proof.
  intros Hd Hdd Hc Hf Hdf Hl.
  pose proof (gaussian_polynomial_times_identity f C p
    (gaussian_polynomial_constant_nonnegative f C p Hf) Hf) as Hxf.
  apply gaussian_stein_second_split_decay with (df := df) (ddf := ddf);
    [exact Hd | exact Hdd | exact Hc | | | | | exact Hl].
  - exact (gaussian_polynomial_envelope_decay_neg df D q Hdf).
  - exact (gaussian_polynomial_envelope_decay_pos df D q Hdf).
  - exact (gaussian_polynomial_envelope_decay_neg (fun x => x*f x)
      (2*C) (S p) Hxf).
  - exact (gaussian_polynomial_envelope_decay_pos (fun x => x*f x)
      (2*C) (S p) Hxf).
Qed.
