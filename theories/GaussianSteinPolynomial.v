(* Port of theories/GaussianSteinPolynomial.v from Coquelicot to
   MathComp-Analysis.

   Every lemma of the original keeps its name and its arguments, in the same
   order. The statements use the vocabulary of AnalysisIntegralDefinitions
   and of the bridge, as in the ports of GaussianKernel and GaussianStein:
   Coquelicot's is_derive f x l becomes @is_derive R R^o R^o x 1 f l,
   continuous f x becomes {for x, continuous f}, and
   is_RInt_gen f (Rbar_locally m_infty) (Rbar_locally p_infty) l becomes
   whole_line_has_integral f l, which is Lebesgue integrability on the line
   with integral l (difference 4 of analysis/README.md). The arithmetic in
   every statement is Stdlib's, as in the original.

   gaussian_abs_linear_polynomial_bound, gaussian_polynomial_times_identity
   and gaussian_polynomial_constant_nonnegative are statements about real
   numbers only. They keep their text and their proofs.

   Statements that change form.

   1. gaussian_stein_polynomial has one more hypothesis, the last one:
      whole_line_integrable (fun t => df t * gaussian_kernel t), which is
      gaussian_integral_exists df. Without an added hypothesis the
      statement is false for the Lebesgue integral, as the header of
      GaussianDefinitions says: f x = sin (exp (x * x)) is bounded, so it
      satisfies the polynomial bound with C = 1 and p = 0, and it has a
      continuous derivative df, but gaussian_stein_integrand f df is not
      absolutely integrable. The improper Riemann integral of the original
      exists in that case; the Lebesgue integral does not. The header of
      GaussianDefinitions asks for the integrability of the integrand
      gaussian_stein_integrand f df. Under the other hypotheses the two are
      equivalent, because x * f x * gaussian_kernel x is then integrable.
      From the added hypothesis this is gaussian_stein_moment_integrable of
      GaussianStein; from the integrability of the integrand it follows
      from the polynomial bound on the continuous function f, a fact that
      this module does not prove. The integrability of
      df t * gaussian_kernel t is the form that the challenge statements
      provide, since they bound df by a polynomial. This is the same choice
      as for gaussian_stein_improper in the port of GaussianKernel.

   2. gaussian_stein_second_polynomial has one more hypothesis, the last
      one: whole_line_integrable (fun x => ddf x * gaussian_kernel x), which
      is gaussian_integral_exists ddf. The example of the header of
      GaussianStein shows that some added hypothesis is needed: take
      df x = sin (exp (x * x)) and f its primitive from 0, which is bounded;
      f and df satisfy the polynomial bounds, but ddf x * gaussian_kernel x
      is not absolutely integrable. Under the other hypotheses the added
      one implies the integrability of the integrand of the conclusion
      (gaussian_stein_second_integrand_integrable of GaussianStein). The
      converse holds too, since (x*x - 1) * f x * gaussian_kernel x is
      integrable when f is continuous and bounded by a polynomial, but this
      module does not prove it.

   gaussian_stein_polynomial_split and gaussian_stein_second_polynomial_split
   need no new hypothesis: their hypothesis gives the integrability of the
   term with the highest derivative. They say the same thing as before, in
   the new vocabulary, and their proofs apply gaussian_stein_split_decay and
   gaussian_stein_second_split_decay of the port of GaussianStein, as
   before.

   The original imported Classical_Prop but did not use it. This port does
   not import it, so the assumptions of the module are the seven axioms of
   analysis/README.md. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
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

(* Added hypothesis, the last one: df t * gaussian_kernel t is integrable on
   the line (header, item 1). *)
Theorem gaussian_stein_polynomial (f df : R -> R) C p :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, {for t, continuous df}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  whole_line_integrable (fun t => df t * gaussian_kernel t) ->
  whole_line_has_integral (gaussian_stein_integrand f df) 0.
Proof.
  intros Hd Hc Hb Hi.
  have Hx := gaussian_stein_moment_integrable f df Hd Hc Hi.
  apply gaussian_stein_improper_decay; [exact Hd | exact Hc | | | ].
  - exact (gaussian_polynomial_envelope_decay_neg f C p Hb).
  - exact (gaussian_polynomial_envelope_decay_pos f C p Hb).
  - apply: (eq_integrable measurableT _ _ _ (integrableB measurableT Hi Hx)).
    move=> y _ /=.
    by rewrite -EFinB /gaussian_stein_integrand -RminusE.
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

(* Added hypothesis, the last one: ddf x * gaussian_kernel x is integrable
   on the line (header, item 2). *)
Theorem gaussian_stein_second_polynomial (f df ddf : R -> R) C p D q :
  (forall t, @is_derive R R^o R^o t 1 f (df t)) ->
  (forall t, @is_derive R R^o R^o t 1 df (ddf t)) ->
  (forall t, {for t, continuous ddf}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (forall x, Rabs (df x) <= D * (1 + Rabs x ^ q)) ->
  whole_line_integrable (fun x => ddf x * gaussian_kernel x) ->
  whole_line_has_integral
    (fun x => (ddf x - (x*x - 1) * f x) * gaussian_kernel x) 0.
Proof.
  intros Hd Hdd Hc Hf Hdf Hi.
  pose proof (gaussian_polynomial_times_identity f C p
    (gaussian_polynomial_constant_nonnegative f C p Hf) Hf) as Hxf.
  have Iz := gaussian_stein_second_integrand_integrable f df ddf Hd Hdd Hc Hi.
  apply gaussian_stein_second_decay with (df := df);
    [exact Hd | exact Hdd | exact Hc | | | | | exact Iz].
  - exact (gaussian_polynomial_envelope_decay_neg df D q Hdf).
  - exact (gaussian_polynomial_envelope_decay_pos df D q Hdf).
  - exact (gaussian_polynomial_envelope_decay_neg (fun x => x*f x)
      (2*C) (S p) Hxf).
  - exact (gaussian_polynomial_envelope_decay_pos (fun x => x*f x)
      (2*C) (S p) Hxf).
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
