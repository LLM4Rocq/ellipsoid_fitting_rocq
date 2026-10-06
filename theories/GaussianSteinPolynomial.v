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
