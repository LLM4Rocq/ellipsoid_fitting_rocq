(* Port of theories/GaussianIntegration.v from Coquelicot to
   MathComp-Analysis.

   Every theorem and lemma of the original keeps its name and its
   arguments, in the same order, and no statement gains or loses a
   hypothesis. The statements use the vocabulary of the ported
   GaussianDefinitions and of the bridge:
   - continuous f x becomes {for x, continuous f} (difference 5 of
     analysis/README.md);
   - is_derive f x l becomes @is_derive R R^o R^o x 1 f l;
   - the bound variable in front of a derivative or a continuity
     hypothesis is written x : R, as in the restated challenge
     ellipsoid_gaussian (analysis/challenges/ellipsoid_gaussian), so that
     its type is literally R.
   The arithmetic in every statement is Stdlib's, as in the original.

   Meaning. gaussian_integral_exists, gaussian_has_integral,
   gaussian_absolutely_integrable and gaussian_expectation keep their text,
   and follow the ported GaussianDefinitions: they now state Borel
   measurability and Lebesgue integrability over the line of
   x |-> f x * gaussian_kernel x (difference 4 of analysis/README.md).
   Every integrand of this module is continuous and bounded in absolute
   value by a polynomial times the kernel under the hypotheses of its
   statement, and for such a function the Lebesgue and the improper Riemann
   readings both hold and give the same value. So the statements say the
   same as before. They are, in this order, the clauses 2 (continuity of
   the density), 3, 5 and 6 of the restated challenge ellipsoid_gaussian.

   gaussian_first_stein and gaussian_second_stein keep their hypotheses.
   The added integrability hypotheses of gaussian_stein_polynomial and
   gaussian_stein_second_polynomial (see the header of the ported
   GaussianSteinPolynomial) do not reach them, because their proofs go
   through gaussian_stein_polynomial_split and
   gaussian_stein_second_polynomial_split, whose hypothesis is the
   integral of the highest derivative, which the polynomial bound on that
   derivative provides.

   What changes in the proofs. The continuity arguments use continuous_mult,
   continuous_minus, continuous_const and continuous_id of the bridge in
   place of Coquelicot's, and is_derive_continuous of the bridge in place of
   ex_derive_continuous. The rest is unchanged.

   The original imported Classical_Prop but did not use it. This port does
   not import it. Print Assumptions on the theorems of this module lists
   only the seven axioms of analysis/README.md (the real-number lemmas
   need fewer), so Classical_Prop.classic is not among them. *)

From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2.
From EllipsoidFitting Require Import AnalysisIntegralDefinitions.
From EllipsoidFitting Require Import GaussianDefinitions GaussianKernel GaussianMass
  GaussianDecay GaussianStein GaussianSteinPolynomial GaussianMoments
  GaussianExpectation GaussianAdmissible.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Theorem gaussian_polynomial_admissible (f : R -> R) C p :
  (forall x : R, {for x, continuous f}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  gaussian_integral_exists f /\ gaussian_absolutely_integrable f.
Proof. exact (gaussian_polynomial_integrals_exist f C p). Qed.

Theorem gaussian_power_moments n :
  gaussian_has_integral (fun x => x ^ n) (moment_factor n * gaussian_mass) /\
  gaussian_integral_exists (fun x => x ^ n) /\
  gaussian_absolutely_integrable (fun x => x ^ n) /\
  gaussian_expectation (fun x => x ^ n) = moment_factor n.
Proof.
  pose proof (gaussian_raw_moments gaussian_mass gaussian_kernel_mass_integral n) as HI.
  assert (Hb : forall x, Rabs (x^n) <= 1 * (1 + Rabs x ^ n)).
  { intro x; rewrite <- RPow_abs; lra. }
  destruct (gaussian_polynomial_admissible (fun x => x^n) 1 n
    (gaussian_power_continuous n) Hb) as [He Ha].
  split; [exact HI|]. split; [exact He|]. split; [exact Ha|].
  unfold gaussian_expectation.
  rewrite (gaussian_integral_unique (fun x => x^n) (moment_factor n * gaussian_mass) HI).
  pose proof gaussian_mass_positive; field; lra.
Qed.

Theorem gaussian_standard_moments :
  gaussian_expectation (fun x => x ^ 0) = 1 /\
  gaussian_expectation (fun x => x ^ 1) = 0 /\
  gaussian_expectation (fun x => x ^ 2) = 1 /\
  gaussian_expectation (fun x => x ^ 4) = 3.
Proof.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 0)))) as H0.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 1)))) as H1.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 2)))) as H2.
  pose proof (proj2 (proj2 (proj2 (gaussian_power_moments 4)))) as H4.
  simpl moment_factor in H0, H1, H2, H4; simpl INR in H2, H4.
  repeat split; lra.
Qed.

Lemma gaussian_power_bound_two_higher x p :
  Rabs x ^ p <= 1 + Rabs x ^ S (S p).
Proof.
  pose proof (Rabs_pos x) as Hx.
  pose proof (pow_le (Rabs x) p Hx) as Hp.
  pose proof (pow_le (Rabs x) (S (S p)) Hx) as Hq.
  destruct (Rle_dec (Rabs x) 1) as [Hle|Hgt].
  - pose proof (pow_incr (Rabs x) 1 p (conj Hx Hle)) as H.
    rewrite pow1 in H; lra.
  - assert (1 <= Rabs x * Rabs x) by nra.
    simpl; nra.
Qed.

Lemma gaussian_centered_square_polynomial_bound (f : R -> R) C p :
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  forall x, Rabs ((x*x - 1) * f x) <= (6*C) * (1 + Rabs x ^ S (S p)).
Proof.
  intro Hf.
  pose proof (gaussian_polynomial_constant_nonnegative f C p Hf) as HC.
  pose proof (gaussian_polynomial_times_identity f C p HC Hf) as Hxf.
  pose proof (gaussian_polynomial_times_identity (fun x => x*f x) (2*C) (S p)
    ltac:(lra) Hxf) as Hxxf.
  intro x; specialize (Hxxf x); specialize (Hf x).
  pose proof (gaussian_power_bound_two_higher x p) as Hp.
  pose proof (pow_le (Rabs x) (S (S p)) (Rabs_pos x)) as Hq.
  pose proof (Rabs_triang (x * (x * f x)) (-f x)) as Habs.
  rewrite Rabs_Ropp in Habs.
  replace ((x*x-1)*f x) with (x*(x*f x)+(-f x)) by ring.
  nra.
Qed.

Theorem gaussian_first_stein (f df : R -> R) C p D q :
  (forall x : R, @is_derive R R^o R^o x 1 f (df x)) ->
  (forall x : R, {for x, continuous df}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (forall x, Rabs (df x) <= D * (1 + Rabs x ^ q)) ->
  gaussian_integral_exists f /\ gaussian_absolutely_integrable f /\
  gaussian_integral_exists df /\ gaussian_absolutely_integrable df /\
  gaussian_integral_exists (fun x => x * f x) /\
  gaussian_absolutely_integrable (fun x => x * f x) /\
  gaussian_expectation df = gaussian_expectation (fun x => x * f x).
Proof.
  intros Hd Hc Hf Hdf.
  assert (Hfc : forall x : R, {for x, continuous f}).
  { intro x; exact (is_derive_continuous f x (df x) (Hd x)). }
  assert (Hxfc : forall x : R, {for x, continuous (fun t => t*f t)}).
  { intro x; apply (continuous_mult R); [apply continuous_id|apply Hfc]. }
  pose proof (gaussian_polynomial_times_identity f C p
    (gaussian_polynomial_constant_nonnegative f C p Hf) Hf) as Hxf.
  destruct (gaussian_polynomial_admissible f C p Hfc Hf) as [If Af].
  destruct (gaussian_polynomial_admissible df D q Hc Hdf) as [Idf Adf].
  destruct (gaussian_polynomial_admissible (fun x => x*f x) (2*C) (S p) Hxfc Hxf)
    as [Ixf Axf].
  pose proof (gaussian_stein_polynomial_split f df C p (gaussian_integral df)
    Hd Hc Hf (gaussian_integral_correct df Idf)) as HI.
  split; [exact If|]. split; [exact Af|]. split; [exact Idf|].
  split; [exact Adf|]. split; [exact Ixf|]. split; [exact Axf|].
  unfold gaussian_expectation.
  rewrite (gaussian_integral_unique (fun x => x*f x) (gaussian_integral df) HI).
  reflexivity.
Qed.

Theorem gaussian_second_stein (f df ddf : R -> R) C p D q E r :
  (forall x : R, @is_derive R R^o R^o x 1 f (df x)) ->
  (forall x : R, @is_derive R R^o R^o x 1 df (ddf x)) ->
  (forall x : R, {for x, continuous ddf}) ->
  (forall x, Rabs (f x) <= C * (1 + Rabs x ^ p)) ->
  (forall x, Rabs (df x) <= D * (1 + Rabs x ^ q)) ->
  (forall x, Rabs (ddf x) <= E * (1 + Rabs x ^ r)) ->
  gaussian_integral_exists f /\ gaussian_absolutely_integrable f /\
  gaussian_integral_exists df /\ gaussian_absolutely_integrable df /\
  gaussian_integral_exists ddf /\ gaussian_absolutely_integrable ddf /\
  gaussian_integral_exists (fun x => (x*x - 1) * f x) /\
  gaussian_absolutely_integrable (fun x => (x*x - 1) * f x) /\
  gaussian_expectation ddf = gaussian_expectation (fun x => (x*x - 1) * f x).
Proof.
  intros Hd Hdd Hc Hf Hdf Hddf.
  assert (Hfc : forall x : R, {for x, continuous f}).
  { intro x; exact (is_derive_continuous f x (df x) (Hd x)). }
  assert (Hdfc : forall x : R, {for x, continuous df}).
  { intro x; exact (is_derive_continuous df x (ddf x) (Hdd x)). }
  assert (Hh : forall x : R, {for x, continuous (fun t => (t*t-1)*f t)}).
  { intro x; apply (continuous_mult R).
    - apply (continuous_minus R).
      + apply (continuous_mult R); apply continuous_id.
      + apply (continuous_const R).
    - apply Hfc. }
  pose proof (gaussian_centered_square_polynomial_bound f C p Hf) as Hhb.
  destruct (gaussian_polynomial_admissible f C p Hfc Hf) as [If Af].
  destruct (gaussian_polynomial_admissible df D q Hdfc Hdf) as [Idf Adf].
  destruct (gaussian_polynomial_admissible ddf E r Hc Hddf) as [Iddf Addf].
  destruct (gaussian_polynomial_admissible (fun x => (x*x-1)*f x)
    (6*C) (S (S p)) Hh Hhb) as [Ih Ah].
  pose proof (gaussian_stein_second_polynomial_split f df ddf C p D q
    (gaussian_integral ddf) Hd Hdd Hc Hf Hdf (gaussian_integral_correct ddf Iddf)) as HI.
  split; [exact If|]. split; [exact Af|]. split; [exact Idf|].
  split; [exact Adf|]. split; [exact Iddf|]. split; [exact Addf|].
  split; [exact Ih|]. split; [exact Ah|].
  unfold gaussian_expectation.
  rewrite (gaussian_integral_unique (fun x => (x*x-1)*f x) (gaussian_integral ddf) HI).
  reflexivity.
Qed.
