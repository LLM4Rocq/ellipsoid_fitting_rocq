(* Targets and deterministic interpolation for Gaussian shifts.
   The correction is not chosen measurably: only its explicit norm bound
   will be used in probability estimates. The scalar intercept is retained
   until positivity of the common quadratic level permits rescaling. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun realfun measurable_realfun probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss normal_integral gauss_moments.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.
From GaussianAnalysis.probability Require Import symmetrization.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Condition Require Import Unsat.
From GaussianAnalysis.matrix Require Import condition_perturbation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).

Definition shifted_interpolation_size n p (L : R) (y : 'I_n -> R) :=
  L * (Num.sqrt (\sum_(i < n) y i ^+ 2) / p%:R +
    ln (p%:R : R) ^+ 4 / Num.sqrt p%:R * \big[Num.max/0]_(i < n) `|y i|).

Lemma shifted_interpolation_size_ge0 n p (L : R) (y : 'I_n -> R) :
  0 <= L -> 0 <= shifted_interpolation_size p L y.
Proof.
move=> L0; rewrite /shifted_interpolation_size.
apply: mulr_ge0 => //; apply: addr_ge0.
- by rewrite divr_ge0 ?sqrtr_ge0 ?ler0n.
- apply: mulr_ge0; first by rewrite divr_ge0 ?sqrtr_ge0 // exprn_even_ge0.
  elim/big_rec: _ => // i v _ v0.
  by rewrite le_max v0 orbT.
Qed.

Lemma shifted_interpolation_opnorm n p (L : R) (x : paper_main_sample n p) :
  0 <= L -> mixture_interpolation n p L x ->
  forall y : 'I_n -> R, exists (E : 'M[R]_p) (b : R),
    [/\ E \is symmetricmx,
      forall i : 'I_n, (paper_main_quadratic_form E (paper_main_point x i) -
        paper_main_trace E) / Num.sqrt p%:R = y i + b &
      opnorm E <= shifted_interpolation_size p L y].
Proof.
move=> L0 hI y; have [E [b [Es hE hB]]] := hI y.
have Es' : E \is symmetricmx.
  by apply/symmetricmxP/matrixP => i j; rewrite mxE Es.
exists E, b; split => //.
apply/(opnorm_symP Es' (shifted_interpolation_size_ge0 p y L0)) => v.
move: (hB v); rewrite /shifted_interpolation_size !pm_qf_col mul1mx.
by [].
Qed.

Lemma conditioned_common_level n d (x : paper_main_sample n d)
    (S : 'M[R]_d) (C t q : R) :
  S \is symmetricmx -> 0 < t ->
  (forall v : 'cV[R]_d,
    t * mxdot v v <= mxdot v (S *m v) <= C * t * mxdot v v) ->
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = q) ->
  (exists i : 'I_n, paper_main_point x i != 0) ->
  universality_conditioned_fit_event n d C x.
Proof.
move=> Ss t0 hS hq [i0 hi0].
have q0 : 0 < q.
  rewrite -(hq i0) pm_qf_col.
  have /andP[h _] := hS (paper_main_point x i0).
  apply: lt_le_trans h; apply: mulr_gt0 => //.
  by rewrite mxdot_gt0.
have qn : q != 0 := lt0r_neq0 q0.
have qi0 : 0 <= q^-1 by rewrite invr_ge0; exact: ltW.
exists (q^-1 *: S), (t / q); split; first exact: divr_gt0.
split.
- apply/uni_loewner_geP; split; first exact: uni_sym_scale _ _ _ (sym_paper _ _ Ss).
  move=> v; rewrite uni_qf_scalemx pm_qf_col pm_sqnorm_col.
  have /andP[h _] := hS v.
  have -> : t / q * mxdot v v = q^-1 * (t * mxdot v v) by ring.
  by apply: ler_wpM2l.
split.
- apply/uni_loewner_leP; split; first exact: uni_sym_scale _ _ _ (sym_paper _ _ Ss).
  move=> v; rewrite uni_qf_scalemx pm_qf_col pm_sqnorm_col.
  have /andP[_ h] := hS v.
  have -> : C * (t / q) * mxdot v v = q^-1 * (C * t * mxdot v v) by ring.
  by apply: ler_wpM2l.
- by move=> i; rewrite uni_qf_scalemx hq mulVf.
Qed.

Lemma shifted_block_common n p (g : paper_main_sample n p)
    (x : paper_main_sample n (1 + p)) (u : 'I_n -> R)
    (A E : 'M[R]_p) (s c q b : R) :
  (0 < p)%N ->
  (forall i : 'I_n, paper_main_point x i =
    col_mx (const_mx (u i) : 'cV[R]_1) (paper_main_point g i)) ->
  (forall i : 'I_n, paper_main_quadratic_form A (paper_main_point g i) = q) ->
  (forall i : 'I_n, (paper_main_quadratic_form E (paper_main_point g i) -
     paper_main_trace E) / Num.sqrt p%:R =
     - s * ((u i)^+2 - c) / Num.sqrt p%:R + b) ->
  forall i : 'I_n, paper_main_quadratic_form
    (block_mx (s%:M : 'M[R]_1) 0 0 (A + E)) (paper_main_point x i) =
    q + s * c + paper_main_trace E + Num.sqrt p%:R * b.
Proof.
move=> p0 hx hA hE i.
have pn : Num.sqrt (p%:R : R) != 0 by rewrite gt_eqF // sqrtr_gt0 ltr0n.
rewrite hx pm_qf_col quadratic_block_diag mul_scalar_mx mxdotZr.
have hu : mxdot (const_mx (u i) : 'cV[R]_1) (const_mx (u i)) = (u i)^+2.
  by rewrite /mxdot !big_ord1 !mxE expr2.
rewrite hu mulmxDl mxdotDr -!pm_qf_col hA.
have he := hE i.
have he' := congr1 (fun z : R => z * Num.sqrt p%:R) he.
rewrite /= !mulrDl !mulfVK // in he'.
nra.
Qed.

Lemma conditioned_common_cone n d (x : paper_main_sample n d)
    (S : 'M[R]_d) (C q : R) :
  cond_cone C S -> posdefmx S ->
  (forall i : 'I_n, paper_main_quadratic_form S (paper_main_point x i) = q) ->
  (exists i : 'I_n, paper_main_point x i != 0) ->
  universality_conditioned_fit_event n d C x.
Proof.
move=> [Ss [t t0 ht]] [_ Sp] hq hn.
have [i0 hi0] := hn.
have xi0 : (paper_main_point x i0)^T != 0 by rewrite trmx_eq0.
have hp := Sp _ xi0.
have ST : S^T = S by apply/symmetricmxP.
rewrite -mxdot_trmx trmx_mul trmxK ST in hp.
have tn : t != 0.
  apply/eqP => tz; have /andP[_ hh] := ht (paper_main_point x i0).
  rewrite tz mulr0 mul0r in hh.
  by have := lt_le_trans hp hh; rewrite ltxx.
have tp : 0 < t by rewrite lt_def tn t0.
exact: conditioned_common_level Ss tp ht hq hn.
Qed.

Theorem shifted_unit_block_interpolation n p (g : paper_main_sample n p)
    (x : paper_main_sample n (1 + p)) (u : 'I_n -> R)
    (A : 'M[R]_p) (D delta L c q : R) :
  (0 < p)%N -> 1 <= D -> 0 <= delta -> delta < D^-1 -> 0 <= L ->
  cond_slice D A -> mixture_interpolation n p L g ->
  (forall i : 'I_n, paper_main_point x i =
    col_mx (const_mx (u i) : 'cV[R]_1) (paper_main_point g i)) ->
  (forall i : 'I_n, paper_main_quadratic_form A (paper_main_point g i) = q) ->
  (exists i : 'I_n, paper_main_point x i != 0) ->
  shifted_interpolation_size p L (fun i => - ((u i)^+2 - c) / Num.sqrt p%:R)
    <= delta ->
  universality_conditioned_fit_event n (1 + p)
    (condition_perturbation_bound D delta) x.
Proof.
move=> p0 D1 de0 deD L0 hA hI hx hq hn hsize.
pose y (i : 'I_n) : R := - ((u i)^+2 - c) / Num.sqrt p%:R.
have [E [b [Es hE Eb]]] := shifted_interpolation_opnorm L0 hI y.
have Ee : opnorm E <= delta := le_trans Eb hsize.
pose B : 'M[R]_(1 + p) := block_mx (1%:M : 'M[R]_1) 0 0 A.
pose F : 'M[R]_(1 + p) := block_mx (0 : 'M[R]_1) 0 0 E.
have hB : cond_slice D B := cond_slice_block1 1 p0 D1 hA.
have Zs : (0 : 'M[R]_1) \is symmetricmx by apply/symmetricmxP; rewrite trmx0.
have Fs : F \is symmetricmx := symmetric_block_diag Zs Es.
have Fe : opnorm F <= delta := le_trans (opnorm_zero_block 1 Es) Ee.
have d0 : (0 < 1 + p)%N by rewrite add1n.
have [hQ Qp] := cond_slice_perturb d0 D1 hB Fs de0 Fe deD.
have BFE : B + F = block_mx (1%:M : 'M[R]_1) 0 0 (A + E).
  by rewrite /B /F add_block_mx !addr0.
rewrite BFE in hQ Qp.
apply: conditioned_common_cone hQ Qp _ hn.
apply: (@shifted_block_common n p g x u A E 1 c q b p0 hx hq) => i.
by rewrite mulN1r; exact: hE.
Qed.

Theorem shifted_weighted_block_interpolation n p (g : paper_main_sample n p)
    (x : paper_main_sample n (1 + p)) (u : 'I_n -> R)
    (A : 'M[R]_p) (D s L c q : R) :
  (0 < p)%N -> 1 <= D -> 0 < s -> s <= 1 -> 0 <= L ->
  cond_slice D A -> mixture_interpolation n p L g ->
  (forall i : 'I_n, paper_main_point x i =
    col_mx (const_mx (u i) : 'cV[R]_1) (paper_main_point g i)) ->
  (forall i : 'I_n, paper_main_quadratic_form A (paper_main_point g i) = q) ->
  (exists i : 'I_n, paper_main_point x i != 0) ->
  shifted_interpolation_size p L (fun i => - s * ((u i)^+2 - c) / Num.sqrt p%:R)
    <= (2 * D)^-1 ->
  universality_conditioned_fit_event n (1 + p) (4%:R * D ^+ 2 / s) x.
Proof.
move=> p0 D1 s0 s1 L0 hA hI hx hq hn hsize.
pose y (i : 'I_n) : R := - s * ((u i)^+2 - c) / Num.sqrt p%:R.
have [E [b [Es hE Eb]]] := shifted_interpolation_opnorm L0 hI y.
have Ee : opnorm E <= (2 * D)^-1 := le_trans Eb hsize.
have [hQ Qp] := cond_slice_weighted_block 1 D1 hA Es Ee s0 s1.
apply: conditioned_common_cone hQ Qp _ hn.
exact: (@shifted_block_common n p g x u A E s c q b p0 hx hq hE).
Qed.

Definition gaussian_centered_shift_square (a t : R) := (t + a)^+2 - (1 + a^+2).

Definition gaussian_shift_target n p (s a : R) (xi : 'rV[RR]_n) (i : 'I_n) :=
  - s * gaussian_centered_shift_square a (xi 0 i) / Num.sqrt p%:R.

Lemma gaussian_centered_shift_squareE (a t : R) :
  gaussian_centered_shift_square a t = t^+2 - 1 + 2 * a * t.
Proof. by rewrite /gaussian_centered_shift_square; ring. Qed.

Lemma shifted_normal_power_integrable k :
  (@normal_prob RR 0 1).-integrable setT (fun t => (t^+k)%:E).
Proof.
apply: (integrable_normal_poly (C := 1) (k := k)) => [|t].
- by apply: measurable_funX; exact: measurable_id.
- by rewrite normrX mul1r lerDr.
Qed.

Lemma shifted_normal_polynomial_integrable k (c : nat -> R) :
  (@normal_prob RR 0 1).-integrable setT
    (fun t => (\sum_(i < k) c i * t ^+ i)%:E).
Proof.
under eq_fun do rewrite -sumEFin.
apply: integrable_sum => // i _.
under eq_fun do rewrite EFinM.
by apply: integrableZl => //; exact: shifted_normal_power_integrable.
Qed.

Lemma shifted_normal_polynomial_integral k (c : nat -> R) :
  (\int[@normal_prob RR 0 1]_t (\sum_(i < k) c i * t ^+ i)%:E =
   \sum_(i < k) (c i)%:E * \int[@normal_prob RR 0 1]_t (t ^+ i)%:E)%E.
Proof.
under eq_integral do rewrite -sumEFin.
rewrite integral_sum //.
- move=> i; under eq_fun do rewrite EFinM.
  by apply: integrableZl => //; exact: shifted_normal_power_integrable.
- apply: eq_bigr => i _.
  under eq_integral do rewrite EFinM.
  by rewrite integralZl //; exact: shifted_normal_power_integrable.
Qed.

Lemma gaussian_centered_shift_square_polynomial (a t : R) :
  gaussian_centered_shift_square a t ^+ 2 =
  \sum_(i < 5) (match i : nat with
     | 0%N => 1 | 1%N => -4%:R*a | 2%N => 4%:R*a^+2-2
     | 3%N => 4%:R*a | _ => 1 end) * t ^+ i.
Proof.
rewrite gaussian_centered_shift_squareE !big_ord_recr big_ord0 /=.
by ring.
Qed.

Lemma gaussian_centered_shift_square_integrable (a : R) :
  (@normal_prob RR 0 1).-integrable setT
    (fun t => (gaussian_centered_shift_square a t ^+ 2)%:E).
Proof.
under eq_fun do rewrite gaussian_centered_shift_square_polynomial.
exact: (@shifted_normal_polynomial_integrable 5 (fun i : nat =>
  match i with | 0%N => 1 | 1%N => -4%:R*a | 2%N => 4%:R*a^+2-2
  | 3%N => 4%:R*a | _ => 1 end)).
Qed.

Lemma gaussian_centered_shift_square_moment (a : R) :
  (\int[@normal_prob RR 0 1]_t (gaussian_centered_shift_square a t ^+ 2)%:E =
    (2 + 4%:R * a ^+ 2)%:E)%E.
Proof.
under eq_integral do rewrite gaussian_centered_shift_square_polynomial.
rewrite (@shifted_normal_polynomial_integral 5 (fun i : nat =>
  match i with | 0%N => 1 | 1%N => -4%:R*a | 2%N => 4%:R*a^+2-2
  | 3%N => 4%:R*a | _ => 1 end)) !big_ord_recr big_ord0 /=.
have m0 : (\int[@normal_prob RR 0 1]_t (t ^+ 0)%:E = 1)%E.
  by rewrite (normal_moment_even 0) big_ord0.
have m1 : (\int[@normal_prob RR 0 1]_t (t ^+ 1)%:E = 0)%E.
  exact: (normal_moment_odd 0).
have m2 : (\int[@normal_prob RR 0 1]_t (t ^+ 2)%:E = 1)%E.
  by rewrite (normal_moment_even 1) big_ord1.
have m3 : (\int[@normal_prob RR 0 1]_t (t ^+ 3)%:E = 0)%E.
  exact: (normal_moment_odd 1).
have m4 : (\int[@normal_prob RR 0 1]_t (t ^+ 4)%:E = 3%:R%:E)%E.
  by rewrite (normal_moment_even 2) big_ord_recr big_ord1 /= mul1r.
rewrite m0 m1 m2 m3 m4 !mule0 !mule1 !mul1e !adde0 add0e -!EFinD.
by congr EFin; ring.
Qed.

Lemma gaussian_shift_target_squareE n p (s a : R) (xi : 'rV[RR]_n) (i : 'I_n) :
  gaussian_shift_target p s a xi i ^+ 2 =
    (s ^+ 2 / p%:R) * gaussian_centered_shift_square a (xi 0 i) ^+ 2.
Proof.
rewrite /gaussian_shift_target !exprMn exprVn sqrrN sqr_sqrtr ?ler0n //.
by ring.
Qed.

Lemma measurable_gaussian_shift_target n p (s a : R) (i : 'I_n) :
  measurable_fun [set: 'rV[RR]_n] (fun xi => (gaussian_shift_target p s a xi i : RR)).
Proof.
rewrite /gaussian_shift_target /gaussian_centered_shift_square.
apply: measurable_funM => //; apply: measurable_funM => //.
apply: measurable_funB => //; apply: measurable_funX.
by apply: measurable_funD => //; exact: measurable_mxentry.
Qed.

Lemma gaussian_shift_target_integrable n p (s a : R) (i : 'I_n) :
  (gauss n).-integrable setT
    (fun xi : 'rV[RR]_n => (gaussian_shift_target p s a xi i ^+ 2)%:E).
Proof.
under eq_fun do rewrite gaussian_shift_target_squareE EFinM.
apply: integrableZl => //.
have mh : measurable_fun [set: RR]
    (fun t => (gaussian_centered_shift_square a t ^+ 2)%:E).
  apply/measurable_EFinP; rewrite /gaussian_centered_shift_square.
  apply: measurable_funX; apply: measurable_funB => //.
  by apply: measurable_funX; apply: measurable_funD.
apply/(integrable_gauss_coord i mh); exact: gaussian_centered_shift_square_integrable.
Qed.

Lemma gaussian_shift_target_moment n p (s a : R) (i : 'I_n) :
  (\int[gauss n]_xi (gaussian_shift_target p s a xi i ^+ 2)%:E =
    (s ^+ 2 / p%:R * (2 + 4%:R * a ^+ 2))%:E)%E.
Proof.
under eq_integral do rewrite gaussian_shift_target_squareE EFinM.
rewrite integralZl //.
- have mh : measurable_fun [set: RR]
      (fun t => (gaussian_centered_shift_square a t ^+ 2)%:E).
    apply/measurable_EFinP; rewrite /gaussian_centered_shift_square.
    apply: measurable_funX; apply: measurable_funB => //.
    by apply: measurable_funX; apply: measurable_funD.
  apply/(integrable_gauss_coord i mh); exact: gaussian_centered_shift_square_integrable.
- by rewrite (integral_gauss_coord i (gaussian_centered_shift_square_integrable a))
    gaussian_centered_shift_square_moment -EFinM.
Qed.

Lemma gaussian_shift_target_sum_moment n p (s a : R) :
  (\int[gauss n]_xi (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2)%:E =
    (n%:R * s ^+ 2 * (2 + 4%:R * a ^+ 2) / p%:R)%:E)%E.
Proof.
under eq_integral do rewrite -sumEFin.
rewrite integral_sum //; first exact: gaussian_shift_target_integrable.
under eq_bigr do rewrite gaussian_shift_target_moment.
rewrite sumEFin sumr_const card_ord -mulr_natl.
by congr EFin; ring.
Qed.

Lemma measurable_gaussian_target_size n p (s a L : R) :
  measurable_fun [set: 'rV[RR]_n] (fun xi =>
    (shifted_interpolation_size p L (gaussian_shift_target p s a xi) : RR)).
Proof.
rewrite /shifted_interpolation_size.
apply: measurable_funM => //; apply: measurable_funD.
- apply: measurable_funM => //.
  have msum : measurable_fun [set: 'rV[RR]_n] (fun xi =>
      (\sum_(i < n) gaussian_shift_target p s a xi i ^+ 2 : RR)).
    apply: measurable_sum => i; apply: measurable_funX.
    exact: measurable_gaussian_shift_target.
  exact: measurableT_comp (continuous_measurable_fun (@sqrt_continuous RR)) msum.
- apply: measurable_funM => //.
  apply: measurable_bigmax0 => i.
  exact: measurableT_comp (@normr_measurable RR setT)
    (measurable_gaussian_shift_target p s a i).
Qed.
