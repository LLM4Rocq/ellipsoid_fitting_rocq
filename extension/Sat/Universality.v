(* Theorem 1.2 (i) of Koehler and Sohn, "Universality and sharp thresholds
   for ellipsoid fitting" (arXiv 2608.27372, lines 164-190, proof lines
   976-991), at Stdlib's R: below the threshold, with probability tending
   to one, the points have a positive definite fit of value 1 with a
   condition number bounded by a constant. Item S11 of stage 3 of phase 5
   (lane A).

   Hypothesis. small_residual_interpolation kappa K alpha is Theorem 1.9
   of the paper in the form that small_residual_interpolation_holds
   (Sat/SmallResidual, item S10 of lane C) proves: with probability
   tending to one, every y in R^n with |y_i| <= Y for every i is
   <W_i, Delta> = y_i + b for some symmetric Delta with
   opnorm Delta <= C1 ((ln d)^4 / sqrt d Y + |y| / d) and some real b,
   where W_i = sample_W x i = (x_i x_i^T - I) / sqrt d. This is
   interpolation_det of Sat/Interpolation on the event of Theorem 2.3,
   with a = c sqrt d / (ln d)^4 and D = d.

   Main results.
   - universality_sat_of_interpolation: the first conjunct of
     universality_statement (Theorem 1.2 (i)) from
     small_residual_interpolation, with condition number c = 4 M / m for
     the constants 0 < m < 1 < M of approximate_fit (Sat/ApproximateFit,
     item S1).
   - universality_statement_of_interpolation: universality_statement,
     both parts, from small_residual_interpolation for every kappa > 1,
     K > 0 and 0 < alpha < alpha*(kappa). The second part is
     universality_unsat of Unsat/Universality. universality_theorem
     (UniversalityTheorem.v) applies it to
     small_residual_interpolation_holds.

   Proof. Take delta with C1 sqrt (2 alpha delta) = m / 4. Outside the
   union of the event of approximate_fit, the event of Theorem 1.9 and the
   event that every point is zero, the residual y_i = b - <W_i, R> of the
   approximate fit R has |y_i| <= C ln d and
   |y| <= sqrt (delta n) <= sqrt (2 alpha delta) d, so Theorem 1.9 gives
   Delta with opnorm Delta <= m / 2 once
   C1 C (ln d)^5 / sqrt d <= m / 4 (ln_pow5_le). Then S = R + Delta has
   all <W_i, S> equal and m / 2 I <= S <= (M + m / 2) I, so
   x_i^T S x_i = sqrt d <W_i, S> + tr S is a common value t, with
   t >= m / 2 |x_i|^2 > 0 for a point x_i != 0, and S / t is a fit of
   value 1 with lm = m / (2 t) and lm I <= S / t <= c lm I (sat_fit_det,
   sat_at_d). All the points vanish with probability at most
   (1 - 1 / kappa)^n (sample_points_zero): a coordinate law of fourth
   moment kappa has P(x != 0) >= 1 / kappa (coordinate_nonzero, from
   x^2 <= x^4 / (2 kappa) + kappa / 2 1_(x != 0)), and the first
   coordinates of the points are independent. The conditioned event is
   contained in the positive definite one (cond_sub_pd), and both are
   measurable (Model/Measurability, item U11). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From mathcomp Require Import numfun measurable_realfun sequences.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import conditioning.
From GaussianAnalysis.convex Require Import logdet_barrier.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Measurability.Fit Measurability.Balanced.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import UniversalityStatement.
From EllipsoidUniversality.Features Require Import Definitions Regular.
From EllipsoidUniversality.Model Require Import Rows Measurability.
From EllipsoidUniversality.Unsat Require Import LeastSquares Regularized.
From EllipsoidUniversality.Unsat Require Import Universality.
From EllipsoidUniversality.Sat Require Import Apriori ApproximateFit.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* Theorem 1.9 in the form that the assembly of Theorem 1.2 (i) takes as
   its hypothesis. *)
Definition small_residual_interpolation (kappa K alpha : R) : Prop :=
  exists C1 : R, 0 < C1 /\
  forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (universality_probability (nu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (y : 'rV[R]_(n d)) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y +
                frobenius y / d%:R)]].

(* 1. Some point is not zero, with probability tending to one. *)

Section zero_points.
Variables (kappa K : R) (mu : probability (measurableTypeR R) R).
Hypotheses (hmu : universality_coordinate_law kappa K mu) (k1 : 1 < kappa).

(* x^2 <= x^4 / (2 kappa) + kappa / 2 1_(x != 0), integrated:
   P(x != 0) >= 1 / kappa. *)
Lemma coordinate_nonzero :
  (kappa^-1%:E <= mu [set x : measurableTypeR R | ((x : R) != 0)%R])%E.
Proof.
have k0 : 0 < kappa by apply: lt_trans k1.
pose A := [set x : measurableTypeR R | (x : R) != 0].
have mA : measurable A.
  have -> : A = ~` [set (0 : R)].
    by apply/seteqP; split => x /=; [move=> /eqP|move=> h; apply/eqP].
  exact: measurableC.
pose g (x : measurableTypeR R) : RR :=
  (x : R) ^+ 4 / (2 * kappa) + kappa / 2 * (\1_A x : RR).
have hpt (x : measurableTypeR R) : ((x : R) ^+ 2 <= g x)%R.
  rewrite /g indicE; have [x0|x0] := eqVneq (x : R) 0.
    rewrite x0 expr0n /= expr0n /= mul0r add0r.
    by apply: mulr_ge0; [rewrite divr_ge0 // ltW | exact: ler0n].
  rewrite mem_set //= mulr1.
  have : (0 <= ((x : R) ^+ 2 - kappa) ^+ 2 / (2 * kappa))%R.
    by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
  have kn : kappa != 0 by rewrite gt_eqF.
  have -> : (((x : R) ^+ 2 - kappa) ^+ 2 / (2 * kappa) =
      (x : R) ^+ 4 / (2 * kappa) + kappa / 2 - (x : R) ^+ 2)%R.
    by field.
  by rewrite subr_ge0.
have i4 := coordinate_law_integrable kappa K mu hmu 4.
have mI : measurable_fun setT (fun x : measurableTypeR R => (\1_A x : RR)).
  exact: measurable_indic.
have h2 := coordinate_law_second kappa K mu hmu.
have h4 := coordinate_law_fourth kappa K mu hmu.
have hle : (\int[mu]_x ((x : R) ^+ 2)%:E <= \int[mu]_x (g x)%:E)%E.
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin sqr_ge0.
  - apply/measurable_EFinP; exact: measurable_funX.
  - apply/measurable_EFinP; apply: measurable_funD.
      by apply: measurable_funM => //; exact: measurable_funX.
    by apply: measurable_funM => //.
  - by move=> x _; rewrite lee_fin.
have m4 : measurable_fun setT
    (fun x : measurableTypeR R => ((x : R) ^+ 4 : RR)%:E).
  by apply/measurable_EFinP; exact: measurable_funX.
have p4 (x : measurableTypeR R) : setT x -> (0 <= ((x : R) ^+ 4 : RR)%:E)%E.
  by move=> _; rewrite lee_fin exprn_even_ge0.
have mI' : measurable_fun setT
    (fun x : measurableTypeR R => ((\1_A x : RR))%:E).
  by apply/measurable_EFinP.
have pI (x : measurableTypeR R) : setT x -> (0 <= ((\1_A x : RR))%:E)%E.
  by move=> _; rewrite lee_fin indicE ler0n.
have kk : (0 <= (2 * kappa)^-1 :> RR)%R by rewrite invr_ge0 mulr_ge0 // ltW.
have k2 : (0 <= kappa / 2 :> RR)%R by rewrite divr_ge0 // ltW.
have I4 : (\int[mu]_x ((x : R) ^+ 4 / (2 * kappa) : RR)%:E =
    (2 * kappa)^-1%:E * \int[mu]_x ((x : R) ^+ 4)%:E)%E.
  under eq_integral do rewrite mulrC EFinM.
  by rewrite ge0_integralZl.
have II : (\int[mu]_x (kappa / 2 * (\1_A x : RR))%:E = (kappa / 2)%:E * mu A)%E.
  under eq_integral do rewrite EFinM.
  by rewrite ge0_integralZl // integral_indic // setIT.
have mf4 : measurable_fun setT
    (fun x : measurableTypeR R => ((x : R) ^+ 4 / (2 * kappa) : RR)%:E).
  apply/measurable_EFinP; apply: measurable_funM; last exact: measurable_cst.
  by apply: measurable_funX.
have f40 (x : measurableTypeR R) : setT x ->
    (0 <= ((x : R) ^+ 4 / (2 * kappa) : RR)%:E)%E.
  by move=> _; rewrite lee_fin divr_ge0 ?exprn_even_ge0 // mulr_ge0 // ltW.
have mfI : measurable_fun setT
    (fun x : measurableTypeR R => (kappa / 2 * (\1_A x : RR))%:E).
  by apply/measurable_EFinP; apply: measurable_funM.
have fI0 (x : measurableTypeR R) : setT x ->
    (0 <= (kappa / 2 * (\1_A x : RR))%:E)%E.
  by move=> _; rewrite lee_fin mulr_ge0 // indicE ler0n.
have hg : (\int[mu]_x (g x)%:E =
    (2 * kappa)^-1%:E * \int[mu]_x ((x : R) ^+ 4)%:E +
    (kappa / 2)%:E * mu A)%E.
  rewrite /g.
  under eq_integral do rewrite EFinD.
  by rewrite ge0_integralD // I4 II.
rewrite hg h2 h4 in hle.
have PA : (mu A <= 1)%E by apply: probability_le1.
have PA0 : (0 <= mu A)%E by exact: measure_ge0.
move: hle PA PA0; case: (mu A) => [a| |] //= hle _ _.
rewrite -EFinM -EFinM -EFinD lee_fin in hle.
rewrite lee_fin.
have kn : kappa != 0 by rewrite gt_eqF.
have : (1 <= 1 / 2 + kappa / 2 * a)%R.
  by move: hle; rewrite (_ : ((2 * kappa)^-1 * kappa = 1 / 2)%R) //; field.
by move=> h; rewrite -div1r ler_pdivrMr //; lra.
Qed.

Lemma coordinate_zero :
  (mu [set (0%R : measurableTypeR R)] <= (1 - kappa^-1)%:E)%E.
Proof.
have h := coordinate_nonzero.
pose B := [set x : measurableTypeR R | ((x : R) != 0)%R].
have mB : measurable B.
  have -> : B = ~` [set (0%R : measurableTypeR R)].
    by apply/seteqP; split => x /=; [move=> /eqP|move=> hx; apply/eqP].
  exact: measurableC.
have -> : [set (0%R : measurableTypeR R)] = ~` B.
  apply/seteqP; split => x /=; first by move=> ->; rewrite /B /= eqxx.
  by move=> hx; apply/eqP/negPn/negP.
rewrite probability_setC //.
move: h (probability_le1 mu mB); rewrite -/B.
case: (mu B) => [b| |] //= hb hb1.
by rewrite -EFinB lee_fin; move: hb; rewrite lee_fin => hb; lra.
Qed.

End zero_points.

(* All the points of a sample vanish with probability at most
   (1 - 1 / kappa)^n: the event that the first coordinates x_(i,0) all
   vanish is measurable, these coordinates are independent with law nu 0
   (sample_map_law of Model/Rows), and nu 0 {0} <= 1 - 1 / kappa. *)
Lemma sample_points_zero (kappa K : R) (nu : nat -> probability (measurableTypeR R) R)
    n d : 1 < kappa -> (0 < d)%N ->
  (forall j, (j < d)%N -> universality_coordinate_law kappa K (nu j)) ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (universality_probability nu n d G <= ((1 - kappa^-1) ^+ n)%:E)%E &
    forall x, ~ G x -> exists i : 'I_n, paper_main_point x i != 0].
Proof.
move=> k1 d0 hnu.
pose j0 : 'I_d := Ordinal d0.
pose g (r : d.-tuple (measurableTypeR R)) : measurableTypeR R := tnth r j0.
have mg : measurable_fun setT g := measurable_tnth j0.
have m0 : measurable [set (0%R : measurableTypeR R)] by [].
pose A : set (n.-tuple (measurableTypeR R)) :=
  tuple_box (fun _ : 'I_n => [set (0%R : measurableTypeR R)]).
have mA : measurable A by apply: measurable_tuple_box => i.
have hg B : measurable B -> nu 0%N B = tuple_prod nu d (g @^-1` B).
  move=> mB.
  have -> : g @^-1` B =
      tuple_box (fun j : 'I_d => if j == j0 then B else setT).
    apply/seteqP; split => r /=.
      by move=> hr j; case: ifP => [/eqP -> //|_ //].
    by move=> /(_ j0); rewrite eqxx.
  rewrite tuple_prod_box; first by move=> j; case: ifP.
  rewrite (bigD1 j0) //= big1 ?mule1 //.
  by move=> j /negbTE ->; rewrite probability_setT.
exists ((fun x => tuple_map (fun=> g) (tuple_rows n d x)) @^-1` A); split.
- have mT : measurable_fun setT (fun x : paper_main_sample n d =>
      tuple_map (fun=> g) (tuple_rows n d x)).
    apply: measurableT_comp; last exact: measurable_tuple_rows.
    exact: measurable_tuple_map.
  by rewrite -[X in measurable X]setTI; exact: mT.
- rewrite /universality_probability.
  rewrite (sample_map_law nu n d _ _ (nu 0%N) g A mg hg mA).
  rewrite tuple_prod_box; first by move=> i.
  have h0 := coordinate_zero kappa K (nu 0%N) (hnu 0%N d0) k1.
  have f0 : nu 0%N [set (0%R : measurableTypeR R)] \is a fin_num.
    exact: fin_num_measure.
  have a0 : (0 <= fine (nu 0%N [set (0%R : measurableTypeR R)]))%R.
    by apply: fine_ge0; exact: measure_ge0.
  rewrite -(fineK f0) prodEFin lee_fin.
  have -> : ((1 - kappa^-1) ^+ n = \prod_(i < n) (1 - kappa^-1))%R.
    by rewrite prodr_const card_ord.
  apply: ler_prod => i _; apply/andP; split; first exact: a0.
  by move: h0; rewrite -(fineK f0) lee_fin.
move=> x hx; apply: contrapT => hno; apply: hx => i /=.
have : paper_main_point x i = 0.
  by apply: contrapT => h; apply: hno; exists i; apply/eqP.
move=> /(congr1 (fun v : 'cV[R]_d => v j0 0)).
by rewrite /g tnth_map tnth_ord_tuple paper_main_point_row !mxE.
Qed.

(* 2. The deterministic step: a well-conditioned S whose values <W_i, S>
   are all equal gives a fit of value 1, with lm I <= S / t <= c lm I, as
   soon as some point is not zero. *)

Lemma pm_sqnormE d (v : 'cV[R]_d) : pm_sqnorm d v = mxdot v^T v^T.
Proof.
rewrite /pm_sqnorm /mxdot big_ord1; apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

Lemma sym_paper d (A : 'M[R]_d) : A \is symmetricmx -> paper_main_symmetric A.
Proof. by move=> /symmetricmxP h i j; rewrite -[in LHS]h mxE. Qed.

(* x_i^T S x_i = sqrt d <W_i, S> + tr S. *)
Lemma qf_sample_W N d (x : paper_main_sample N d) (i : 'I_N) (S : 'M[R]_d) :
  (0 < d)%N ->
  paper_main_quadratic_form S (paper_main_point x i) =
  Num.sqrt d%:R * mxdot (sample_W x i) S + \tr S.
Proof.
move=> d0.
have sd : Num.sqrt d%:R != 0 :> RR by rewrite gt_eqF // sqrtr_gt0 ltr0n.
rewrite /sample_W mxdotZl mxdotBl quadratic_form_mxdot.
have -> : mxdot 1%:M S = \tr S by rewrite -trace_mxdot.
by field.
Qed.

(* The quadratic form of a point of pd_slice2 d m M. *)
Lemma slice2_qf d (m M : R) (R0 : 'M[R]_d) (v : 'cV[R]_d) :
  pd_slice2 d m M (mxvec R0) ->
  m * pm_sqnorm d v <= paper_main_quadratic_form R0 v <= M * pm_sqnorm d v.
Proof.
rewrite /pd_slice2 /= mxvecK => [[[_ hlo] [[_ hhi] _]]].
have [->|v0] := eqVneq v 0; first by rewrite pm_qf0 pm_sqnorm0 !mulr0 lexx.
have vT : v^T != 0 by rewrite trmx_eq0.
have := hlo _ vT; have := hhi _ vT.
rewrite !mulmxBr !mul_mx_scalar !mxdotBr !mxdotZr -!quadratic_form_row.
rewrite -!pm_sqnormE subr_gt0 => h2; rewrite subr_gt0 => h1.
by apply/andP; split; apply: ltW.
Qed.

Lemma qf_opnorm d (D : 'M[R]_d) (v : 'cV[R]_d) : D \is symmetricmx ->
  `|paper_main_quadratic_form D v| <= opnorm D * pm_sqnorm d v.
Proof.
move=> Ds.
have := (opnorm_symP Ds (opnorm_ge0 D)).2 (lexx _) v.
rewrite quadratic_form_row pm_sqnormE -[mxdot v v]mxdot_trmx.
suff -> : mxdot v^T (v^T *m D) = mxdot v (D *m v) by [].
have DT : D^T = D by apply/symmetricmxP.
by rewrite -mxdot_trmx trmxK trmx_mul trmxK DT.
Qed.

Lemma sat_fit_det N d (x : paper_main_sample N d) (m M : R)
    (R0 Delta : 'M[R]_d) (c0 : R) :
  (0 < d)%N -> 0 < m -> m < 1 < M ->
  pd_slice2 d m M (mxvec R0) -> Delta \is symmetricmx -> opnorm Delta <= m / 2 ->
  (forall i, mxdot (sample_W x i) (R0 + Delta) = c0) ->
  (exists i : 'I_N, paper_main_point x i != 0) ->
  universality_conditioned_fit_event N d (4 * M / m)%R x.
Proof.
move=> d0 m0 /andP[m1 M1] hR Ds hD hc [i0 hi0].
have R0s : R0 \is symmetricmx.
  move: hR; rewrite /pd_slice2 /= mxvecK => [[[h _] _]].
  apply/symmetricmxP; move/symmetricmxP: h.
  by rewrite raddfB /= tr_scalar_mx => /addIr.
have Ss : R0 + Delta \is symmetricmx.
  have R0T : R0^T = R0 by apply/symmetricmxP.
  have DT : Delta^T = Delta by apply/symmetricmxP.
  by apply/symmetricmxP; rewrite raddfD /= R0T DT.
have hq v : m / 2 * pm_sqnorm d v <= paper_main_quadratic_form (R0 + Delta) v <=
    (M + m / 2) * pm_sqnorm d v.
  rewrite pm_qf_add.
  have /andP[a1 a2] := slice2_qf d m M R0 v hR.
  have := qf_opnorm d Delta v Ds; rewrite ler_norml => /andP[b1 b2].
  have n0 : 0 <= pm_sqnorm d v by exact: pm_sqnorm_ge0.
  have c1 : opnorm Delta * pm_sqnorm d v <= m / 2 * pm_sqnorm d v.
    exact: ler_wpM2r.
  by apply/andP; split; lra.
pose t := Num.sqrt d%:R * c0 + \tr (R0 + Delta).
have ht (i : 'I_N) :
    paper_main_quadratic_form (R0 + Delta) (paper_main_point x i) = t.
  by rewrite qf_sample_W // hc.
have t0 : 0 < t.
  rewrite -(ht i0); have /andP[h _] := hq (paper_main_point x i0).
  apply: lt_le_trans h; apply: mulr_gt0; first by rewrite divr_gt0.
  exact: pm_sqnorm_gt0.
have tn : t != 0 by rewrite gt_eqF.
exists (t^-1 *: (R0 + Delta)), (m / 2 / t); split.
  by rewrite divr_gt0 // divr_gt0.
split.
  apply/uni_loewner_geP; split; first exact: (uni_sym_scale _ _ _ (sym_paper _ _ Ss)).
  move=> v; rewrite uni_qf_scalemx.
  have /andP[h _] := hq v.
  have ti : 0 <= t^-1 by rewrite invr_ge0 ltW.
  apply: le_trans (ler_wpM2l ti h).
  by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
split.
  apply/uni_loewner_leP; split; first exact: (uni_sym_scale _ _ _ (sym_paper _ _ Ss)).
  move=> v; rewrite uni_qf_scalemx.
  have /andP[_ h] := hq v.
  have ti : 0 <= t^-1 by rewrite invr_ge0 ltW.
  apply: le_trans (ler_wpM2l ti h) _.
  have mn : m != 0 by rewrite gt_eqF.
  have -> : 4 * M / m * (m / 2 / t) * pm_sqnorm d v =
      t^-1 * (2 * M * pm_sqnorm d v) by field.
  apply: ler_wpM2l => //; apply: ler_wpM2r; first exact: pm_sqnorm_ge0.
  by lra.
by move=> i; rewrite uni_qf_scalemx ht mulVf.
Qed.

(* 3. (ln d)^5 / sqrt d tends to 0: (ln d)^10 <= 2^10 10! sqrt d, from
   ln_pow10_le of Unsat/Regularized at sqrt d. *)
Lemma ln_pow5_le (d : nat) : (0 < d)%N ->
  ln (d%:R : RR) ^+ 5 / Num.sqrt d%:R <=
  Num.sqrt (2 ^+ 10 * 10`!%:R) / Num.sqrt (Num.sqrt d%:R).
Proof.
move=> d0.
have d1 : 1 <= d%:R :> RR by rewrite ler1n.
have s1 : 1 <= Num.sqrt d%:R :> RR by have := ler_wsqrtr d1; rewrite sqrtr1.
have s0 : 0 < Num.sqrt d%:R :> RR by apply: lt_le_trans s1.
have ss0 : 0 < Num.sqrt (Num.sqrt d%:R) :> RR by rewrite sqrtr_gt0.
have hl : ln (d%:R : RR) = 2 * ln (Num.sqrt d%:R : RR).
  rewrite -[in LHS](sqr_sqrtr (ler0n _ d)) lnXn //.
  by rewrite mulr_natl.
have h10 := ln_pow10_le RR (Num.sqrt d%:R) s1.
have l0 : 0 <= ln (d%:R : RR) := ln_ge0 d1.
have h : ln (d%:R : RR) ^+ 10 <= 2 ^+ 10 * 10`!%:R * Num.sqrt d%:R.
  rewrite hl exprMn -mulrA; apply: ler_wpM2l; first exact: exprn_ge0.
  exact: h10.
have h5 : ln (d%:R : RR) ^+ 5 <=
    Num.sqrt (2 ^+ 10 * 10`!%:R) * Num.sqrt (Num.sqrt d%:R).
  rewrite -sqrtrM ?mulr_ge0 ?exprn_ge0 ?ler0n //.
  rewrite -[X in X <= _](ger0_norm (exprn_ge0 5 l0)) -sqrtr_sqr -exprM.
  by apply: ler_wsqrtr; rewrite mulrC; apply: le_trans h _; rewrite mulrC.
rewrite ler_pdivrMr //.
have hs : Num.sqrt (Num.sqrt d%:R) * Num.sqrt (Num.sqrt d%:R) =
    Num.sqrt d%:R :> RR by rewrite -expr2 sqr_sqrtr // ltW.
have ssn : Num.sqrt (Num.sqrt d%:R) != 0 :> RR by rewrite gt_eqF.
move: h5 hs ssn; move: (Num.sqrt (Num.sqrt d%:R)) => s.
move: (Num.sqrt (2 ^+ 10 * 10`!%:R)) => A h5 hs sn.
rewrite -hs.
have -> : A / s * (s * s) = A * s :> RR by field.
exact: h5.
Qed.

(* 4. One dimension: outside the event of the approximate fit (on the
   features), the event of Theorem 1.9 and the event that every point
   vanishes, the approximate fit corrected by the Delta of Theorem 1.9 is
   a fit of value 1 with condition number at most 4 M / m. *)
Lemma sat_at_d (m M C C1 delta : R) (N d : nat)
    (E1 : set (N.-tuple 'rV[RR]_(d * d))) (E2 G : set (paper_main_sample N d)) :
  (0 < d)%N -> 0 < m -> m < 1 < M -> 0 <= C1 ->
  (forall Z, ~ E1 Z -> exists (theta : 'rV[R]_(d * d)) (b : R), [/\
      pd_slice2 d m M theta,
      \sum_(i < N) (b - mxdot (tnth Z i) theta) ^+ 2 <= delta * N%:R &
      forall i, `|b - mxdot (tnth Z i) theta| <= C * ln (d%:R : RR)]) ->
  (forall x, ~ E2 x -> forall (y : 'rV[R]_N) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y + frobenius y / d%:R)]) ->
  (forall x, ~ G x -> exists i : 'I_N, paper_main_point x i != 0) ->
  C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * (C * ln (d%:R : RR))) <= m / 4 ->
  C1 * (Num.sqrt (delta * N%:R) / d%:R) <= m / 4 ->
  forall x, ~ (unsat_features N d @^-1` E1) x -> ~ E2 x -> ~ G x ->
    universality_conditioned_fit_event N d (4 * M / m)%R x.
Proof.
move=> d0 m0 mM C10 h1 h2 hG s1 s2 x n1 n2 n3.
have [theta [b [hth hsum hres]]] := h1 _ n1.
have hR0 : pd_slice2 d m M (mxvec (vec_mx theta)) by rewrite vec_mxK.
have hW i : mxdot (tnth (unsat_features N d x) i) theta =
    mxdot (sample_W x i) (vec_mx theta).
  by rewrite -mxvec_sample_W -[in LHS](vec_mxK theta) mxdot_mxvec.
pose y : 'rV[R]_N := \row_i (b - mxdot (sample_W x i) (vec_mx theta)).
have hy i : `|y 0 i| <= C * ln (d%:R : RR) by rewrite mxE -hW; exact: hres.
have [Delta [b' [Ds hD hop]]] := h2 x n2 y _ hy.
have hfy : frobenius y <= Num.sqrt (delta * N%:R).
  rewrite /frobenius; apply: ler_wsqrtr.
  apply: le_trans hsum; rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite /mxdot big_ord1; apply: eq_bigr => i _.
  by rewrite !mxE -hW expr2.
have dR : 0 < d%:R :> RR by rewrite ltr0n.
have hop' : opnorm Delta <= m / 2.
  apply: le_trans hop _.
  have h3 : C1 * (frobenius y / d%:R) <= m / 4.
    apply: le_trans s2; apply: ler_wpM2l => //.
    by apply: ler_wpM2r; [rewrite invr_ge0 ltW | exact: hfy].
  rewrite mulrDr.
  move: s1 h3; move: (C1 * _) (C1 * (frobenius y / d%:R)) => u v.
  by lra.
apply: (sat_fit_det N d x m M (vec_mx theta) Delta (b + b')%R d0 m0 mM hR0 Ds
  hop').
  by move=> i; rewrite mxdotDr hD mxE; ring.
exact: hG x n3.
Qed.

(* 5. Theorem 1.2 (i) from Theorem 1.9. *)

(* The two smallness conditions of sat_at_d hold for d large. *)
Lemma sat_small1 (C1 C m : R) (d : nat) :
  (0 < d)%N -> 0 < C1 -> 0 < C -> 0 < m ->
  (4 * C1 * C * Num.sqrt (2 ^+ 10 * 10`!%:R) / m) ^+ 2 <= Num.sqrt d%:R ->
  C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * (C * ln (d%:R : RR))) <= m / 4.
Proof.
move=> d0 C10 C0 m0 hd.
have hl := ln_pow5_le d d0.
have sd0 : 0 < Num.sqrt (d%:R : RR) by rewrite sqrtr_gt0 ltr0n.
have s40 : 0 < Num.sqrt (Num.sqrt (d%:R : RR)) by rewrite sqrtr_gt0.
move: hd hl sd0 s40.
move: (Num.sqrt (2 ^+ 10 * 10`!%:R : RR)) => A.
move: (Num.sqrt (d%:R : RR)) (ln (d%:R : RR)) => sd L hd hl sd0 s40.
have hq : 4 * C1 * C * A / m <= Num.sqrt sd.
  apply: le_trans (ler_norm _) _.
  rewrite -sqrtr_sqr; exact: ler_wsqrtr hd.
apply: le_trans (_ : C1 * C * (A / Num.sqrt sd) <= _).
  have -> : C1 * (L ^+ 4 / sd * (C * L)) = C1 * C * (L ^+ 5 / sd) by ring.
  by apply: ler_wpM2l => //; apply: mulr_ge0; exact: ltW.
rewrite mulrA ler_pdivrMr //.
rewrite ler_pdivrMr // in hq.
lra.
Qed.

Lemma sat_small2 (C1 m alpha : R) (N d : nat) :
  (0 < d)%N -> 0 < C1 -> 0 < m -> 0 < alpha ->
  N%:R <= 2 * alpha * d%:R ^+ 2 ->
  C1 * (Num.sqrt ((m / (4 * C1)) ^+ 2 / (2 * alpha) * N%:R) / d%:R) <= m / 4.
Proof.
move=> d0 C10 m0 a0 hN.
have y0 : 0 < d%:R :> RR by rewrite ltr0n.
have y0' : d%:R != 0 :> RR by rewrite gt_eqF.
have a0' : alpha != 0 by rewrite gt_eqF.
have c0' : C1 != 0 by rewrite gt_eqF.
have c4 : 0 < 4 * C1 by lra.
have a2 : 0 < 2 * alpha by lra.
have q0 : 0 < m / (4 * C1) by apply: divr_gt0.
have h1 : (m / (4 * C1)) ^+ 2 / (2 * alpha) * N%:R <=
    (m / (4 * C1) * d%:R) ^+ 2.
  apply: le_trans (_ : (m / (4 * C1)) ^+ 2 / (2 * alpha) *
    (2 * alpha * d%:R ^+ 2) <= _).
    apply: ler_wpM2l => //; apply: divr_ge0; [exact: sqr_ge0 | exact: ltW].
  have -> : (m / (4 * C1)) ^+ 2 / (2 * alpha) * (2 * alpha * d%:R ^+ 2) =
    (m / (4 * C1) * d%:R) ^+ 2 by field.
  exact: lexx.
have h2 : Num.sqrt ((m / (4 * C1)) ^+ 2 / (2 * alpha) * N%:R) <=
    m / (4 * C1) * d%:R.
  apply: le_trans (ler_wsqrtr h1) _.
  have qy0 : 0 <= m / (4 * C1) * d%:R by apply: mulr_ge0; exact: ltW.
  rewrite sqrtr_sqr (ger0_norm qy0); exact: lexx.
apply: le_trans (_ : C1 * (m / (4 * C1) * d%:R / d%:R) <= _).
  apply: ler_wpM2l; first exact: ltW.
  by apply: ler_wpM2r => //; rewrite invr_ge0 ler0n.
have -> : C1 * (m / (4 * C1) * d%:R / d%:R) = m / 4 by field.
exact: lexx.
Qed.

(* Arithmetic for the choice of d. *)
Lemma sat_ratio_lt1 (kappa : R) : 1 < kappa -> `|1 - kappa^-1| < 1.
Proof.
move=> k1.
have k0 : 0 < kappa by apply: lt_trans k1.
have ki : kappa^-1 < 1 by rewrite invf_lt1.
have ki0 : 0 < kappa^-1 by rewrite invr_gt0.
by rewrite ger0_norm; lra.
Qed.

Lemma sat_count_ge (alpha : R) (N0 N d : nat) : (0 < d)%N -> 0 < alpha ->
  2 * N0%:R / alpha <= d%:R -> alpha / 2 * d%:R ^+ 2 <= N%:R -> (N0 <= N)%N.
Proof.
move=> d0 a0 hq hN.
rewrite -(@ler_nat RR); apply: le_trans hN.
rewrite ler_pdivrMr // in hq.
have hdd : d%:R <= d%:R ^+ 2 :> RR.
  by rewrite expr2 ler_peMl // ?ler0n // ler1n.
nra.
Qed.

Lemma sat_expr_small (q e : R) : `|q| < 1 -> 0 < e ->
  exists N0 : nat, forall N, (N0 <= N)%N -> `|q ^+ N| < e.
Proof.
move=> q1 e0.
have hm := proj1 (@cvgrPdist_lt R R^o nat \oo _ (fun N => q ^+ N) 0)
  (@cvg_expr _ q q1).
have [N0 _ hN0] := hm ltac:(typeclasses eauto) e e0.
exists N0 => N hN.
by have := hN0 N hN; rewrite /= sub0r normrN.
Qed.

Lemma sat_quarters (e : R) : 0 <= e -> e / 4 + e / 4 + e / 4 <= e.
Proof. by move=> e0; lra. Qed.

Lemma sat_half (e : R) : 0 < e -> e / 2 < e.
Proof. by move=> e0; lra. Qed.

(* An event whose complement is in an event of probability at most e has
   probability within e of 1. *)
Lemma prob_close_one dT (T : measurableType dT) (P : probability T RR)
    (A B : set T) (e : RR) :
  measurable A -> measurable B -> ~` A `<=` B -> (P B <= e%:E)%E ->
  (`|P A - 1%:E| <= e%:E)%E.
Proof.
move=> mA mB AB PB.
have hC : (P (~` A) <= e%:E)%E.
  apply: le_trans PB; apply: le_measure; last exact: AB.
  - by rewrite inE; exact: measurableC.
  - by rewrite inE.
rewrite -(setCK A) probability_setC; first exact: measurableC.
have hp0 : (0 <= P (~` A))%E by exact: measure_ge0.
move: hC hp0; case: (P (~` A)) => [p| |] //= hp hp0.
have -> : (1 - p - 1 = - p)%R by ring.
by rewrite normrN ger0_norm // -lee_fin.
Qed.

(* A conditioned fit is a positive definite fit. *)
Lemma cond_sub_pd N d (c : R) :
  universality_conditioned_fit_event N d c `<=` universality_pd_fit_event N d.
Proof.
move=> x [S [lm [lm0 [hlo [_ hfit]]]]].
have [Ss Slo] := (uni_loewner_geP d lm S).1 hlo.
exists S; split => //; split => // v v0.
apply: lt_le_trans (Slo v).
by apply: mulr_gt0 => //; exact: pm_sqnorm_gt0.
Qed.

(* Theorem 1.2 (i) from Theorem 1.9. *)
Theorem universality_sat_of_interpolation (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  small_residual_interpolation kappa K alpha ->
  exists c : R, 1 <= c /\
  (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
  (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
  (forall nu : nat -> nat -> probability (measurableTypeR R) R,
    (forall d j : nat, (j < d)%nat -> universality_coordinate_law kappa K (nu d j)) ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d
                    (universality_pd_fit_event (n d) d)) 1 /\
      paper_main_tends_to
        (fun d => universality_probability (nu d) (n d) d
                    (universality_conditioned_fit_event (n d) d c)) 1).
Proof.
move=> k1 K0 a0 aast [C1 [C10 hI]].
have [m [M [C [m0 m1 M1 C0 hAF]]]] := approximate_fit kappa K alpha k1 K0 a0 aast.
have mM : m < 1 < M by rewrite m1 M1.
exists (4 * M / m)%R; split.
  by rewrite ler_pdivlMr // mul1r; lra.
split; first by move=> n d; exact: measurable_pd_fit_event.
split; first by move=> n d; exact: measurable_conditioned_fit_event.
move=> nu hnu n hn.
(* for every eps > 0 and d large, a measurable event of probability at
   most eps that contains the complement of the conditioned fit *)
have key (eps : RR) : 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    exists B : set (paper_main_sample (n d) d), [/\ measurable B,
      (universality_probability (nu d) (n d) d B <= eps%:E)%E &
      ~` universality_conditioned_fit_event (n d) d (4 * M / m)%R `<=` B].
  move=> e0.
  have e4 : 0 < eps / 4 by rewrite divr_gt0.
  have [delta dl0 hs2] : exists2 delta : RR, 0 < delta &
      forall N d, (0 < d)%N -> N%:R <= 2 * alpha * d%:R ^+ 2 ->
        C1 * (Num.sqrt (delta * N%:R) / d%:R) <= m / 4.
    exists ((m / (4 * C1)) ^+ 2 / (2 * alpha)).
      apply: divr_gt0.
        by apply: exprn_gt0; apply: divr_gt0 => //; apply: mulr_gt0; rewrite ?ltr0n.
      by apply: mulr_gt0; rewrite ?ltr0n.
    move=> N d d0 hN; exact: (sat_small2 C1 m alpha N d d0 C10 m0 a0 hN).
  have [D1 hD1] := hAF nu hnu n hn delta (eps / 4)%R dl0 e4.
  have [D2 hD2] := hI nu hnu n hn (eps / 4)%R e4.
  have [N0 hN0] :=
    sat_expr_small (1 - kappa^-1)%R (eps / 4)%R (sat_ratio_lt1 kappa k1) e4.
  have [Dn hDn] := af_ev_density n alpha a0 hn.
  have [Dq hDq] := af_ev_ge (2 * N0%:R / alpha).
  have [Dl hDl] : af_eventually (fun d => (0 < d)%N ->
      C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * (C * ln (d%:R : RR))) <= m / 4).
    apply: (af_ev_mono _ _ _ (af_ev_sqrt
      ((4 * C1 * C * Num.sqrt (2 ^+ 10 * 10`!%:R) / m) ^+ 2))) => d hd d0.
    exact: (sat_small1 C1 C m d d0 C10 C0 m0 hd).
  exists (maxn (maxn D1 D2) (maxn (maxn Dn Dq) Dl)) => d.
  rewrite !geq_max => /andP[/andP[d1 d2] /andP[/andP[dn dq] dl]].
  have [d0 [nlo nhi]] := hDn d dn.
  have dR : 0 < d%:R :> RR by rewrite ltr0n.
  have [E1 [mE1 PE1 hE1]] := hD1 d d1.
  have [E2 [mE2 PE2 hE2]] := hD2 d d2.
  have [G [mG PG hG]] :=
    sample_points_zero kappa K (nu d) (n d) d k1 d0 (fun j jd => hnu d j jd).
  have nN0 := sat_count_ge alpha N0 (n d) d d0 a0 (hDq d dq) nlo.
  have PG' : (universality_probability (nu d) (n d) d G <= (eps / 4)%:E)%E.
    apply: le_trans PG _; rewrite lee_fin.
    exact: le_trans (ler_norm _) (ltW (hN0 _ nN0)).
  have [F1 [mF1 PF1 hF1]] : exists F1 : set (paper_main_sample (n d) d),
      [/\ measurable F1,
        (universality_probability (nu d) (n d) d F1 <= (eps / 4)%:E)%E &
        unsat_features (n d) d @^-1` E1 `<=` F1].
    exists (unsat_features (n d) d @^-1` E1); split => //.
      by rewrite -[X in measurable X]setTI; exact: measurable_unsat_features.
    by rewrite /universality_probability sample_features_law.
  exists (F1 `|` E2 `|` G); split.
  - by apply: measurableU => //; exact: measurableU.
  - apply: le_trans (measureU2 _ (measurableU _ _ mF1 mE2) mG) _.
    apply: le_trans (leeD (measureU2 _ mF1 mE2) (lexx _)) _.
    apply: le_trans (leeD (leeD PF1 PE2) PG') _.
    by rewrite -!EFinD lee_fin; exact: sat_quarters (ltW e0).
  move=> x hx; apply: contrapT => hno; apply: hx.
  apply: (sat_at_d m M C C1 delta (n d) d E1 E2 G d0 m0 mM (ltW C10) hE1 hE2 hG
    (hDl d dl d0) (hs2 (n d) d d0 nhi) x) => h; apply: hno.
  - by left; left; exact: hF1.
  - by left; right.
  - by right.
suff hlim (A : forall d, set (paper_main_sample (n d) d)) :
    (forall d, measurable (A d)) ->
    (forall d, universality_conditioned_fit_event (n d) d (4 * M / m)%R `<=` A d) ->
    paper_main_tends_to (fun d => universality_probability (nu d) (n d) d (A d)) 1.
  split; apply: hlim => d.
  - exact: measurable_pd_fit_event.
  - exact: cond_sub_pd.
  - exact: measurable_conditioned_fit_event.
  - by [].
move=> mA hA eps e0.
have e2 : 0 < eps / 2 by rewrite divr_gt0.
have [D hD] := key (eps / 2) e2.
exists D => d dD.
have [B [mB PB hB]] := hD d dD.
have AB : ~` A d `<=` B.
  by move=> x hx; apply: hB => hc; apply: hx; exact: hA.
have h := prob_close_one _ _ (universality_sample_law (nu d) (n d) d) (A d) B
  (eps / 2) (mA d) mB AB PB.
rewrite /universality_probability; apply: le_lt_trans h _.
by rewrite lte_fin; exact: sat_half.
Qed.

(* 6. Theorem 1.2, both parts, from Theorem 1.9. *)
Theorem universality_statement_of_interpolation :
  (forall kappa K alpha : R, 1 < kappa -> 0 < K -> 0 < alpha ->
    alpha < universality_alpha_star kappa ->
    small_residual_interpolation kappa K alpha) ->
  universality_statement.
Proof.
move=> hI kappa K alpha k1 K0 a0; split => ha.
  exact: (universality_sat_of_interpolation kappa K alpha k1 K0 a0 ha
    (hI kappa K alpha k1 K0 a0 ha)).
exact: (universality_unsat kappa K alpha k1 a0 ha).
Qed.
