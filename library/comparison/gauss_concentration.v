From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences derive.
From mathcomp Require Import realfun exp trigo measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.gaussian Require Import partial_derivative.
From GaussianAnalysis.comparison Require Import normal_mgf gauss_rotation.
From GaussianAnalysis.comparison Require Import gauss_smoothing.

(**md**************************************************************************)
(* # Gaussian concentration for Lipschitz functions                           *)
(*                                                                            *)
(* Let x have law gauss n and let F : 'rV[R]_n -> R be L-Lipschitz for the    *)
(* Euclidean norm: |F x - F y| <= L |x - y|. Then E[expR (t (F x - E[F]))] <= *)
(* expR (t^2 L^2 / 2) for every real t (gauss_concentration), with the sharp  *)
(* constant of Tsirelson, Ibragimov and Sudakov. For u >= 0, P(F x >= E[F] +  *)
(* u) and P(F x <= E[F] - u) are at most expR (- u^2 / (2 L^2))               *)
(* (gauss_concentration_upper_tail, gauss_concentration_lower_tail), and P(|F *)
(* x - E[F]| >= u) is at most twice that (gauss_concentration_abs_tail).      *)
(*                                                                            *)
(* The proof follows Herbst. Let F be bounded, of class C^1, with gradient of *)
(* Euclidean norm at most L, and let t >= 0. Let y be an independent copy of  *)
(* x and phi th = E[F x expR (t F (cos th x + sin th y))]. After the rotation *)
(* of (x, y) by th, Gaussian integration by parts in y (gauss2_ibp_snd) shows *)
(* that the derivative of phi is at least - sin th t L^2 E[expR (t F)].       *)
(* Comparing phi 0 and phi (pi / 2) gives the covariance inequality E[F expR  *)
(* (t F)] <= (E[F] + t L^2) E[expR (t F)] (gauss_herbst_ineq), and            *)
(* integrating the resulting differential inequality for t |-> E[expR (t F)]  *)
(* gives the bound for such F (gauss_concentration_smooth). A general         *)
(* Lipschitz F is the pointwise limit of Gaussian smoothings                  *)
(* (gauss_smoothing.v) of F clipped to [-(k + 1), k + 1] (clip), and Fatou's  *)
(* lemma concludes.                                                           *)
(*                                                                            *)
(* The file also proves facts on the law gauss n \x gauss n of two            *)
(* independent standard Gaussian vectors: its marginals (integral_gauss2_fst, *)
(* integral_gauss2_snd), the independence of its components                   *)
(* (integral_gauss2_prod) and integration by parts in the second component    *)
(* (gauss2_ibp_snd).                                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*   clip k x == the point of [-k, k] closest to x                            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section prob_bounded.
Context d (T : measurableType d) (R : realType) (mu : probability T R).

Lemma integrable_prob_bounded (f : T -> R) (C : R) :
  measurable_fun [set: T] f -> (forall x, `|f x| <= C) ->
  mu.-integrable [set: T] (EFin \o f).
Proof.
move=> mf fC.
apply: (le_integrable measurableT _ _ (finite_measure_integrable_cst mu C measurableT)).
  exact/measurable_EFinP.
by move=> x _; rewrite /comp lee_fin (le_trans (fC x))// ler_norm.
Qed.

End prob_bounded.

Section gauss2.
Context {R : realType} {n : nat}.
Local Notation P := (gauss n \x gauss n)%E.

Lemma integrable_gauss2_fst (g : 'rV[R]_n -> R) :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o g) ->
  P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (fun p => (g p.1)%:E).
Proof.
move=> gi.
have mg : measurable_fun [set: 'rV[R]_n] g.
  by apply/measurable_EFinP; exact: measurable_int gi.
have mg1 : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => (g p.1)%:E).
  by apply/measurable_EFinP; apply: measurableT_comp => //; exact: measurable_fst.
have ma : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => `|(g p.1)%:E|%E).
  exact: measurableT_comp.
apply/integrableP; split => //.
rewrite (@fubini_tonelli1 _ _ _ _ R (gauss n) (gauss n) _ ma (fun p => abse_ge0 _)).
rewrite /fubini_F /=.
under eq_integral do rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
by case/integrableP: gi.
Qed.

Lemma integrable_gauss2_snd (g : 'rV[R]_n -> R) :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o g) ->
  P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (fun p => (g p.2)%:E).
Proof.
move=> gi.
have mg : measurable_fun [set: 'rV[R]_n] g.
  by apply/measurable_EFinP; exact: measurable_int gi.
have mg2 : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => (g p.2)%:E).
  by apply/measurable_EFinP; apply: measurableT_comp => //; exact: measurable_snd.
have ma : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => `|(g p.2)%:E|%E).
  exact: measurableT_comp.
apply/integrableP; split => //.
rewrite (@fubini_tonelli1 _ _ _ _ R (gauss n) (gauss n) _ ma (fun p => abse_ge0 _)).
rewrite /fubini_F /=; case/integrableP: gi => _ gi.
by rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
Qed.

Lemma integral_gauss2_fst (g : 'rV[R]_n -> R) :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o g) ->
  (\int[P]_p (g p.1)%:E = \int[gauss n]_x (g x)%:E)%E.
Proof.
move=> gi; rewrite -(integral12_prod_meas1 (integrable_gauss2_fst gi)) /=.
apply: eq_integral => x _; rewrite /fubini_F /= integral_cst//.
by rewrite [X in (_ * X)%E]probability_setT mule1.
Qed.

Lemma integral_gauss2_snd (g : 'rV[R]_n -> R) :
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o g) ->
  (\int[P]_p (g p.2)%:E = \int[gauss n]_x (g x)%:E)%E.
Proof.
move=> gi; rewrite -(integral12_prod_meas1 (integrable_gauss2_snd gi)) /=.
by rewrite /fubini_F /= integral_cst// [X in (_ * X)%E]probability_setT mule1.
Qed.

(* The two components of a vector of law gauss n \x gauss n are
   independent. *)
Lemma integral_gauss2_prod (f g : 'rV[R]_n -> R) (C : R) :
    measurable_fun [set: 'rV[R]_n] f -> measurable_fun [set: 'rV[R]_n] g ->
    (forall x, `|f x| <= C) -> (forall x, `|g x| <= C) ->
  (\int[P]_p (f p.1 * g p.2)%:E =
   \int[gauss n]_x (f x)%:E * \int[gauss n]_y (g y)%:E)%E.
Proof.
move=> mf mg fC gC.
have fi := integrable_prob_bounded (gauss n) mf fC.
have gi := integrable_prob_bounded (gauss n) mg gC.
have mfg : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => f p.1 * g p.2).
  apply: measurable_funM.
    by apply: measurableT_comp => //; exact: measurable_fst.
  by apply: measurableT_comp => //; exact: measurable_snd.
have fgi : P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (EFin \o (fun p => f p.1 * g p.2)).
  apply: (integrable_prob_bounded P (C := C * C) mfg) => p.
  by rewrite normrM ler_pM.
have gE : (\int[gauss n]_y (g y)%:E = (\int[gauss n]_y g y)%:E)%E.
  by rewrite /Rintegral fineK//; exact: integrable_fin_num.
rewrite -(integral12_prod_meas1 fgi) /= gE -integralZr//.
apply: eq_integral => x _; rewrite /fubini_F /=.
under eq_integral do rewrite EFinM.
by rewrite integralZl// gE.
Qed.

(* Gaussian integration by parts in the second component. *)
Lemma gauss2_ibp_snd (j : 'I_n) (H dH : 'rV[R]_n * 'rV[R]_n -> R) (C : R) :
    measurable_fun [set: 'rV[R]_n * 'rV[R]_n] H ->
    measurable_fun [set: 'rV[R]_n * 'rV[R]_n] dH ->
    (forall x v, is_derive v (delta_mx 0 j) (fun v => H (x, v)) (dH (x, v))) ->
    (forall x, continuous (fun v => H (x, v))) ->
    (forall x, continuous (fun v => dH (x, v))) ->
    (forall p, `|H p| <= C) -> (forall p, `|dH p| <= C) ->
  (\int[P]_p (p.2 0 j * H p)%:E = \int[P]_p (dH p)%:E)%E.
Proof.
move=> mH mdH Hd cH cdH HC dHC.
have C0 : 0 <= C := le_trans (normr_ge0 _) (HC (0, 0)).
have mvH : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => p.2 0 j * H p).
  apply: measurable_funM => //.
  exact: (measurableT_comp (measurable_mxentry 0 j) measurable_snd).
have iA : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun v : 'rV[R]_n => `|v|)).
  apply: (integrable_gauss_poly (C := 1) (k := 1)) => [|v].
    by apply: continuous_measurable_mx; exact: norm_continuous.
  by rewrite normr_id mul1r expr1 lerDr.
have iA2 := integrableZl measurableT C (integrable_gauss2_snd iA).
have vHi : P.-integrable [set: 'rV[R]_n * 'rV[R]_n]
    (EFin \o (fun p : 'rV[R]_n * 'rV[R]_n => p.2 0 j * H p)).
  apply: (le_integrable measurableT _ _ iA2); first exact/measurable_EFinP.
  move=> p _; rewrite /comp -EFinM lee_fin.
  rewrite [leRHS]ger0_norm ?mulr_ge0// normrM mulrC ler_pM//.
  exact: mx_norm_entry_le.
have dHi : P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (EFin \o dH).
  exact: integrable_prob_bounded dHC.
rewrite -(integral12_prod_meas1 vHi) -(integral12_prod_meas1 dHi).
apply: eq_integral => x _; rewrite /fubini_F /=.
apply: (gauss_ibp (C := C) (k := 0)) => //.
  by move=> v; rewrite expr0 (le_trans (HC _))// ler_peMr// lerDr.
by move=> v; rewrite expr0 (le_trans (dHC _))// ler_peMr// lerDr.
Qed.

End gauss2.

(* F is bounded by K, of class C^1 with partial derivatives DF j, and its
   gradient has Euclidean norm at most L. *)
Section gauss_herbst.
Context {R : realType} {n : nat}.
Variables (F : 'rV[R]_n -> R) (DF : 'I_n -> 'rV[R]_n -> R) (K L : R).
Hypothesis dF : forall j x, is_derive x (delta_mx 0 j) F (DF j x).
Hypothesis cDF : forall j, continuous (DF j).
Hypothesis FK : forall x, `|F x| <= K.
Hypothesis gradL : forall x, mxdot (\row_j DF j x) (\row_j DF j x) <= L ^+ 2.
Local Notation P := (gauss n \x gauss n)%E.

Local Lemma herbst_Fdiff x : differentiable (F : 'rV[R]_n -> R^o) x.
Proof. exact: differentiable_partials dF cDF x. Qed.

Local Lemma herbst_cF : continuous F.
Proof. by move=> x; exact: differentiable_continuous (herbst_Fdiff x). Qed.

Local Lemma herbst_mF : measurable_fun [set: 'rV[R]_n] F.
Proof. exact: (continuous_measurable_mx herbst_cF). Qed.

Local Lemma herbst_mDF j : measurable_fun [set: 'rV[R]_n] (DF j).
Proof. by apply: continuous_measurable_mx => x; exact: cDF. Qed.

Local Lemma herbst_K0 : 0 <= K.
Proof. exact: le_trans (normr_ge0 _) (FK 0). Qed.

Local Lemma herbst_DFL j x : `|DF j x| <= `|L|.
Proof.
have h := le_trans (mxdot_entry (\row_j DF j x) 0 j) (gradL x).
rewrite mxE in h.
by rewrite -(@ler_pXn2r _ 2) ?nnegrE// !real_normK ?num_real.
Qed.

Local Lemma herbst_DFdot x y : \sum_j DF j x * DF j y <= L ^+ 2.
Proof.
have fr z : frobenius (\row_j DF j z) <= `|L|.
  by rewrite /frobenius -sqrtr_sqr ler_sqrt// sqr_ge0.
have h := ler_mxdot (\row_j DF j x) (\row_j DF j y).
have -> : \sum_j DF j x * DF j y = mxdot (\row_j DF j x) (\row_j DF j y).
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE.
rewrite (le_trans h)// -real_normK ?num_real// expr2.
by rewrite ler_pM// frobenius_ge0.
Qed.

(* The interpolation between x and y along a quarter circle, and its
   derivative. *)
Local Definition herbst_z (th : R) (p : 'rV[R]_n * 'rV[R]_n) : 'rV[R]_n :=
  cos th *: p.1 + sin th *: p.2.
Local Definition herbst_dz (th : R) (p : 'rV[R]_n * 'rV[R]_n) : 'rV[R]_n :=
  - sin th *: p.1 + cos th *: p.2.

Local Lemma herbst_is_derive_z (th : R) p : is_derive th 1 (herbst_z ^~ p) (herbst_dz th p).
Proof.
exact: (is_deriveD (is_derive_scalel _ (is_derive_cos th))
  (is_derive_scalel _ (is_derive_sin th))).
Qed.

Local Lemma herbst_is_derive_Fz (th : R) p :
  is_derive th 1 (fun th => F (herbst_z th p))
    (\sum_j herbst_dz th p 0 j * DF j (herbst_z th p)).
Proof.
have h := is_derive_rV_comp (herbst_Fdiff (herbst_z th p)) (herbst_is_derive_z th p).
apply: (is_derive_eq h); apply: eq_bigr => j _.
by have hj := dF j (herbst_z th p); rewrite derive_val.
Qed.

Local Lemma herbst_mz (th : R) :
  measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (herbst_z th).
Proof.
apply: measurable_addmx.
  by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_fst].
by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_snd].
Qed.

Local Lemma herbst_mdz (th : R) :
  measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (herbst_dz th).
Proof.
apply: measurable_addmx.
  by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_fst].
by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_snd].
Qed.

Local Lemma herbst_dz_bound (th : R) p j : `|herbst_dz th p 0 j| <= `|p.1| + `|p.2|.
Proof.
have s1 : `|sin th| <= 1 by rewrite ler_norml sin_le1 sin_geN1.
have c1 : `|cos th| <= 1 by rewrite ler_norml cos_le1 cos_geN1.
rewrite /herbst_dz !mxE (le_trans (ler_normD _ _))// lerD//.
  rewrite normrM normrN -[`|p.1|]mul1r ler_pM//.
  exact: mx_norm_entry_le.
rewrite normrM -[`|p.2|]mul1r ler_pM//.
exact: mx_norm_entry_le.
Qed.

Local Lemma continuous_affine_rV (c s : R) (x : 'rV[R]_n) :
  continuous (fun v : 'rV[R]_n => c *: x - s *: v).
Proof.
move=> v; apply: (@continuousB _ _ _ (cst (c *: x)) (fun v : 'rV[R]_n => s *: v)).
  exact: cst_continuous.
by apply: (@continuousZ _ _ _ (cst s) id); first exact: cst_continuous.
Qed.

Local Lemma measurable_affine2 (c s : R) :
  measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => c *: p.1 - s *: p.2).
Proof.
apply: measurable_addmx.
  by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_fst].
apply: measurable_oppmx.
by apply: measurable_scalemx; [exact: measurable_cst|exact: measurable_snd].
Qed.

Local Lemma herbst_is_derive_Fr (c s : R) (x v : 'rV[R]_n) j :
  is_derive v (delta_mx 0 j) (fun v => F (c *: x - s *: v))
    (- s * DF j (c *: x - s *: v)).
Proof.
set w := c *: x - s *: v.
have Fd := herbst_Fdiff w.
have dw : is_derive w (- s *: delta_mx 0 j) F (- s * DF j w).
  apply: DeriveDef; first exact: diff_derivable.
  rewrite deriveE// linearZ /= -deriveE//.
  by have h := dF j w; rewrite derive_val.
apply: (is_derive_transfer (G := F) (b := w) (w := - s *: delta_mx 0 j)) => // h.
by congr F; apply/rowP => k; rewrite /w !mxE; ring.
Qed.

Section herbst_t.
Variable t : R.
Hypothesis t0 : 0 <= t.

Local Definition herbst_f (th : R) (p : 'rV[R]_n * 'rV[R]_n) : R :=
  F p.1 * expR (t * F (herbst_z th p)).

Local Definition herbst_df (th : R) (p : 'rV[R]_n * 'rV[R]_n) : R :=
  F p.1 * (expR (t * F (herbst_z th p)) *
    (t * \sum_j herbst_dz th p 0 j * DF j (herbst_z th p))).

Local Lemma herbst_is_derive_f (th : R) p : is_derive th 1 (herbst_f ^~ p) (herbst_df th p).
Proof.
have h := is_deriveZ (F p.1) (@is_derive1_comp R expR
  (fun th => t * F (herbst_z th p)) th _ _ (is_derive_expR _)
  (is_deriveZ t (herbst_is_derive_Fz th p))).
by apply: (is_derive_eq h); rewrite /GRing.scale.
Qed.

Local Lemma herbst_mf (th : R) : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (herbst_f th).
Proof.
apply: measurable_funM; first exact: measurableT_comp herbst_mF measurable_fst.
apply: measurableT_comp => //; apply: measurable_funM => //.
exact: measurableT_comp herbst_mF (herbst_mz th).
Qed.

Local Lemma herbst_mdf (th : R) : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (herbst_df th).
Proof.
apply: measurable_funM; first exact: measurableT_comp herbst_mF measurable_fst.
apply: measurable_funM.
  apply: measurableT_comp => //; apply: measurable_funM => //.
  exact: measurableT_comp herbst_mF (herbst_mz th).
apply: measurable_funM => //; apply: measurable_sum => j.
apply: measurable_funM.
  exact: measurableT_comp (measurable_mxentry 0 j) (herbst_mdz th).
exact: measurableT_comp (herbst_mDF j) (herbst_mz th).
Qed.

Local Lemma herbst_expR_le (x : 'rV[R]_n) : expR (t * F x) <= expR (t * K).
Proof. by rewrite ler_expR ler_wpM2l// (le_trans (ler_norm _))// FK. Qed.

Local Lemma herbst_f_bound (th : R) p : `|herbst_f th p| <= K * expR (t * K).
Proof.
rewrite /herbst_f normrM (ger0_norm (expR_ge0 _)).
by apply: ler_pM => //; exact: herbst_expR_le.
Qed.

Local Lemma herbst_df_bound (th : R) p :
  `|herbst_df th p| <= K * expR (t * K) * (t * (n%:R * `|L|)) * (`|p.1| + `|p.2|).
Proof.
have hs : `|\sum_j herbst_dz th p 0 j * DF j (herbst_z th p)| <=
    n%:R * `|L| * (`|p.1| + `|p.2|).
  apply: (le_trans (ler_norm_sum _ _ _)).
  apply: (@le_trans _ _ (\sum_(j < n) (`|p.1| + `|p.2|) * `|L|)).
    apply: ler_sum => j _; rewrite normrM ler_pM//.
      exact: herbst_dz_bound.
    exact: herbst_DFL.
  rewrite sumr_const card_ord -[X in X <= _]mulr_natl [_ * `|L|]mulrC mulrA.
  by [].
rewrite /herbst_df !normrM (ger0_norm (expR_ge0 _)) (ger0_norm t0).
have hK := herbst_K0.
apply: (@le_trans _ _
    (K * (expR (t * K) * (t * (n%:R * `|L| * (`|p.1| + `|p.2|)))))).
  apply: ler_pM => //; first by rewrite !mulr_ge0// expR_ge0.
  apply: ler_pM => //; first by rewrite mulr_ge0.
    exact: herbst_expR_le.
  by rewrite ler_wpM2l.
by rewrite !mulrA.
Qed.

Local Definition herbst_D (p : 'rV[R]_n * 'rV[R]_n) : R :=
  K * expR (t * K) * (t * (n%:R * `|L|)) * (`|p.1| + `|p.2|).

Local Lemma herbst_D_ge0 p : 0 <= herbst_D p.
Proof. by rewrite /herbst_D !mulr_ge0 ?expR_ge0 ?addr_ge0// herbst_K0. Qed.

Local Lemma integrable_herbst_D :
  P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (EFin \o herbst_D).
Proof.
have iA : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun v : 'rV[R]_n => `|v|)).
  apply: (integrable_gauss_poly (C := 1) (k := 1)) => [|v].
    by apply: continuous_measurable_mx; exact: norm_continuous.
  by rewrite normr_id mul1r expr1 lerDr.
have := integrableZl measurableT (K * expR (t * K) * (t * (n%:R * `|L|)))
  (integrableD measurableT (integrable_gauss2_fst iA) (integrable_gauss2_snd iA)).
by apply: eq_integrable => // p _; rewrite /herbst_D /= -EFinD -EFinM.
Qed.

Local Lemma integrable_herbst_df (th : R) :
  P.-integrable [set: 'rV[R]_n * 'rV[R]_n] (EFin \o herbst_df th).
Proof.
apply: (le_integrable measurableT _ _ integrable_herbst_D).
  by apply/measurable_EFinP; exact: herbst_mdf.
move=> p _; rewrite /comp lee_fin (ger0_norm (herbst_D_ge0 p)).
exact: herbst_df_bound.
Qed.

Local Lemma herbst_phi_derive (th : R) : th \in `]-1, 2[ ->
  is_derive th 1 (fun th => \int[P]_p herbst_f th p) (\int[P]_p herbst_df th p).
Proof.
move=> thI; apply: (is_derive_Rintegral thI _ _ herbst_D_ge0 integrable_herbst_D).
- by move=> x _; exact: integrable_prob_bounded (herbst_mf x) (herbst_f_bound x).
- by move=> x p _; exact: herbst_is_derive_f.
- move=> x p _; rewrite (le_trans (herbst_df_bound x p))//.
Qed.

Local Definition herbst_k (j : 'I_n) (x : 'rV[R]_n) : R := t * expR (t * F x) * DF j x.

Local Lemma herbst_k_bound j x : `|herbst_k j x| <= t * expR (t * K) * `|L|.
Proof.
rewrite /herbst_k !normrM (ger0_norm t0) (ger0_norm (expR_ge0 _)).
rewrite ler_pM ?mulr_ge0 ?expR_ge0//; last exact: herbst_DFL.
by rewrite ler_wpM2l// herbst_expR_le.
Qed.

Local Lemma herbst_mk j : measurable_fun [set: 'rV[R]_n] (herbst_k j).
Proof.
apply: measurable_funM; last exact: herbst_mDF.
apply: measurable_funM => //; apply: measurableT_comp => //.
by apply: measurable_funM => //; exact: herbst_mF.
Qed.

(* Gaussian integration by parts in the second component, for the test
   functions of the rotated covariance identity. *)
Local Lemma herbst_ibp (c s : R) j :
  \int[P]_p (p.2 0 j * (herbst_k j p.1 * F (c *: p.1 - s *: p.2))) =
  \int[P]_p (herbst_k j p.1 * (- s * DF j (c *: p.1 - s *: p.2))).
Proof.
have mA := measurable_affine2 c s.
have kb := herbst_k_bound j.
have tL0 : 0 <= t * expR (t * K) * `|L| by rewrite !mulr_ge0// expR_ge0.
have K0 := herbst_K0.
rewrite /Rintegral; congr fine.
apply: (gauss2_ibp_snd (C := t * expR (t * K) * `|L| * (K + `|s| * `|L|))).
- apply: measurable_funM; first exact: measurableT_comp (herbst_mk j) measurable_fst.
  exact: measurableT_comp herbst_mF mA.
- apply: measurable_funM; first exact: measurableT_comp (herbst_mk j) measurable_fst.
  by apply: measurable_funM => //; exact: measurableT_comp (herbst_mDF j) mA.
- by move=> x v /=; exact: (is_deriveZ (herbst_k j x) (herbst_is_derive_Fr c s x v j)).
- move=> x v /=; apply: (cvgM (cvg_cst _)); [apply: nbhs_filter|apply: nbhs_filter|].
  by apply: continuous_comp; [exact: continuous_affine_rV|exact: herbst_cF].
- move=> x v /=; apply: (cvgM (cvg_cst _)); [apply: nbhs_filter|apply: nbhs_filter|].
  apply: (cvgM (cvg_cst _)); [apply: nbhs_filter|apply: nbhs_filter|].
  by apply: continuous_comp; [exact: continuous_affine_rV|exact: cDF].
- move=> p; rewrite normrM ler_pM//.
  by rewrite (le_trans (FK _))// lerDl mulr_ge0.
- move=> p; rewrite !normrM normrN ler_pM// ?mulr_ge0//.
    by have := kb p.1; rewrite /herbst_k !normrM.
  apply: (le_trans (ler_wpM2l (normr_ge0 s) (herbst_DFL _ _))).
  by rewrite lerDr.
Qed.

Local Lemma herbst_df_lower (th : R) : 0 <= sin th ->
  - (sin th * t * L ^+ 2) * \int[gauss n]_x expR (t * F x) <=
  \int[P]_p herbst_df th p.
Proof.
move=> s0; set c := cos th; set s := sin th.
have cs : c ^+ 2 + s ^+ 2 = 1 := cos2Dsin2 th.
(* Rotate (x, y) to (c x - s y, s x + c y). *)
have rotE : \int[P]_p herbst_df th p =
    \int[P]_p herbst_df th (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2).
  rewrite /Rintegral; congr fine; apply/esym.
  exact: (integral_gauss2_rotation (f := EFin \o herbst_df th) cs
    (integrable_herbst_df th)).
have ptE p : herbst_df th (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2) =
    \sum_j p.2 0 j * (herbst_k j p.1 * F (c *: p.1 - s *: p.2)).
  have zE : herbst_z th (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2) = p.1.
    apply/rowP => k; rewrite /herbst_z !mxE /= -/c -/s.
    transitivity ((c ^+ 2 + s ^+ 2) * p.1 0 k); first by ring.
    by rewrite cs mul1r.
  have dzE : herbst_dz th (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2) = p.2.
    apply/rowP => k; rewrite /herbst_dz !mxE /= -/c -/s.
    transitivity ((c ^+ 2 + s ^+ 2) * p.2 0 k); first by ring.
    by rewrite cs mul1r.
  rewrite /herbst_df zE dzE /= !mulr_sumr; apply: eq_bigr => j _.
  by rewrite /herbst_k; ring.
rewrite rotE.
have -> : \int[P]_p herbst_df th (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2) =
    \int[P]_p \sum_j p.2 0 j * (herbst_k j p.1 * F (c *: p.1 - s *: p.2)).
  by apply: eq_Rintegral => p _; exact: ptE.
(* Integrate by parts in y, one coordinate at a time. *)
have mA := measurable_affine2 c s.
have K0 := herbst_K0.
have tL0 : 0 <= t * expR (t * K) * `|L| by rewrite !mulr_ge0// expR_ge0.
have iA : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun v : 'rV[R]_n => `|v|)).
  apply: (integrable_gauss_poly (C := 1) (k := 1)) => [|v].
    by apply: continuous_measurable_mx; exact: norm_continuous.
  by rewrite normr_id mul1r expr1 lerDr.
have iT j : P.-integrable [set: 'rV[R]_n * 'rV[R]_n]
    (EFin \o (fun p : 'rV[R]_n * 'rV[R]_n =>
      p.2 0 j * (herbst_k j p.1 * F (c *: p.1 - s *: p.2)))).
  apply: (le_integrable measurableT _ _ (integrableZl measurableT
    (t * expR (t * K) * `|L| * K) (integrable_gauss2_snd iA))).
    apply/measurable_EFinP; apply: measurable_funM.
      exact: (measurableT_comp (measurable_mxentry 0 j) measurable_snd).
    apply: measurable_funM; first exact: measurableT_comp (herbst_mk j) measurable_fst.
    exact: measurableT_comp herbst_mF mA.
  move=> p _; rewrite /comp -EFinM lee_fin [leRHS]ger0_norm ?mulr_ge0//.
  rewrite normrM mulrC ler_pM//; last exact: mx_norm_entry_le.
  by rewrite normrM ler_pM//; exact: herbst_k_bound.
have mD j : measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
    (fun p : 'rV[R]_n * 'rV[R]_n =>
      herbst_k j p.1 * (- s * DF j (c *: p.1 - s *: p.2))).
  apply: measurable_funM; first exact: measurableT_comp (herbst_mk j) measurable_fst.
  by apply: measurable_funM => //; exact: measurableT_comp (herbst_mDF j) mA.
have bD j p : `|herbst_k j p.1 * (- s * DF j (c *: p.1 - s *: p.2))| <=
    t * expR (t * K) * `|L| * (`|s| * `|L|).
  rewrite normrM ler_pM//; first exact: herbst_k_bound.
  by rewrite normrM normrN ler_wpM2l// herbst_DFL.
have iD j := integrable_prob_bounded P (mD j) (bD j).
rewrite Rintegral_sum//.
under eq_bigr do rewrite herbst_ibp.
rewrite -Rintegral_sum//.
(* Compare with the integral of expR (t * F x) by Cauchy-Schwarz. *)
have me : measurable_fun [set: 'rV[R]_n] (fun x => expR (t * F x)).
  by apply: measurableT_comp => //; apply: measurable_funM => //; exact: herbst_mF.
have be x : `|expR (t * F x)| <= expR (t * K).
  by rewrite ger0_norm ?expR_ge0// herbst_expR_le.
have ie := integrable_prob_bounded (gauss n) me be.
have -> : \int[gauss n]_x expR (t * F x) = \int[P]_p expR (t * F p.1).
  by rewrite /Rintegral (integral_gauss2_fst ie).
have ie2 : P.-integrable [set: 'rV[R]_n * 'rV[R]_n]
    (EFin \o (fun p : 'rV[R]_n * 'rV[R]_n => expR (t * F p.1))).
  exact: (integrable_gauss2_fst ie).
rewrite -RintegralZl//.
have mS : measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
    (fun p : 'rV[R]_n * 'rV[R]_n =>
      \sum_i herbst_k i p.1 * (- s * DF i (c *: p.1 - s *: p.2))).
  by apply: measurable_sum => j; exact: mD.
have iS : P.-integrable [set: 'rV[R]_n * 'rV[R]_n]
    (EFin \o (fun p : 'rV[R]_n * 'rV[R]_n =>
      \sum_i herbst_k i p.1 * (- s * DF i (c *: p.1 - s *: p.2)))).
  apply: (integrable_prob_bounded P mS
    (C := n%:R * (t * expR (t * K) * `|L| * (`|s| * `|L|)))).
  move=> p; apply: (le_trans (ler_norm_sum _ _ _)).
  apply: (@le_trans _ _ (\sum_(i < n) (t * expR (t * K) * `|L| * (`|s| * `|L|)))).
    by apply: ler_sum => i _; exact: bD.
  by rewrite sumr_const card_ord -[X in X <= _]mulr_natl.
apply: le_Rintegral => //.
  have := integrableZl measurableT (- (s * t * L ^+ 2)) ie2.
  by apply: eq_integrable => // p _; rewrite /= EFinM.
move=> p _.
have -> : \sum_i herbst_k i p.1 * (- s * DF i (c *: p.1 - s *: p.2)) =
    - (s * t * expR (t * F p.1)) * \sum_i DF i p.1 * DF i (c *: p.1 - s *: p.2).
  rewrite mulr_sumr; apply: eq_bigr => i _; rewrite /herbst_k; ring.
have a0 : 0 <= s * t * expR (t * F p.1) by rewrite !mulr_ge0// expR_ge0.
have S := herbst_DFdot p.1 (c *: p.1 - s *: p.2).
have -> : - (s * t * L ^+ 2) * expR (t * F p.1) =
    - (s * t * expR (t * F p.1)) * L ^+ 2 by ring.
by rewrite !mulNr lerN2 ler_wpM2l.
Qed.

(* The covariance inequality behind Herbst's argument:
   E[F expR (t F)] <= (E[F] + t L^2) E[expR (t F)]. *)
Lemma gauss_herbst_ineq :
  \int[gauss n]_x (F x * expR (t * F x)) <=
  (\int[gauss n]_x F x + t * L ^+ 2) * \int[gauss n]_x expR (t * F x).
Proof.
set m := \int[gauss n]_x expR (t * F x).
pose phi th := \int[P]_p herbst_f th p.
pose psi th := phi th - t * L ^+ 2 * m * cos th.
have psid (th : R) : th \in `]-1, 2[ ->
    is_derive th 1 psi (\int[P]_p herbst_df th p + t * L ^+ 2 * m * sin th).
  move=> thI; have h := is_deriveB (herbst_phi_derive thI)
    (is_deriveZ (t * L ^+ 2 * m) (is_derive_cos th)).
  by apply: (is_derive_eq h); rewrite /GRing.scale /= mulrN opprK.
have I02 (x : R) : x \in `[0, pi / 2] -> x \in `]-1, 2[.
  rewrite !in_itv /= => /andP[x0 x1].
  by rewrite (lt_le_trans _ x0) ?ltrN10// (le_lt_trans x1)// pihalf_lt2.
have cpsi : {within `[0, pi / 2], continuous psi}.
  apply: derivable_within_continuous => x xI.
  by case: (psid x (I02 x xI)).
have pi0 : 0 <= pi / 2 :> R by rewrite divr_ge0// ltW// pi_gt0.
have [c cI E] := MVT_segment pi0
  (fun x xI => psid x (I02 x (subset_itv_oo_cc xI))) cpsi.
have sc : 0 <= sin c.
  apply: sin_ge0_pi; move: cI; rewrite !in_itv /= => /andP[c0 c1].
  rewrite c0 (le_trans c1)// ler_pdivrMr// ler_peMr// ?ler1n//.
  exact: (ltW (@pi_gt0 R)).
have le_psi : psi 0 <= psi (pi / 2).
  rewrite -subr_ge0 E subr0 mulr_ge0//.
  rewrite -lerBlDr sub0r (le_trans _ (herbst_df_lower sc))//.
  by rewrite -/m le_eqVlt; apply/orP; left; apply/eqP; ring.
(* The ends of the path: phi 0 = E[F expR (t F)], phi (pi / 2) = E[F] m. *)
have me : measurable_fun [set: 'rV[R]_n] (fun x => expR (t * F x)).
  by apply: measurableT_comp => //; apply: measurable_funM => //; exact: herbst_mF.
have mFe : measurable_fun [set: 'rV[R]_n] (fun x => F x * expR (t * F x)).
  exact: measurable_funM herbst_mF me.
have K0 := herbst_K0.
have be x : `|expR (t * F x)| <= expR (t * K).
  by rewrite ger0_norm ?expR_ge0// herbst_expR_le.
have bFe x : `|F x * expR (t * F x)| <= K * expR (t * K).
  by rewrite normrM ler_pM.
have phi0 : phi 0 = \int[gauss n]_x (F x * expR (t * F x)).
  rewrite /phi /herbst_f /herbst_z cos0 sin0 /Rintegral.
  under eq_integral do rewrite scale1r scale0r addr0.
  by rewrite (integral_gauss2_fst (integrable_prob_bounded _ mFe bFe)).
have phi1 : phi (pi / 2) = \int[gauss n]_x F x * m.
  have bF' x : `|F x| <= K + expR (t * K).
    by rewrite (le_trans (FK x))// lerDl expR_ge0.
  have be' x : `|expR (t * F x)| <= K + expR (t * K).
    by rewrite (le_trans (be x))// lerDr.
  rewrite /phi /herbst_f /herbst_z cos_pihalf sin_pihalf /Rintegral.
  under eq_integral do rewrite scale0r add0r scale1r.
  rewrite (integral_gauss2_prod herbst_mF me bF' be') fineM//.
    apply: integrable_fin_num => //.
    exact: (integrable_prob_bounded _ herbst_mF FK).
  apply: integrable_fin_num => //.
  exact: (integrable_prob_bounded _ me be).
move: le_psi; rewrite /psi cos0 cos_pihalf phi0 phi1 mulr0 subr0 mulr1.
by rewrite lerBlDr mulrDl addrC.
Qed.

End herbst_t.

Local Lemma herbst_mgf_derive (s : R) :
  is_derive s 1 (fun s => \int[gauss n]_x expR (s * F x))
    (\int[gauss n]_x (F x * expR (s * F x))).
Proof.
have sI : s \in `](s - 1), (s + 1)[.
  by rewrite in_itv /=; apply/andP; split; [rewrite ltrBlDr|]; rewrite ltrDl ltr01.
have K0 := herbst_K0.
have ed (x : 'rV[R]_n) (a : R) :
    is_derive a 1 (fun a => expR (a * F x)) (F x * expR (a * F x)).
  have h := @is_derive1_comp R expR (fun a => a * F x) a _ _ (is_derive_expR _)
    (is_deriveM (is_derive_id a 1) (is_derive_cst (F x) a 1)).
  by apply: (is_derive_eq h); rewrite /GRing.scale /= mulr0 add0r mulr1 mulrC.
have mE (a : R) : measurable_fun [set: 'rV[R]_n] (fun x => expR (a * F x)).
  by apply: measurableT_comp => //; apply: measurable_funM => //; exact: herbst_mF.
have eb (a : R) x : expR (a * F x) <= expR (`|a| * K).
  by rewrite ler_expR (le_trans (ler_norm _))// normrM ler_wpM2l.
have aI (a : R) : a \in `](s - 1), (s + 1)[ -> `|a| <= `|s| + 1.
  rewrite in_itv /= => /andP[a1 a2]; rewrite ler_norml; apply/andP; split.
    rewrite (le_trans _ (ltW a1))// opprD lerD2r.
    by rewrite lerNl ler_normr lexx orbT.
  by rewrite (le_trans (ltW a2))// lerD2r ler_norm.
apply: (is_derive_Rintegral sI (D := fun _ => K * expR ((`|s| + 1) * K)) _
  (fun a x _ => ed x a)).
- move=> a _; apply: (integrable_prob_bounded _ (mE a) (C := expR (`|a| * K))) => x.
  by rewrite ger0_norm ?expR_ge0// eb.
- by move=> _; rewrite mulr_ge0// expR_ge0.
- exact: finite_measure_integrable_cst.
- move=> a x /aI ab; rewrite normrM (ger0_norm (expR_ge0 _)) ler_pM// ?expR_ge0//.
  by rewrite (le_trans (eb a x))// ler_expR ler_wpM2r.
Qed.

Lemma gauss_concentration_smooth_ge0 (t : R) : 0 <= t ->
  \int[gauss n]_x expR (t * (F x - \int[gauss n]_y F y)) <=
  expR (t ^+ 2 * L ^+ 2 / 2).
Proof.
move=> t0.
set mu := \int[gauss n]_y F y.
pose m s := \int[gauss n]_x expR (s * F x).
pose q s := - (mu * s + s ^+ 2 * L ^+ 2 / 2).
pose k s := m s * expR (q s).
have qd (s : R) : is_derive s 1 q (- (mu + s * L ^+ 2)).
  have hsq : is_derive s 1 (@GRing.exp R ^~ 2) (2%:R *: s ^+ 1 *: 1).
    by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
  have h := is_deriveN (is_deriveD (is_deriveZ mu (is_derive_id s 1))
    (is_deriveZ (L ^+ 2 / 2) hsq)).
  have -> : q = - (mu \*: id + (L ^+ 2 / 2) \*: (@GRing.exp R ^~ 2)).
    apply/funext => x; rewrite /q !fctE /GRing.scale /=.
    by rewrite /GRing.scale /=; ring.
  by apply: (is_derive_eq h); rewrite /GRing.scale /= !mulr1 expr1; field.
(* k' = (E[F expR (s F)] - (mu + s L^2) m s) expR (q s) <= 0 for s >= 0. *)
have kd (s : R) : is_derive s 1 k
    ((\int[gauss n]_x (F x * expR (s * F x)) - (mu + s * L ^+ 2) * m s) *
     expR (q s)).
  have h := is_deriveM (herbst_mgf_derive s)
    (@is_derive1_comp R expR q s _ _ (is_derive_expR _) (qd s)).
  apply: (is_derive_eq h); rewrite /GRing.scale /= /m.
  set A := \int[gauss n]_x expR (s * F x).
  set B := \int[gauss n]_x (F x * expR (s * F x)).
  by set E := expR (q s); ring.
have me (s : R) : measurable_fun [set: 'rV[R]_n] (fun x => expR (s * F x)).
  by apply: measurableT_comp => //; apply: measurable_funM => //; exact: herbst_mF.
have K0 := herbst_K0.
have m0 : m 0 = 1.
  rewrite /m; under eq_Rintegral do rewrite mul0r expR0.
  by rewrite Rintegral_cst// [X in fine X]probability_setT mulr1.
have k0 : k 0 = 1.
  by rewrite /k m0 /q mulr0 expr0n /= !mul0r addr0 oppr0 expR0 mulr1.
have ck : {within `[0, t], continuous k}.
  by apply: derivable_within_continuous => x _; case: (kd x).
have [c cI E] := MVT_segment t0 (fun x _ => kd x) ck.
have c0 : 0 <= c by move: cI; rewrite in_itv /= => /andP[].
have kt : k t <= k 0.
  rewrite -subr_le0 E subr0 mulr_le0_ge0// mulr_le0_ge0 ?expR_ge0//.
  by rewrite subr_le0 gauss_herbst_ineq.
have be x : `|expR (t * F x)| <= expR (t * K).
  by rewrite ger0_norm ?expR_ge0// ler_expR ler_wpM2l// (le_trans (ler_norm _))// FK.
have ie := integrable_prob_bounded (gauss n) (me t) be.
have -> : \int[gauss n]_x expR (t * (F x - mu)) = m t * expR (- (t * mu)).
  rewrite /m -RintegralZr//; apply: eq_Rintegral => x _; rewrite -expRD.
  by congr expR; ring.
move: kt; rewrite k0 /k /q.
have -> : - (mu * t + t ^+ 2 * L ^+ 2 / 2) = - (t * mu) + - (t ^+ 2 * L ^+ 2 / 2).
  by ring.
rewrite expRD expRN mulrA ler_pdivrMr ?expR_gt0//.
by rewrite expRN -mulrA -invfM ler_pdivrMr ?mulr_gt0 ?expR_gt0// mul1r mulrC.
Qed.

End gauss_herbst.

Section gauss_concentration_smooth.
Context {R : realType} {n : nat}.

(* Gaussian concentration for a bounded function of class C^1 whose
   gradient has Euclidean norm at most L, with the sharp constant. *)
Theorem gauss_concentration_smooth (F : 'rV[R]_n -> R) (DF : 'I_n -> 'rV[R]_n -> R)
    (K L t : R) :
    (forall j x, is_derive x (delta_mx 0 j) F (DF j x)) ->
    (forall j, continuous (DF j)) -> (forall x, `|F x| <= K) ->
    (forall x, mxdot (\row_j DF j x) (\row_j DF j x) <= L ^+ 2) ->
  \int[gauss n]_x expR (t * (F x - \int[gauss n]_y F y)) <=
  expR (t ^+ 2 * L ^+ 2 / 2).
Proof.
move=> dF cDF FK gL.
have [t0|t0] := leP 0 t; first exact: (gauss_concentration_smooth_ge0 dF cDF FK gL t0).
(* For t < 0, apply the case t >= 0 to - F. *)
have dF' j x : is_derive x (delta_mx 0 j) (fun x => - F x) (- DF j x).
  exact: is_deriveN (dF j x).
have cDF' j : continuous (fun x => - DF j x).
  by move=> x; apply: continuousN; exact: cDF.
have FK' x : `|- F x| <= K by rewrite normrN.
have gL' x : mxdot (\row_j - DF j x) (\row_j - DF j x) <= L ^+ 2.
  have -> : \row_j - DF j x = - \row_j DF j x by apply/rowP => j; rewrite !mxE.
  by rewrite mxdotNl mxdotNr opprK.
have t0' : 0 <= - t by rewrite oppr_ge0 ltW.
have := gauss_concentration_smooth_ge0 dF' cDF' FK' gL' t0'.
rewrite sqrrN; apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP.
have iF : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o F).
  apply: (integrable_prob_bounded _ _ FK); apply: continuous_measurable_mx => x.
  exact: differentiable_continuous (differentiable_partials dF cDF x).
rewrite (_ : \int[gauss n]_y - F y = - \int[gauss n]_y F y).
  rewrite -mulN1r -RintegralZl//.
  by apply: eq_Rintegral => x _; rewrite mulN1r.
by apply: eq_Rintegral => x _; congr expR; ring.
Qed.

End gauss_concentration_smooth.

Section clip.
Context {R : realType}.

(* The clipping of x to [-k, k]. *)
Definition clip (k x : R) : R := Num.max (- k) (Num.min k x).

Lemma clip_bound (k x : R) : 0 <= k -> `|clip k x| <= k.
Proof.
move=> k0; rewrite /clip ler_norml; apply/andP; split.
  by rewrite le_max lexx.
by rewrite ge_max ge_min lexx orTb andbT lerNl (le_trans _ k0)// oppr_le0.
Qed.

Lemma clip_id (k x : R) : `|x| <= k -> clip k x = x.
Proof.
rewrite ler_norml => /andP[kx xk].
by rewrite /clip (min_r xk) (max_r kx).
Qed.

Lemma clip_abs (k x : R) : 0 <= k -> `|clip k x| <= `|x|.
Proof.
move=> k0; have [xk|xk] := leP `|x| k; first by rewrite clip_id.
by rewrite (le_trans (clip_bound x k0))// ltW.
Qed.

Lemma clip_lipschitz (k x y : R) : `|clip k x - clip k y| <= `|x - y|.
Proof.
have Lmin (c a b : R) : `|Num.min c a - Num.min c b| <= `|a - b|.
  have h1 := ler_norm (a - b); have h2 : b - a <= `|a - b| by rewrite distrC ler_norm.
  have [ca|ca] := leP c a; have [cb|cb] := leP c b;
    rewrite ?(min_l ca) ?(min_r (ltW ca)) ?(min_l cb) ?(min_r (ltW cb));
    rewrite ler_norml; apply/andP; split; lra.
have Lmax (c a b : R) : `|Num.max c a - Num.max c b| <= `|a - b|.
  have h1 := ler_norm (a - b); have h2 : b - a <= `|a - b| by rewrite distrC ler_norm.
  have [ca|ca] := leP c a; have [cb|cb] := leP c b;
    rewrite ?(max_r ca) ?(max_l (ltW ca)) ?(max_r cb) ?(max_l (ltW cb));
    rewrite ler_norml; apply/andP; split; lra.
exact: le_trans (Lmax _ _ _) (Lmin _ _ _).
Qed.

End clip.

Section gauss_concentration_lipschitz.
Context {R : realType} {n : nat}.
Variables (F : 'rV[R]_n -> R) (L : R).
Hypothesis FL : forall x y, `|F x - F y| <= L * frobenius (x - y).

Let cF : continuous F := lipschitz_frobenius_continuous FL.
Let mF : measurable_fun [set: 'rV[R]_n] F := continuous_measurable_mx cF.
Let M : R := \int[gauss n]_y frobenius y.

Let M0 : 0 <= M.
Proof. by apply: Rintegral_ge0 => y _; exact: frobenius_ge0. Qed.

Lemma lipschitz_frobenius_bound x : `|F x| <= `|F 0| + `|L| * frobenius x.
Proof.
have h := FL x 0; rewrite subr0 in h.
rewrite -[F x](subrK (F 0)) (le_trans (ler_normD _ _))// addrC lerD2l.
by rewrite (le_trans h)// ler_wpM2r ?frobenius_ge0// ler_norm.
Qed.

Lemma integrable_gauss_lipschitz : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o F).
Proof.
have iF := integrable_gauss_frobenius (R := R) (n := n).
have iC := finite_measure_integrable_cst (gauss n) `|F 0| measurableT.
have := integrableD measurableT iC (integrableZl measurableT `|L| iF).
apply: le_integrable => //; first exact/measurable_EFinP.
move=> x _ /=; rewrite lee_fin [leRHS]ger0_norm ?addr_ge0 ?mulr_ge0 ?frobenius_ge0//.
exact: lipschitz_frobenius_bound.
Qed.

(* The approximations of F: clip it to [-(k + 1), k + 1], then smooth it
   at the scale 1 / (k + 1). *)
Local Definition lip_approx (k : nat) : 'rV[R]_n -> R :=
  gauss_smooth (k.+1%:R^-1) (fun x => clip k.+1%:R (F x)).

Let clipL k x y : `|clip k.+1%:R (F x) - clip k.+1%:R (F y)| <= L * frobenius (x - y).
Proof. exact: le_trans (clip_lipschitz _ _ _) (FL x y). Qed.

Let clipK k x : `|clip k.+1%:R (F x)| <= k.+1%:R.
Proof. exact: clip_bound. Qed.

Let ek0 (k : nat) : 0 < k.+1%:R^-1 :> R.
Proof. by rewrite invr_gt0 ltr0n. Qed.

Local Lemma lip_approx_mgf k t :
  \int[gauss n]_x expR (t * (lip_approx k x - \int[gauss n]_y lip_approx k y)) <=
  expR (t ^+ 2 * L ^+ 2 / 2).
Proof.
apply: (gauss_concentration_smooth (K := k.+1%:R)
  (DF := gauss_smooth_partial k.+1%:R^-1 (fun x => clip k.+1%:R (F x)))).
- by move=> j x; exact: (gauss_smooth_derive (clipK k) (clipL k) (ek0 k)).
- by move=> j; exact: (continuous_gauss_smooth_partial (clipK k) (clipL k) (ek0 k)).
- by move=> x; exact: (gauss_smooth_bounded k.+1%:R^-1 (clipK k) (clipL k)).
- by move=> x; exact: (gauss_smooth_grad (clipK k) (clipL k) (ek0 k)).
Qed.

Local Lemma lip_approx_dom k x : `|lip_approx k x| <= `|F x| + `|L| * M.
Proof.
have h := gauss_smooth_close (clipK k) (clipL k) (ek0 k) x.
rewrite -/M in h.
rewrite -[lip_approx k x](subrK (clip k.+1%:R (F x))) (le_trans (ler_normD _ _))//.
rewrite addrC lerD ?clip_abs// (le_trans h)// ler_wpM2r//.
rewrite (le_trans (ler_norm _))// normrM (ger0_norm (ltW (ek0 k))).
by rewrite ler_piMr// invf_le1// ler1n.
Qed.

Local Lemma lip_approx_cvg x : lip_approx ^~ x @ \oo --> F x.
Proof.
apply/cvgrPdist_le => e e0; near=> k.
have kk : (k%:R : R) <= k.+1%:R by rewrite ler_nat.
have k1 : `|F x| <= k.+1%:R.
  by rewrite (le_trans _ kk)//; near: k; exact: nbhs_infty_ger.
have k2 : `|L| * M / e <= k.+1%:R.
  by rewrite (le_trans _ kk)//; near: k; exact: nbhs_infty_ger.
have h := gauss_smooth_close (clipK k) (clipL k) (ek0 k) x.
rewrite -/M (clip_id k1) in h.
rewrite distrC (le_trans h)//.
apply: (@le_trans _ _ (`|L| * M / k.+1%:R)).
  by rewrite mulrAC ler_wpM2r ?invr_ge0// ler_wpM2r// ler_norm.
by rewrite ler_pdivrMr ?ltr0n// -ler_pdivrMl// mulrC.
Unshelve. all: by end_near.
Qed.

Let mA k : measurable_fun [set: 'rV[R]_n] (lip_approx k).
Proof.
apply: continuous_measurable_mx; apply: lipschitz_frobenius_continuous.
exact: (gauss_smooth_lipschitz _ (clipK k) (clipL k)).
Qed.

Local Lemma lip_approx_mean :
  (fun k => \int[gauss n]_x lip_approx k x) @ \oo --> \int[gauss n]_x F x.
Proof.
have iF := integrable_gauss_lipschitz.
have iFa : (gauss n).-integrable [set: 'rV[R]_n] (EFin \o (fun x => `|F x|)).
  apply/integrableP; split; first exact/measurable_EFinP/measurableT_comp.
  case/integrableP: iF => _; apply: le_lt_trans; apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; apply/measurable_EFinP; exact: measurableT_comp.
  - exact/measurableT_comp/measurable_EFinP.
  - by move=> x _; rewrite /= normr_id.
have ig : (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x => `|F x| + `|L| * M)).
  have := integrableD measurableT iFa
    (finite_measure_integrable_cst (gauss n) (`|L| * M) measurableT).
  by apply: eq_integrable => // x _; rewrite /= EFinD.
have H1 k : measurable_fun [set: 'rV[R]_n] (EFin \o lip_approx k).
  by apply/measurable_EFinP; exact: mA.
have H2 x : [set: 'rV[R]_n] x -> (EFin \o lip_approx ^~ x) @ \oo --> (EFin \o F) x.
  move=> _; apply: cvg_EFin; first exact: nearW.
  exact: lip_approx_cvg.
have H4 k x : [set: 'rV[R]_n] x ->
    (`|(EFin \o lip_approx k) x| <= (EFin \o (fun x => `|F x| + `|L| * M)%R) x)%E.
  by move=> _; rewrite /= lee_fin lip_approx_dom.
have h := @dominated_cvg _ _ R (gauss n) setT measurableT
  (fun k => EFin \o lip_approx k) (EFin \o F)
  (EFin \o (fun x => `|F x| + `|L| * M)) H1 H2 (fun x _ => isT) ig H4.
have Ffin : (\int[gauss n]_x (EFin \o F) x)%E \is a fin_num.
  exact: integrable_fin_num iF.
rewrite -(fineK Ffin) in h.
exact: (fine_cvg h).
Qed.

(* Gaussian concentration for Lipschitz functions (Tsirelson, Ibragimov and
   Sudakov), with the sharp constant. *)
Theorem gauss_concentration (t : R) :
  (\int[gauss n]_x (expR (t * (F x - \int[gauss n]_y F y)))%:E <=
   (expR (t ^+ 2 * L ^+ 2 / 2))%:E)%E.
Proof.
set mu := \int[gauss n]_y F y.
pose m k := \int[gauss n]_y lip_approx k y.
pose f k x := (expR (t * (lip_approx k x - m k)))%:E.
have mf k : measurable_fun [set: 'rV[R]_n] (f k).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; apply: measurable_funB => //; exact: mA.
have f0 k x : [set: 'rV[R]_n] x -> (0 <= f k x)%E.
  by move=> _; rewrite lee_fin expR_ge0.
have fcvg x : f ^~ x @ \oo --> (expR (t * (F x - mu)))%:E.
  apply: cvg_EFin; first exact: nearW.
  apply: continuous_cvg; first exact: continuous_expR.
  apply: cvgM; first exact: cvg_cst.
  by apply: cvgB; [exact: lip_approx_cvg|exact: lip_approx_mean].
have := fatou (gauss n) measurableT mf f0.
have -> : (\int[gauss n]_(x in [set: 'rV[R]_n]) limn_einf (f ^~ x) =
    \int[gauss n]_x (expR (t * (F x - mu)))%:E)%E.
  by apply: eq_integral => x _; exact: (cvg_limn_einf_sup (fcvg x)).1.
move=> /le_trans; apply.
rewrite limn_einf_lim; apply: lime_le; first exact: is_cvg_einfs.
apply: nearW => k; apply: (le_trans (ereal_inf_lbound _)); first by exists k => /=.
have bk x : `|expR (t * (lip_approx k x - m k))| <=
    expR (`|t| * (k.+1%:R + `|m k|)).
  rewrite (ger0_norm (expR_ge0 _)) ler_expR (le_trans (ler_norm _))// normrM.
  rewrite ler_wpM2l// (le_trans (ler_normB _ _))// lerD2r.
  exact: (gauss_smooth_bounded k.+1%:R^-1 (clipK k) (clipL k)).
have mk : measurable_fun [set: 'rV[R]_n] (fun x => expR (t * (lip_approx k x - m k))).
  apply: measurableT_comp => //.
  by apply: measurable_funM => //; apply: measurable_funB => //; exact: mA.
have ik := integrable_prob_bounded (gauss n) mk bk.
rewrite -(fineK (integrable_fin_num measurableT ik)) lee_fin.
exact: lip_approx_mgf.
Qed.

Corollary integrable_gauss_concentration (t : R) :
  (gauss n).-integrable [set: 'rV[R]_n]
    (EFin \o (fun x => expR (t * (F x - \int[gauss n]_y F y)))).
Proof.
apply/integrableP; split.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funB.
under eq_integral do rewrite /= ger0_norm ?expR_ge0//.
exact: le_lt_trans (gauss_concentration t) (ltry _).
Qed.

Corollary gauss_concentration_upper_tail (u : R) : 0 <= u ->
  (gauss n [set x | \int[gauss n]_y F y + u <= F x]%R <=
   (expR (- u ^+ 2 / (2 * L ^+ 2)))%:E)%E.
Proof.
move=> u0; set mu := \int[gauss n]_y F y.
have [->|L0] := eqVneq L 0.
  rewrite expr0n /= mulr0 invr0 mulr0 expR0; apply: probability_le1.
  have -> : [set x | (mu + u <= F x)%R] = F @^-1` `[mu + u, +oo[.
    by rewrite preimage_itvcy.
  by rewrite -[X in measurable X]setTI; apply: mF => //; exact: measurable_itv.
have L2 : 0 < L ^+ 2 by rewrite exprn_even_gt0.
set t := u / L ^+ 2.
have t0 : 0 <= t by rewrite divr_ge0// ltW.
apply: (le_trans (measure_ge_expR (gauss n) (mu + u) mF t0)).
have -> : (\int[gauss n]_x (expR (t * (F x - (mu + u))))%:E =
    \int[gauss n]_x ((expR (t * (F x - mu)))%:E * (expR (- (t * u)))%:E))%E.
  by apply: eq_integral => x _; rewrite -EFinM -expRD; congr (expR _)%:E; ring.
have me : measurable_fun [set: 'rV[R]_n] (fun x => (expR (t * (F x - mu)))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_funB.
have e0 x : [set: 'rV[R]_n] x -> (0 <= (expR (t * (F x - mu)))%:E)%E.
  by move=> _; rewrite lee_fin expR_ge0.
rewrite ge0_integralZr// ?lee_fin ?expR_ge0//.
rewrite (le_trans (lee_wpmul2r _ (gauss_concentration t)))// ?lee_fin ?expR_ge0//.
rewrite -expRD ler_expR /t le_eqVlt; apply/orP; left; apply/eqP.
have L2' : L ^+ 2 != 0 by rewrite gt_eqF.
by field.
Qed.

End gauss_concentration_lipschitz.

Section gauss_concentration_tails.
Context {R : realType} {n : nat}.
Variables (F : 'rV[R]_n -> R) (L : R).
Hypothesis FL : forall x y, `|F x - F y| <= L * frobenius (x - y).

Let mF : measurable_fun [set: 'rV[R]_n] F :=
  continuous_measurable_mx (lipschitz_frobenius_continuous FL).

Corollary gauss_concentration_lower_tail (u : R) : 0 <= u ->
  (gauss n [set x | F x <= \int[gauss n]_y F y - u]%R <=
   (expR (- u ^+ 2 / (2 * L ^+ 2)))%:E)%E.
Proof.
move=> u0.
have FL' x y : `|- F x - - F y| <= L * frobenius (x - y).
  by rewrite -opprD normrN; exact: FL.
have := gauss_concentration_upper_tail FL' u0.
have iF := integrable_gauss_lipschitz FL.
have -> : \int[gauss n]_y - F y = - \int[gauss n]_y F y.
  rewrite -mulN1r -RintegralZl//.
  by apply: eq_Rintegral => x _; rewrite mulN1r.
apply: le_trans; rewrite le_eqVlt; apply/orP; left; apply/eqP; congr (gauss n _).
by apply/seteqP; split => x /=; lra.
Qed.

Corollary gauss_concentration_abs_tail (u : R) : 0 <= u ->
  (gauss n [set x | u <= `|F x - \int[gauss n]_y F y|]%R <=
   (2 * expR (- u ^+ 2 / (2 * L ^+ 2)))%:E)%E.
Proof.
move=> u0; set mu := \int[gauss n]_y F y.
have -> : [set x | u <= `|F x - mu|]%R =
    [set x | mu + u <= F x]%R `|` [set x | F x <= mu - u]%R.
  apply/seteqP; split => x /=.
    rewrite ler_normr => /orP[ux|ux]; [left|right]; lra.
  by move=> [ux|ux]; rewrite ler_normr; apply/orP; [left|right]; lra.
have mI (A : set R) : measurable A -> measurable (F @^-1` A).
  by move=> mA; rewrite -[X in measurable X]setTI; exact: mF.
apply: (le_trans (measureU2 _ _ _)).
- by rewrite -preimage_itvcy; apply: mI; exact: measurable_itv.
- by rewrite -preimage_itvNyc; apply: mI; exact: measurable_itv.
rewrite mulr_natl mulr2n EFinD.
apply: leeD; first exact: gauss_concentration_upper_tail.
exact: gauss_concentration_lower_tail.
Qed.

End gauss_concentration_tails.
