From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences exp derive realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral numfun.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear real_spectral.
From GaussianAnalysis.matrix Require Import centered_correction centered_quadratic_correction.
From GaussianAnalysis.matrix Require Import quadratic_series_variance.
From GaussianAnalysis.convex Require Import image_projection.
From GaussianAnalysis.comparison Require Import gauss_smoothing.
From GaussianAnalysis.probability Require Import symmetrization subgaussian_matrix total_variation.
From GaussianAnalysis.random_matrix Require Import rademacher_series.

(**md**************************************************************************)
(* # A centered reserve correction for a row-sign invariant sample law       *)
(* Source: the independent-reserve argument in doc/shifted-gaussian.tex.      *)
(* The event used for sign averaging is intrinsic to the row outer products. *)
(* Centered covariance conditions are imposed only after that averaging.     *)
(* Random right-hand sides are integrated under a product law and truncated; *)
(* no moment assumption on their law is used.                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sign_algebra.
Context {R : realType} {k d : nat}.

Definition reserve_row_sign (s : k.-tuple bool) (H : 'M[R]_(k,d)) :=
  \matrix_(i,j) (rademacher (tnth s i) * H i j).

Lemma reserve_row_sign_row s H i :
  row i (reserve_row_sign s H) = rademacher (tnth s i) *: row i H.
Proof. by apply/matrixP => x j; rewrite !mxE. Qed.

Lemma reserve_row_sign_feature s H i :
  reserve_feature (reserve_row_sign s H) i = reserve_feature H i.
Proof.
rewrite /reserve_feature reserve_row_sign_row [(_ *: _)^T]linearZ /= -scalemxAl
  -scalemxAr scalerA -expr2 rademacher_sqr scale1r.
by [].
Qed.

Lemma reserve_row_sign_norm s H i :
  frobenius (row i (reserve_row_sign s H)) = frobenius (row i H).
Proof.
by rewrite reserve_row_sign_row frobeniusZ normr_rademacher mul1r.
Qed.

Definition reserve_intrinsic (L M : R) : set 'M[R]_(k,d) :=
  [set H | (forall t : 'rV[R]_k,
    frobenius (coef_adj (reserve_feature H) t) <= L * frobenius t) /\
    (forall i, frobenius (row i H) ^+ 2 <= M)].

Lemma reserve_intrinsic_sign L M s H :
  reserve_intrinsic L M (reserve_row_sign s H) <-> reserve_intrinsic L M H.
Proof.
have feat : reserve_feature (reserve_row_sign s H) = reserve_feature H.
  by apply/funext => i; exact: reserve_row_sign_feature.
rewrite /reserve_intrinsic /= feat.
split; move=> [ha hr]; split => // i.
- by move: (hr i); rewrite reserve_row_sign_norm.
- by rewrite reserve_row_sign_norm; exact: hr.
Qed.

Lemma reserve_linearized_sign s H (b : 'cV[R]_d) :
  reserve_linearized_quadratic (reserve_row_sign s H) b =
  k%:R^-1 *: \sum_i rademacher (tnth s i) *:
    (mxdot (row i H)^T b *: reserve_feature H i).
Proof.
rewrite /reserve_linearized_quadratic /coef_adj; congr (_ *: _).
apply: eq_bigr => i _; rewrite reserve_row_sign_feature scalerA.
congr (_ *: _); rewrite mxE mxE /reserve_row_sign.
under eq_bigr do rewrite mxE -mulrA.
rewrite -mulr_sumr mxdot_colE.
rewrite trmxK mxE; congr (_ * _).
by apply: eq_bigr => j _; rewrite mxE.
Qed.

Lemma reserve_linearized_sign_mean (L M : R) H (b : 'cV[R]_d) :
  (0 < d)%N -> 0 <= L -> 0 <= M -> reserve_intrinsic L M H ->
  rademacher_mean (fun s : k.-tuple bool =>
    opnorm (reserve_linearized_quadratic (reserve_row_sign s H) b)) <=
  40 * Num.sqrt (ln (2 * d%:R)) *
    Num.sqrt (M * quadratic_fourth_constant k L +
      Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b / k%:R.
Proof.
move=> d0 L0 M0 [adj rows].
pose u i := (row i H)^T.
pose A i := mxdot (u i) b *: quadratic_series_feature u i.
have fe i : quadratic_series_feature u i = reserve_feature H i.
  by rewrite /quadratic_series_feature /u trmxK.
have Asym i : A i \is symmetricmx.
  apply/symmetricmxP; rewrite /A linearZ /=.
  by rewrite (symmetricmxP _ (quadratic_feature_symmetric u i)).
have adj' t : frobenius (coef_adj (quadratic_series_feature u) t) <=
    L * frobenius t.
  have -> : quadratic_series_feature u = reserve_feature H by apply/funext.
  exact: adj.
have row' i : frobenius (u i) ^+ 2 <= M.
  by rewrite /u frobenius_trmx.
have vb := quadratic_series_variance_bound L0 M0 adj' row' b.
have ve : \sum_i A i ^+ 2 = quadratic_series_variance u b.
  apply: eq_bigr => i _; rewrite /A expr2 -scalerAl -scalerAr scalerA.
  by rewrite -expr2.
have hb := rademacher_mx_series_variance d0 Asym.
rewrite ve in hb.
have v0 : 0 <= M * quadratic_fourth_constant k L +
    Num.sqrt (k%:R * quadratic_fourth_constant k L).
  apply: addr_ge0 => //; apply: mulr_ge0 => //.
  exact: quadratic_fourth_constant_ge0.
have hs := ler_wsqrtr vb.
rewrite sqrtrM // sqrtr_sqr ger0_norm ?frobenius_ge0 // in hs.
have cf0 : 0 <= 40 * Num.sqrt (ln (2 * d%:R)) :> R by rewrite ?invr_ge0 ?mulr_ge0 ?sqrtr_ge0 ?ler0n.
have ki0 : 0 <= (k%:R : R)^-1 by rewrite ?invr_ge0 ?mulr_ge0 ?sqrtr_ge0 ?ler0n.
apply: le_trans (_ : k%:R^-1 *
    (40 * Num.sqrt (ln (2 * d%:R)) *
      (Num.sqrt (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b)) <= _).
  have -> : rademacher_mean (fun s : k.-tuple bool =>
      opnorm (reserve_linearized_quadratic (reserve_row_sign s H) b)) =
      k%:R^-1 * rademacher_mean (fun s : k.-tuple bool =>
        opnorm (\sum_i rademacher (tnth s i) *: A i)).
    rewrite -rademacher_meanZ /rademacher_mean; congr (_ * _).
    apply: eq_bigr => s _; rewrite (reserve_linearized_sign s H b) opnormZ (ger0_norm ki0).
    have e : (\sum_i rademacher (tnth s i) *:
        (mxdot (row i H)^T b *: reserve_feature H i)) =
        (\sum_i rademacher (tnth s i) *: A i).
      by apply: eq_bigr => i _; rewrite /A /u fe.
    by rewrite e.
  apply: ler_wpM2l => //.
  exact: le_trans hb (ler_wpM2l cf0 hs).
rewrite [k%:R^-1 * _]mulrC !mulrA.
exact: lexx.
Qed.

End sign_algebra.

Section intrinsic_measurability.
Context {R : realType} {k d : nat}.

Lemma reserve_frobenius_continuous m n : continuous (@frobenius R m n).
Proof.
move=> A; rewrite /frobenius; apply: (continuous_comp (f := fun A : 'M[R]_(m,n) => mxdot A A) (g := Num.sqrt)).
- rewrite /mxdot; apply: (@cvg_big R^o _ +%R 0 xpredT (@add_continuous R^o)); first exact: nbhs_filter.
  move=> i _; apply: (@cvg_big R^o _ +%R 0 xpredT (@add_continuous R^o)); first exact: nbhs_filter.
  move=> j _.
  apply: continuousM; exact: matrix_normedtype.coord_continuous.
- exact: sqrt_continuous.
Qed.

Lemma reserve_adjoint_continuous (t : 'rV[R]_k) :
  continuous (fun H : 'M[R]_(k,d) => coef_adj (reserve_feature H) t).
Proof.
apply: continuous_mxP => a b.
have -> : (fun H : 'M[R]_(k,d) => coef_adj (reserve_feature H) t a b) =
    (fun H => \sum_i t 0 i * (H i a * H i b - (a == b)%:R)).
  apply/funext => H; rewrite /coef_adj summxE; apply: eq_bigr => i _.
  by rewrite /reserve_feature !mxE big_ord1 !mxE.
apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
  (fun i (H : 'M[R]_(k,d)) => t 0 i * (H i a * H i b - (a == b)%:R))) => i _ H.
apply: (continuousM (s := fun _ : 'M[R]_(k,d) => t 0 i)
  (t := fun X => X i a * X i b - (a == b)%:R)); first exact: cst_continuous.
apply: (continuousB (f := fun X : 'M[R]_(k,d) => X i a * X i b)
  (g := fun _ => (a == b)%:R)); last exact: cst_continuous.
apply: (continuousM (s := fun X : 'M[R]_(k,d) => X i a)
  (t := fun X => X i b)); exact: matrix_normedtype.coord_continuous.
Qed.

Lemma reserve_row_continuous i :
  continuous (fun H : 'M[R]_(k,d) => row i H).
Proof.
apply: continuous_mxP => a b.
have -> : (fun H : 'M[R]_(k,d) => row i H a b) = (fun H => H i b).
  by apply/funext => H; rewrite mxE.
exact: matrix_normedtype.coord_continuous.
Qed.

Lemma reserve_intrinsic_closed L M : closed (@reserve_intrinsic R k d L M).
Proof.
have -> : @reserve_intrinsic R k d L M =
    (\bigcap_(t in [set: 'rV[R]_k])
      [set H | frobenius (coef_adj (reserve_feature H) t) <= L * frobenius t])
    `&` (\bigcap_(i in [set: 'I_k])
      [set H | frobenius (row i H) ^+ 2 <= M]).
  apply/seteqP; split=> H [a b]; split.
  - by move=> t _; exact: a.
  - by move=> i _; exact: b.
  - by move=> t; exact: (a t I).
  - by move=> i; exact: (b i I).
apply: closedI.
- apply: closed_bigI => t _.
  have cf : continuous (fun H : 'M[R]_(k,d) =>
      frobenius (coef_adj (reserve_feature H) t)).
    move=> H.
    apply: (continuous_comp
      (f := fun X : 'M[R]_(k,d) => coef_adj (reserve_feature X) t)
      (g := @frobenius R d d)).
    - exact: reserve_adjoint_continuous.
    - exact: reserve_frobenius_continuous.
  exact: (continuous_closedP _).1 cf _ (@closed_le R _).
- apply: closed_bigI => i _.
  have cf : continuous (fun H : 'M[R]_(k,d) => frobenius (row i H) ^+ 2).
    have cc : continuous (fun H : 'M[R]_(k,d) => frobenius (row i H)).
      move=> H; apply: (continuous_comp (f := fun X : 'M[R]_(k,d) => row i X)
        (g := @frobenius R 1 d)).
      - exact: reserve_row_continuous.
      - exact: reserve_frobenius_continuous.
    have -> : (fun H : 'M[R]_(k,d) => frobenius (row i H) ^+ 2) =
        (fun H => frobenius (row i H) * frobenius (row i H)).
      by apply/funext => H; rewrite expr2.
    move=> H; apply: (continuousM (s := fun X : 'M[R]_(k,d) => frobenius (row i X))
      (t := fun X => frobenius (row i X))); exact: cc.
  exact: (continuous_closedP _).1 cf _ (@closed_le R M).
Qed.

Lemma reserve_intrinsic_measurable L M : measurable (@reserve_intrinsic R k d L M).
Proof.
rewrite -[X in measurable X]setCK; apply: measurableC.
apply: open_measurable_mx; apply: closed_openC.
exact: reserve_intrinsic_closed.
Qed.

End intrinsic_measurability.

Section measurable_correction.
Context {R : realType} {e} {T : measurableType e} {k d : nat}.

Lemma reserve_determinant_measurable n (A : T -> 'M[R]_n) :
  measurable_fun setT A -> measurable_fun setT (fun x => \det (A x)).
Proof.
move=> mA; rewrite /determinant; apply: measurable_sum => s.
apply: measurable_funM; first exact: measurable_cst.
have prodm (r : seq 'I_n) : measurable_fun setT
    (fun x => \prod_(i <- r) A x i (s i)).
  elim: r => [|i r IH].
  - under eq_fun do rewrite big_nil; exact: measurable_cst.
  - under eq_fun do rewrite big_cons.
    apply: measurable_funM => //; exact: measurableT_comp (measurable_mxentry i (s i)) mA.
exact: prodm.
Qed.

Lemma reserve_unitmx_measurable n (A : T -> 'M[R]_n) :
  measurable_fun setT A -> measurable_fun setT (fun x => A x \in unitmx).
Proof.
move=> mA; under eq_fun do rewrite unitmxE unitfE.
apply: measurable_neg; apply: measurable_fun_eqr; last exact: measurable_cst.
exact: reserve_determinant_measurable.
Qed.

Let reserve_scalar_inverse_measurable : measurable_fun [set: R] (fun x : R => x^-1).
Proof.
have part : [set: R] = [set 0] `|` ~` [set 0].
  apply/seteqP; split => // x _.
  have [->|x0] := eqVneq x 0; first by left.
  by right => /= x00; rewrite x00 eqxx in x0.
rewrite part; apply/measurable_funU.
- exact: measurable_set1.
- exact: measurableC (measurable_set1 _).
split; first exact: measurable_fun_set1.
apply: open_continuous_measurable_fun.
  apply: closed_openC; apply: accessible_closed_set1.
  by apply: hausdorff_accessible; exact: Rhausdorff.
by move=> x; rewrite inE /= => /eqP x0; exact: inv_continuous.
Qed.

Lemma reserve_inverse_measurable n (A : T -> 'M[R]_n) :
  measurable_fun setT A -> measurable_fun setT (fun x => invmx (A x)).
Proof.
move=> mA; rewrite /invmx; apply: measurable_fun_ifT => //.
  exact: reserve_unitmx_measurable.
apply: measurable_scalemx.
- exact: measurableT_comp reserve_scalar_inverse_measurable
    (reserve_determinant_measurable mA).
- apply/measurable_fun_mxP => i j.
  under eq_fun do rewrite mxE /cofactor.
  apply: measurable_funM; first exact: measurable_cst.
  apply: reserve_determinant_measurable; apply/measurable_fun_mxP => a b.
  under eq_fun do rewrite !mxE.
  exact: measurableT_comp (measurable_mxentry _ _) mA.
Qed.

Definition guarded_reserve_potential (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :=
  if centered_covariance H \in unitmx then centered_potential H b else 0.

Definition guarded_reserve_correction (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :=
  if centered_covariance H \in unitmx then centered_correction H b else 0.

Definition guarded_reserve_quadratic (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :=
  if centered_covariance H \in unitmx then reserve_quadratic H b else 0.

Lemma reserve_covariance_measurable (H : T -> 'M[R]_(k,d)) :
  measurable_fun setT H -> measurable_fun setT (fun x => centered_covariance (H x)).
Proof.
move=> mH; rewrite /centered_covariance; apply: measurable_mulmx => //.
- apply: measurable_mulmx; last exact: measurable_cst.
  apply: measurableT_comp; [exact: measurable_trmx | exact: mH].
Qed.

Lemma guarded_reserve_potential_measurable (H : T -> 'M[R]_(k,d)) (b : T -> 'cV[R]_d) :
  measurable_fun setT H -> measurable_fun setT b ->
  measurable_fun setT (fun x => guarded_reserve_potential (H x) (b x)).
Proof.
move=> mH mb; rewrite /guarded_reserve_potential; apply: measurable_fun_ifT.
- exact: reserve_unitmx_measurable (reserve_covariance_measurable mH).
- rewrite /centered_potential; apply: measurable_mulmx => //.
  exact: reserve_inverse_measurable (reserve_covariance_measurable mH).
- exact: measurable_cst.
Qed.

Lemma guarded_reserve_correctionE (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :
  guarded_reserve_correction H b =
    centering_mx k *m H *m guarded_reserve_potential H b.
Proof.
rewrite /guarded_reserve_correction /guarded_reserve_potential.
by case: ifP => _; rewrite /centered_correction ?mulmx0.
Qed.

Lemma guarded_reserve_correction_measurable (H : T -> 'M[R]_(k,d)) (b : T -> 'cV[R]_d) :
  measurable_fun setT H -> measurable_fun setT b ->
  measurable_fun setT (fun x => guarded_reserve_correction (H x) (b x)).
Proof.
move=> mH mb; under eq_fun do rewrite guarded_reserve_correctionE.
apply: measurable_mulmx; last exact: guarded_reserve_potential_measurable.
by apply: measurable_mulmx => //; exact: measurable_cst.
Qed.

Lemma reserve_row_measurable (H : T -> 'M[R]_(k,d)) i :
  measurable_fun setT H -> measurable_fun setT (fun x => row i (H x)).
Proof.
move=> mH; apply/measurable_fun_mxP => a b.
under eq_fun do rewrite mxE.
exact: measurableT_comp (measurable_mxentry i b) mH.
Qed.

Lemma reserve_feature_measurable (H : T -> 'M[R]_(k,d)) i :
  measurable_fun setT H -> measurable_fun setT (fun x => reserve_feature (H x) i).
Proof.
move=> mH; apply/measurable_fun_mxP => a b.
under eq_fun do rewrite /reserve_feature !mxE big_ord1 !mxE.
apply: measurable_funB; last exact: measurable_cst.
apply: measurable_funM; exact: measurableT_comp (measurable_mxentry _ _) mH.
Qed.

Lemma reserve_coef_adj_measurable (B : T -> 'I_k -> 'M[R]_d) (u : T -> 'rV[R]_k) :
  (forall i, measurable_fun setT (fun x => B x i)) -> measurable_fun setT u ->
  measurable_fun setT (fun x => coef_adj (B x) (u x)).
Proof.
move=> mB mu; apply/measurable_fun_mxP => a b.
under eq_fun do rewrite /coef_adj summxE.
apply: measurable_sum => i; under eq_fun do rewrite mxE.
apply: measurable_funM.
- exact: measurableT_comp (measurable_mxentry 0 i) mu.
- exact: measurableT_comp (measurable_mxentry a b) (mB i).
Qed.

Lemma reserve_linearized_measurable (H : T -> 'M[R]_(k,d)) (b : T -> 'cV[R]_d) :
  measurable_fun setT H -> measurable_fun setT b ->
  measurable_fun setT (fun x => reserve_linearized_quadratic (H x) (b x)).
Proof.
move=> mH mb; rewrite /reserve_linearized_quadratic.
apply: measurable_scalemx; first exact: measurable_cst.
apply: reserve_coef_adj_measurable.
- by move=> i; exact: reserve_feature_measurable.
- apply: measurableT_comp; first exact: measurable_trmx.
   exact: measurable_mulmx mH mb.
Qed.

Lemma guarded_reserve_quadraticE (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :
  guarded_reserve_quadratic H b =
    coef_adj (fun i => (row i H)^T *m row i H) (guarded_reserve_correction H b)^T.
Proof.
rewrite /guarded_reserve_quadratic /guarded_reserve_correction.
case: ifP => _; first by [].
rewrite trmx0 /coef_adj; symmetry; apply: big1 => i _.
by rewrite mxE scale0r.
Qed.

Lemma guarded_reserve_quadratic_measurable (H : T -> 'M[R]_(k,d)) (b : T -> 'cV[R]_d) :
  measurable_fun setT H -> measurable_fun setT b ->
  measurable_fun setT (fun x => guarded_reserve_quadratic (H x) (b x)).
Proof.
move=> mH mb; under eq_fun do rewrite guarded_reserve_quadraticE.
apply: reserve_coef_adj_measurable.
- move=> i; apply: measurable_mulmx; last exact: reserve_row_measurable.
  apply: measurableT_comp; first exact: measurable_trmx.
   exact: reserve_row_measurable.
- apply: measurableT_comp; first exact: measurable_trmx.
   exact: guarded_reserve_correction_measurable.
Qed.

End measurable_correction.

Section finite_tail_tools.
Context {R : realType} {e} {T : measurableType e}.
Variable P : probability T R.

Lemma reserve_Rintegral_indic (A : set T) : measurable A ->
  \int[P]_x (\1_A x : R) = fine (P A).
Proof. by move=> mA; rewrite /Rintegral integral_indic // setIT. Qed.

Lemma reserve_rademacher_markov n (F : n.-tuple bool -> R) (t : R) :
  0 < t -> (forall s, 0 <= F s) ->
  rademacher_mean (fun s => ((t < F s)%R)%:R) <= rademacher_mean F / t.
Proof.
move=> t0 F0; rewrite ler_pdivlMr // mulrC -rademacher_meanZ.
apply: ler_rademacher_mean => s.
by case: (ltP t (F s)) => h; rewrite ?mulr1 ?mulr0 //; exact: ltW.
Qed.

Lemma reserve_integral_tail (E : set T) (f : T -> R) (c : R) :
  measurable E -> measurable_fun setT f ->
  (forall x, 0 <= f x <= 1) -> 0 <= c ->
  (forall x, E x -> f x <= c) ->
  \int[P]_x f x <= fine (P (~` E)) + c.
Proof.
move=> mE mf f01 c0 Ef.
have i1 : P.-integrable setT (EFin \o (fun _ : T => (1 : R))).
  exact: finite_measure_integrable_cst.
have iff : P.-integrable setT (EFin \o f).
  apply: (le_integrable measurableT _ _ i1).
  - exact/measurable_EFinP.
  - by move=> x _; rewrite /comp !abse_EFin lee_fin !ger0_norm ?(proj1 (andP (f01 x))) //; exact: (proj2 (andP (f01 x))).
have mi : measurable (~` E) := measurableC mE.
have ii := integrable_indic P mi.
have ic : P.-integrable setT (EFin \o (fun _ : T => c)) := finite_measure_integrable_cst P c measurableT.
have sumint : P.-integrable setT (EFin \o (fun x => (\1_(~` E) x : R) + c)).
  rewrite /comp; under eq_fun do rewrite EFinD.
  exact: integrableD ii ic.
have le := le_Rintegral measurableT iff sumint _.
have point x (_ : setT x) : f x <= (\1_(~` E) x : R) + c.
  rewrite indicE; case: (x \in ~` E) / boolP => hx /=.
  - apply: le_trans (proj2 (andP (f01 x))) _.
    by lra.
  - rewrite add0r; apply: Ef.
    by move: hx; rewrite in_setC negbK => /set_mem.
have := le point.
rewrite RintegralD // reserve_Rintegral_indic // Rintegral_cst //.
by rewrite [X in c * fine X]probability_setT mulr1.
Qed.

End finite_tail_tools.

Section sign_law_tail.
Context {R : realType} {k d : nat}.

Definition reserve_sign_invariant (Q : probability 'M[R]_(k,d) R) : Prop :=
  forall (s : k.-tuple bool) A, measurable A ->
    Q ((reserve_row_sign s) @^-1` A) = Q A.

Lemma reserve_row_sign_measurable s :
  measurable_fun [set: 'M[R]_(k,d)] (@reserve_row_sign R k d s).
Proof.
apply/measurable_fun_mxP => i j; under eq_fun do rewrite /reserve_row_sign mxE.
apply: measurable_funM; [exact: measurable_cst | exact: measurable_mxentry].
Qed.

Lemma reserve_sign_average_tail (Q : probability 'M[R]_(k,d) R)
    (E : set 'M[R]_(k,d)) (f : 'M[R]_(k,d) -> R) (B t : R) :
  reserve_sign_invariant Q -> measurable E -> measurable_fun setT f ->
  (forall H, 0 <= f H) -> 0 <= B -> 0 < t ->
  (forall H, E H -> rademacher_mean (fun s : k.-tuple bool =>
    f (reserve_row_sign s H)) <= B) ->
  (Q [set H | (t < f H)%R] <= Q (~` E) + (B / t)%:E)%E.
Proof.
move=> symQ mE mf f0 B0 t0 avg.
pose A := [set H | t < f H].
have mA : measurable A.
  have mt : measurable ([set true] : set bool) by [].
  have h := measurable_fun_ltr (measurable_cst t) mf measurableT mt.
  by rewrite setTI preimage_true in h.
pose F (s : k.-tuple bool) (H : 'M[R]_(k,d)) :=
  (\1_((reserve_row_sign s) @^-1` A) H : R).
have mAs s : measurable ((reserve_row_sign s) @^-1` A).
  have h := reserve_row_sign_measurable s measurableT mA.
  by rewrite setTI in h.
have iF s : Q.-integrable setT (EFin \o F s) := integrable_indic Q (mAs s).
have mF s : measurable_fun setT (F s) := measurable_indic (mAs s).
have F01 s H : 0 <= F s H <= 1.
  rewrite /F indicE.
  rewrite ler0n /=.
  by case: (H \in (reserve_row_sign s) @^-1` A).
pose g H := rademacher_mean (fun s => F s H).
have mg : measurable_fun setT g := measurable_rademacher_mean mF.
have g01 H : 0 <= g H <= 1.
  apply/andP; split.
  - apply: rademacher_mean_ge0 => s; exact: (proj1 (andP (F01 s H))).
  - rewrite -[leRHS](rademacher_mean_cst k 1).
    apply: ler_rademacher_mean => s; exact: (proj2 (andP (F01 s H))).
have bound H : E H -> g H <= B / t.
  move=> EH.
  have eF s : F s H = (t < f (reserve_row_sign s H))%R%:R.
    rewrite /F indicE.
    change ((`[< (t < f (reserve_row_sign s H))%R >])%:R =
      (t < f (reserve_row_sign s H))%R%:R :> R).
    by rewrite asboolb.
  have eg : g H = rademacher_mean (fun s : k.-tuple bool =>
      (t < f (reserve_row_sign s H))%R%:R).
    by rewrite /g /rademacher_mean; congr (_ * _); apply: eq_bigr => s _; exact: eF.
  rewrite eg; apply: le_trans (reserve_rademacher_markov t0 (fun s => f0 _)) _.
  apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
  exact: avg EH.
have c0 : 0 <= B / t by rewrite divr_ge0 // ltW.
have h := reserve_integral_tail Q mE mg g01 c0 bound.
have gi : \int[Q]_H g H = fine (Q A).
  rewrite /g Rintegral_rademacher_mean //.
  have eI s : \int[Q]_H F s H = fine (Q A).
    by rewrite /F reserve_Rintegral_indic // symQ.
  rewrite /rademacher_mean; under eq_bigr do rewrite eI.
  exact: rademacher_mean_cst.
rewrite gi in h.
have QA : Q A = (fine (Q A))%:E by rewrite fineK //; exact: fin_num_measure.
have QE : Q (~` E) = (fine (Q (~` E)))%:E.
  symmetry; apply: fineK; exact: fin_num_measure (measurableC mE).
by rewrite QA QE -EFinD lee_fin.
Qed.

Theorem reserve_linearized_tail (Q : probability 'M[R]_(k,d) R) (L M t : R) :
  (0 < d)%N -> reserve_sign_invariant Q -> 0 <= L -> 0 <= M -> 0 < t ->
  forall b : 'cV[R]_d,
  (Q [set H | (t < opnorm (reserve_linearized_quadratic H b))%R] <=
    Q (~` reserve_intrinsic L M) +
    (40 * Num.sqrt (ln (2 * d%:R)) *
      Num.sqrt (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b / k%:R / t)%:E)%E.
Proof.
move=> d0 symQ L0 M0 t0 b.
apply: reserve_sign_average_tail => //.
- exact: reserve_intrinsic_measurable.
- apply: measurable_opnorm.
  have mD : measurable_fun setT (fun H : 'M[R]_(k,d) => reserve_linearized_quadratic H b).
    apply: reserve_linearized_measurable; [exact: measurable_id | exact: measurable_cst].
  exact/measurable_fun_mxP.
- by move=> H; exact: opnorm_ge0.
- by rewrite !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?frobenius_ge0 ?ler0n.
- by move=> H EH; exact: reserve_linearized_sign_mean.
Qed.

End sign_law_tail.

Section independent_example.
Variable R : realType.

(* A single scalar observation has zero centered Gram matrix. The guarded
   construction therefore returns zero, for every right-hand side. *)
Example singleton_reserve_guard_zero (x b : R) :
  guarded_reserve_correction (const_mx x : 'M[R]_(1,1)) (const_mx b) = 0.
Proof.
have P0 : centering_mx 1 = (0 : 'M[R]_1).
  apply/matrixP => i j; rewrite !ord1 /centering_mx /centering_ones.
  by rewrite !mxE big_ord1 !mxE /=; field.
rewrite /guarded_reserve_correction /centered_covariance P0 mulmx0 mul0mx.
by rewrite unitmxE unitfE det_mx11 mxE eqxx.
Qed.

End independent_example.

Section independent_truncation.
Context {R : realType} {e1 e2} {T1 : measurableType e1} {T2 : measurableType e2}.
Variables (P : probability T1 R) (nu : probability T2 R).

(* Independence is the product measure in the conclusion. Only a uniform
   section bound on the truncation set is integrated. *)
Lemma reserve_product_truncation (A : set (T1 * T2)) (C : set T2) (c : R) :
  measurable A -> measurable C -> 0 <= c ->
  (forall b, C b -> (P (ysection A b) <= c%:E)%E) ->
  ((P \x nu) A <= nu (~` C) + c%:E)%E.
Proof.
move=> mA mC c0 sections.
pose f b := fine (P (ysection A b)).
have ms b : measurable (ysection A b) := measurable_ysection b mA.
have mf : measurable_fun setT f.
  apply: measurableT_comp; first exact: fine_measurable.
  exact: measurable_fun_ysection.
have f01 b : 0 <= f b <= 1 := prob_fine_itv P (ms b).
have bound b : C b -> f b <= c.
  move=> Cb; have h := sections b Cb.
  have pf : P (ysection A b) \is a fin_num by exact: fin_num_measure.
  by rewrite -(fineK pf) lee_fin in h.
have h := reserve_integral_tail nu mC mf f01 c0 bound.
have iff : nu.-integrable setT (EFin \o f).
  have i1 : nu.-integrable setT (EFin \o (fun _ : T2 => (1 : R))).
    exact: finite_measure_integrable_cst.
  apply: (le_integrable measurableT _ _ i1); first exact/measurable_EFinP.
  move=> b _; rewrite /comp !abse_EFin lee_fin !ger0_norm ?(proj1 (andP (f01 b))) //.
  exact: (proj2 (andP (f01 b))).
have pe : ((P \x nu) A = (P \x^ nu) A)%E.
  apply: product_measure_unique => //= B D mB mD.
  by rewrite product_measure2E.
rewrite pe /product_measure2 /=.
have fe b : P (ysection A b) = (f b)%:E.
  by rewrite /f fineK //; exact: fin_num_measure.
have ei : (\int[nu]_b P (ysection A b))%E = (\int[nu]_b f b)%:E.
  under eq_integral do rewrite fe.
  by rewrite /Rintegral fineK //; exact: integrable_fin_num.
rewrite ei.
have ne : nu (~` C) = (fine (nu (~` C)))%:E.
  symmetry; apply: fineK; exact: fin_num_measure (measurableC mC).
by rewrite ne -EFinD lee_fin.
Qed.

End independent_truncation.

Section linearized_independent.
Context {R : realType} {k d : nat}.

Theorem reserve_linearized_independent_tail
    (Q : probability 'M[R]_(k,d) R) (nu : probability 'cV[R]_d R) (L M B t : R) :
  (0 < d)%N -> reserve_sign_invariant Q -> 0 <= L -> 0 <= M -> 0 <= B -> 0 < t ->
  ((Q \x nu) [set z | (t < opnorm (reserve_linearized_quadratic z.1 z.2))%R] <=
    nu [set b | (B < frobenius b)%R] + Q (~` reserve_intrinsic L M) +
    (40 * Num.sqrt (ln (2 * d%:R)) *
      Num.sqrt (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * B / k%:R / t)%:E)%E.
Proof.
move=> d0 symQ L0 M0 B0 t0.
pose a := 40 * Num.sqrt (ln (2 * d%:R)) *
  Num.sqrt (M * quadratic_fourth_constant k L +
    Num.sqrt (k%:R * quadratic_fourth_constant k L)) / k%:R / t.
have a0 : 0 <= a by rewrite /a !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?ler0n ?(ltW t0).
pose E : set 'M[R]_(k,d) := reserve_intrinsic L M.
have mE : measurable E := reserve_intrinsic_measurable L M.
pose q := fine (Q (~` E)).
have qe : Q (~` E) = q%:E.
  rewrite /q; symmetry; apply: fineK; exact: fin_num_measure (measurableC mE).
have q0 : 0 <= q := proj1 (andP (prob_fine_itv Q (measurableC mE))).
pose A : set ('M[R]_(k,d) * 'cV[R]_d) :=
  [set z | t < opnorm (reserve_linearized_quadratic z.1 z.2)].
have mA : measurable A.
  have mf : measurable_fun setT (fun z : 'M[R]_(k,d) * 'cV[R]_d =>
      opnorm (reserve_linearized_quadratic z.1 z.2)).
    apply: measurable_opnorm; apply/measurable_fun_mxP.
    apply: reserve_linearized_measurable; [exact: measurable_fst | exact: measurable_snd].
  have mt : measurable ([set true] : set bool) by [].
  have h := measurable_fun_ltr (measurable_cst t) mf measurableT mt.
  by rewrite setTI preimage_true in h.
pose T := [set b : 'cV[R]_d | B < frobenius b].
have mT : measurable T.
  have mf : measurable_fun [set: 'cV[R]_d] (@frobenius R d 1).
    apply: continuous_measurable_mx; exact: reserve_frobenius_continuous.
  have mt : measurable ([set true] : set bool) by [].
  have h := measurable_fun_ltr (measurable_cst B) mf measurableT mt.
  by rewrite setTI preimage_true in h.
have c0 : 0 <= q + a * B by rewrite addr_ge0 // mulr_ge0.
have h := @reserve_product_truncation R _ _ _ _ Q nu A (~` T) (q + a * B)
  mA (measurableC mT) c0.
have sections b : (~` T) b -> (Q (ysection A b) <= (q + a * B)%:E)%E.
  move=> bT.
  have bB : frobenius b <= B.
    rewrite leNgt; apply/negP => contra; exact: bT contra.
  have ht := reserve_linearized_tail d0 symQ L0 M0 t0 b.
  rewrite -/E qe in ht.
  have he : 40 * Num.sqrt (ln (2 * d%:R)) *
      Num.sqrt (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b / k%:R / t = a * frobenius b.
    by rewrite /a; ring.
  rewrite he -EFinD in ht.
  have secE : ysection A b =
      [set H | t < opnorm (reserve_linearized_quadratic H b)].
    by apply/funext=> H; rewrite /ysection /A /= inE.
  rewrite secE.
  apply: le_trans ht _; rewrite lee_fin lerD2l.
  by apply: ler_wpM2l.
have := h sections; rewrite setCK EFinD addeA -qe /a.
have he : 40 * Num.sqrt (ln (2 * d%:R)) *
    Num.sqrt (M * quadratic_fourth_constant k L +
      Num.sqrt (k%:R * quadratic_fourth_constant k L)) / k%:R / t * B =
  40 * Num.sqrt (ln (2 * d%:R)) *
    Num.sqrt (M * quadratic_fourth_constant k L +
      Num.sqrt (k%:R * quadratic_fourth_constant k L)) * B / k%:R / t by ring.
by rewrite he.
Qed.

End linearized_independent.

Section covariance_event.
Context {R : realType} {k d : nat}.

Definition reserve_covariance_event (eta A h S : R) : set 'M[R]_(k,d) :=
  [set H | [&& opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <= eta,
    opnorm H <= A, frobenius (reserve_mean H) <= h &
    opnorm (\sum_i reserve_feature H i) <= S]].

Lemma reserve_covariance_event_measurable eta A h S :
  measurable (reserve_covariance_event eta A h S).
Proof.
have mnear : measurable_fun [set: 'M[R]_(k,d)]
    (fun H => opnorm (k%:R^-1 *: centered_covariance H - 1%:M)).
  apply: measurable_opnorm; apply/measurable_fun_mxP.
  apply: measurable_addmx; last exact: measurable_cst.
  apply: measurable_scalemx; first exact: measurable_cst.
  apply: reserve_covariance_measurable; exact: measurable_id.
have mn : measurable_fun [set: 'M[R]_(k,d)] (fun H => opnorm H).
  apply: measurable_opnorm => i j; exact: measurable_mxentry.
have mm : measurable_fun [set: 'M[R]_(k,d)] (fun H => frobenius (reserve_mean H)).
  apply: measurable_frobenius_fun; rewrite /reserve_mean.
  apply: measurable_scalemx; first exact: measurable_cst.
  apply: measurable_mulmx; [exact: measurable_trmx | exact: measurable_cst].
have ms : measurable_fun [set: 'M[R]_(k,d)] (fun H => opnorm (\sum_i reserve_feature H i)).
  apply: measurable_opnorm; apply/measurable_fun_mxP.
  have eqs H : \sum_i reserve_feature H i = coef_adj (reserve_feature H) (centering_ones k)^T.
    by rewrite coef_adj_ones.
  under eq_fun do rewrite eqs.
  apply: reserve_coef_adj_measurable; last exact: measurable_cst.
  move=> i; apply: reserve_feature_measurable; exact: measurable_id.
have mf : measurable_fun [set: 'M[R]_(k,d)]
    (fun H => [&& opnorm (k%:R^-1 *: centered_covariance H - 1%:M) <= eta,
      opnorm H <= A, frobenius (reserve_mean H) <= h &
      opnorm (\sum_i reserve_feature H i) <= S]).
  apply: measurable_and; first exact: measurable_fun_ler mnear (measurable_cst eta).
  apply: measurable_and; first exact: measurable_fun_ler mn (measurable_cst A).
  apply: measurable_and; [exact: measurable_fun_ler mm (measurable_cst h) |
    exact: measurable_fun_ler ms (measurable_cst S)].
have mt : measurable ([set true] : set bool) by [].
have m := mf measurableT _ mt.
by rewrite setTI preimage_true in m.
Qed.

Theorem guarded_reserve_on_events (L M eta A h S B : R) (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :
  (0 < k)%N -> 0 <= L -> 0 <= eta -> eta <= 2^-1 ->
  0 <= A -> 0 <= h -> 0 <= S -> 0 <= B ->
  reserve_intrinsic L M H -> reserve_covariance_event eta A h S H -> frobenius b <= B ->
  [ /\ centered_covariance H \in unitmx,
      (centering_ones k)^T *m guarded_reserve_correction H b = 0,
      H^T *m guarded_reserve_correction H b = b,
      frobenius (guarded_reserve_correction H b) <= Num.sqrt (2 / k%:R) * B &
      opnorm (guarded_reserve_quadratic H b - reserve_linearized_quadratic H b) <=
        (2 * B / k%:R) * (L * A * eta + h * S) ].
Proof.
move=> k0 L0 eta0 eta2 A0 h0 S0 B0 [adj rows] /and4P[near HA mh Sh] bB.
have kr0 : (0 : R) < k%:R by rewrite ltr0n.
have ki0 : (0 : R) <= k%:R^-1 by rewrite invr_ge0 ltW.
have near2 := le_trans near eta2.
have [Ku mass moment energy] := centered_correction_bounds b k0 near2.
rewrite /guarded_reserve_correction /guarded_reserve_quadratic Ku.
have vb := centered_potential_bound b k0 near2.
have va := centered_potential_approx b k0 near2.
have vp : frobenius (centered_potential H b) <= 2 * B / k%:R.
  apply: le_trans vb _; by rewrite ler_wpM2r // ler_wpM2l ?ler0n.
have vap : frobenius (centered_potential H b - k%:R^-1 *: b) <= 2 * eta * B / k%:R.
  apply: le_trans va _; apply: ler_wpM2r => //.
  apply: ler_pM; [by rewrite mulr_ge0 ?ler0n ?opnorm_ge0 | exact: frobenius_ge0 |
    by rewrite ler_wpM2l ?ler0n | exact: bB].
have eb := reserve_quadratic_error_bound b k0 L0 adj.
have first : L * opnorm H * frobenius (centered_potential H b - k%:R^-1 *: b) <=
    L * A * (2 * eta * B / k%:R).
  apply: ler_pM; [by rewrite mulr_ge0 ?opnorm_ge0 | exact: frobenius_ge0 |
    by apply: ler_wpM2l | exact: vap].
have second : frobenius (reserve_mean H) * frobenius (centered_potential H b) *
    opnorm (\sum_i reserve_feature H i) <= h * (2 * B / k%:R) * S.
  apply: ler_pM; [by rewrite mulr_ge0 ?frobenius_ge0 | exact: opnorm_ge0 | | exact: Sh].
  apply: ler_pM; [exact: frobenius_ge0 | exact: frobenius_ge0 | exact: mh | exact: vp].
have err : opnorm (reserve_quadratic H b - reserve_linearized_quadratic H b) <=
    (2 * B / k%:R) * (L * A * eta + h * S).
  apply: le_trans eb _; apply: le_trans (lerD first second) _.
  have -> : L * A * (2 * eta * B / k%:R) + h * (2 * B / k%:R) * S =
      (2 * B / k%:R) * (L * A * eta + h * S) by ring.
  exact: lexx.
split => //.
have r0 := frobenius_ge0 (centered_correction H b).
have bound0 : 0 <= Num.sqrt (2 / k%:R) * B by rewrite mulr_ge0 ?sqrtr_ge0.
have sqrt2 : Num.sqrt (2 / k%:R) ^+ 2 = (2 / k%:R : R).
  by rewrite sqr_sqrtr ?divr_ge0 ?ler0n ?(ltW kr0).
have rb : frobenius (centered_correction H b) ^+ 2 <=
    (Num.sqrt (2 / k%:R) * B) ^+ 2.
  rewrite exprMn sqrt2; apply: le_trans energy _.
  have sq : frobenius b ^+ 2 <= B ^+ 2.
    by apply: lerXn2r; rewrite ?nnegrE ?frobenius_ge0.
  rewrite [leRHS]mulrAC.
  apply: ler_wpM2r => //; by apply: ler_wpM2l.
by move: rb; rewrite ler_sqr ?nnegrE.
Qed.

End covariance_event.

Section restricted_sign_tail.
Context {R : realType} {k d : nat}.

(* Restricting the tail to an invariant event avoids charging its complement
   twice when a second, non-invariant covariance event is imposed later. *)
Lemma reserve_sign_restricted_tail (Q : probability 'M[R]_(k,d) R)
    (E : set 'M[R]_(k,d)) (f : 'M[R]_(k,d) -> R) (B t : R) :
  reserve_sign_invariant Q -> measurable E ->
  (forall s H, E (reserve_row_sign s H) <-> E H) ->
  measurable_fun setT f -> (forall H, 0 <= f H) -> 0 <= B -> 0 < t ->
  (forall H, E H -> rademacher_mean (fun s : k.-tuple bool =>
    f (reserve_row_sign s H)) <= B) ->
  (Q (E `&` [set H | (t < f H)%R]) <= (B / t)%:E)%E.
Proof.
move=> symQ mE symE mf f0 B0 t0 avg.
pose g := f \_ E.
have mg : measurable_fun setT g.
  apply/(measurable_restrictT f mE).
  apply: measurable_funS mf => //; exact: subsetT.
have g0 H : 0 <= g H by apply: restrict_ge0 => //.
have avgG H : setT H -> rademacher_mean (fun s : k.-tuple bool =>
    g (reserve_row_sign s H)) <= B.
  move=> _; case: (pselect (E H)) => EH.
  - have eqg s : g (reserve_row_sign s H) = f (reserve_row_sign s H).
      rewrite /g patchT // inE; exact: (proj2 (symE s H) EH).
    rewrite /rademacher_mean; under eq_bigr do rewrite eqg.
    exact: avg EH.
  - have eqg s : g (reserve_row_sign s H) = 0.
      rewrite /g /patch; case: ifP => // /set_mem hs.
      by exfalso; apply: EH; exact: (proj1 (symE s H) hs).
    rewrite /rademacher_mean; under eq_bigr do rewrite eqg.
    by rewrite big1 ?mulr0.
have ht := reserve_sign_average_tail symQ measurableT mg g0 B0 t0 avgG.
rewrite setCT measure0 add0e in ht.
have eqA : [set H | t < g H] = E `&` [set H | t < f H].
  apply/seteqP; split=> H; rewrite /g /patch /=.
  - case: ifP => [/set_mem EH|nEH] hf; first by split.
    by move: hf; rewrite ltNge (ltW t0).
  - move=> [EH hf]; rewrite ifT //; exact: mem_set.
by rewrite eqA in ht.
Qed.

Theorem reserve_linearized_restricted_tail
    (Q : probability 'M[R]_(k,d) R) (L M t : R) :
  (0 < d)%N -> reserve_sign_invariant Q -> 0 <= L -> 0 <= M -> 0 < t ->
  forall b : 'cV[R]_d,
  (Q (reserve_intrinsic L M `&`
      [set H | (t < opnorm (reserve_linearized_quadratic H b))%R]) <=
    (40 * Num.sqrt (ln (2 * d%:R)) *
      Num.sqrt (M * quadratic_fourth_constant k L +
        Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b / k%:R / t)%:E)%E.
Proof.
move=> d0 symQ L0 M0 t0 b.
apply: reserve_sign_restricted_tail => //.
- exact: reserve_intrinsic_measurable.
- exact: reserve_intrinsic_sign.
- apply: measurable_opnorm.
  have mD : measurable_fun setT (fun H : 'M[R]_(k,d) => reserve_linearized_quadratic H b).
    apply: reserve_linearized_measurable; [exact: measurable_id | exact: measurable_cst].
  exact/measurable_fun_mxP.
- by move=> H; exact: opnorm_ge0.
- by rewrite !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?frobenius_ge0 ?ler0n.
- by move=> H EH; exact: reserve_linearized_sign_mean.
Qed.

End restricted_sign_tail.

Section correction_failure.
Context {R : realType} {k d : nat}.

Definition reserve_failure (r u : R) : set ('M[R]_(k,d) * 'cV[R]_d) :=
  [set z | [|| ~~ (centered_covariance z.1 \in unitmx),
    r < frobenius (guarded_reserve_correction z.1 z.2) |
    u < opnorm (guarded_reserve_quadratic z.1 z.2)]].

Lemma reserve_failure_measurable r u : measurable (reserve_failure r u).
Proof.
have mu : measurable_fun [set: 'M[R]_(k,d) * 'cV[R]_d]
    (fun z => centered_covariance z.1 \in unitmx).
  apply: reserve_unitmx_measurable; apply: reserve_covariance_measurable.
  exact: measurable_fst.
have mr : measurable_fun [set: 'M[R]_(k,d) * 'cV[R]_d]
    (fun z => frobenius (guarded_reserve_correction z.1 z.2)).
  apply: measurable_frobenius_fun; apply: guarded_reserve_correction_measurable;
    [exact: measurable_fst | exact: measurable_snd].
have mq : measurable_fun [set: 'M[R]_(k,d) * 'cV[R]_d]
    (fun z => opnorm (guarded_reserve_quadratic z.1 z.2)).
  apply: measurable_opnorm; apply/measurable_fun_mxP.
  apply: guarded_reserve_quadratic_measurable;
    [exact: measurable_fst | exact: measurable_snd].
have mf : measurable_fun [set: 'M[R]_(k,d) * 'cV[R]_d]
    (fun z => [|| ~~ (centered_covariance z.1 \in unitmx),
      r < frobenius (guarded_reserve_correction z.1 z.2) |
      u < opnorm (guarded_reserve_quadratic z.1 z.2)]).
  apply: measurable_or; first exact: measurable_neg.
  apply: measurable_or; [exact: measurable_fun_ltr (measurable_cst r) mr |
    exact: measurable_fun_ltr (measurable_cst u) mq].
have mt : measurable ([set true] : set bool) by [].
have m := mf measurableT _ mt.
by rewrite setTI preimage_true in m.
Qed.

Lemma reserve_failure_success r u (H : 'M[R]_(k,d)) (b : 'cV[R]_d) :
  (0 < k)%N -> ~ reserve_failure r u (H,b) ->
  [ /\ centered_covariance H \in unitmx,
      (centering_ones k)^T *m guarded_reserve_correction H b = 0,
      H^T *m guarded_reserve_correction H b = b,
      frobenius (guarded_reserve_correction H b) <= r &
      opnorm (guarded_reserve_quadratic H b) <= u ].
Proof.
move=> k0 hf.
have hn : ~~ [|| ~~ (centered_covariance H \in unitmx),
    r < frobenius (guarded_reserve_correction H b) |
    u < opnorm (guarded_reserve_quadratic H b)].
  exact/negP.
move: hn; rewrite !negb_or negbK -!leNgt => /and3P[Ku hr hu].
split => //; rewrite /guarded_reserve_correction Ku.
- exact: centered_correction_mass.
- exact: centered_correction_moment.
Qed.

Lemma reserve_failure_subset (L M eta A h S B t : R) (b : 'cV[R]_d) :
  (0 < k)%N -> 0 <= L -> 0 <= eta -> eta <= 2^-1 ->
  0 <= A -> 0 <= h -> 0 <= S -> 0 <= B -> frobenius b <= B ->
  ysection (reserve_failure (Num.sqrt (2 / k%:R) * B)
      (t + (2 * B / k%:R) * (L * A * eta + h * S))) b `<=`
    ((~` reserve_intrinsic L M) `|` (~` reserve_covariance_event eta A h S)) `|`
      (reserve_intrinsic L M `&`
        [set H | t < opnorm (reserve_linearized_quadratic H b)]).
Proof.
move=> k0 L0 eta0 eta2 A0 h0 S0 B0 bB H hf.
case: (pselect (reserve_intrinsic L M H)) => [EH|nE]; last by left; left.
case: (pselect (reserve_covariance_event eta A h S H)) => [GH|nG]; last by left; right.
have [Ku _ _ rb er] := guarded_reserve_on_events k0 L0 eta0 eta2 A0 h0 S0 B0 EH GH bB.
move: hf; rewrite /ysection /reserve_failure /= inE => /or3P[fail|fail|fail].
- by rewrite Ku in fail.
- by move: fail; rewrite ltNge rb.
- right; split => //.
  have tri := opnormD (guarded_reserve_quadratic H b - reserve_linearized_quadratic H b)
    (reserve_linearized_quadratic H b).
  rewrite subrK in tri.
  have bd := le_trans tri (lerD er (lexx (opnorm (reserve_linearized_quadratic H b)))).
  lra.
Qed.

End correction_failure.

Section correction_probability.
Context {R : realType} {k d : nat}.

Definition reserve_tail_coefficient (L M : R) :=
  40 * Num.sqrt (ln (2 * d%:R)) *
    Num.sqrt (M * quadratic_fourth_constant k L +
      Num.sqrt (k%:R * quadratic_fourth_constant k L)) / k%:R.

Lemma reserve_tail_coefficient_ge0 L M : 0 <= reserve_tail_coefficient L M.
Proof.
by rewrite /reserve_tail_coefficient !mulr_ge0 ?invr_ge0 ?sqrtr_ge0 ?ler0n.
Qed.

Theorem reserve_correction_tail (Q : probability 'M[R]_(k,d) R)
    (L M eta A h S B t : R) :
  (0 < k)%N -> (0 < d)%N -> reserve_sign_invariant Q ->
  0 <= L -> 0 <= M -> 0 <= eta -> eta <= 2^-1 ->
  0 <= A -> 0 <= h -> 0 <= S -> 0 <= B -> 0 < t ->
  forall b : 'cV[R]_d, frobenius b <= B ->
  (Q (ysection (reserve_failure (Num.sqrt (2 / k%:R) * B)
      (t + (2 * B / k%:R) * (L * A * eta + h * S))) b) <=
    Q (~` reserve_intrinsic L M) + Q (~` reserve_covariance_event eta A h S) +
    (reserve_tail_coefficient L M * B / t)%:E)%E.
Proof.
move=> k0 d0 symQ L0 M0 eta0 eta2 A0 h0 S0 B0 t0 b bB.
pose E : set 'M[R]_(k,d) := reserve_intrinsic L M.
pose G : set 'M[R]_(k,d) := reserve_covariance_event eta A h S.
pose T := [set H : 'M[R]_(k,d) | t < opnorm (reserve_linearized_quadratic H b)].
have mE : measurable E := reserve_intrinsic_measurable L M.
have mG : measurable G := reserve_covariance_event_measurable eta A h S.
have mT : measurable T.
  have mf : measurable_fun [set: 'M[R]_(k,d)]
      (fun H => opnorm (reserve_linearized_quadratic H b)).
    apply: measurable_opnorm; apply/measurable_fun_mxP.
    apply: reserve_linearized_measurable;
      [exact: measurable_id | exact: measurable_cst].
  have mt : measurable ([set true] : set bool) by [].
  have ht := measurable_fun_ltr (measurable_cst t) mf measurableT mt.
  by rewrite setTI preimage_true in ht.
have mEc := measurableC mE.
have mGc := measurableC mG.
have mU := measurableU _ _ mEc mGc.
have mF := measurableI _ _ mE mT.
have mUF := measurableU _ _ mU mF.
have mb := measurable_ysection b (@reserve_failure_measurable R k d
  (Num.sqrt (2 / k%:R) * B) (t + (2 * B / k%:R) * (L * A * eta + h * S))).
have sub := @reserve_failure_subset R k d L M eta A h S B t b
  k0 L0 eta0 eta2 A0 h0 S0 B0 bB.
apply: le_trans (le_measure Q (mem_set mb) (mem_set mUF) sub) _.
apply: le_trans (measureU2 Q mU mF) _.
apply: leeD; first exact: measureU2.
have tail := reserve_linearized_restricted_tail d0 symQ L0 M0 t0 b.
rewrite -/E -/T in tail.
apply: le_trans tail _; rewrite lee_fin.
have eqc : 40 * Num.sqrt (ln (2 * d%:R)) *
    Num.sqrt (M * quadratic_fourth_constant k L +
      Num.sqrt (k%:R * quadratic_fourth_constant k L)) * frobenius b / k%:R / t =
    reserve_tail_coefficient L M * frobenius b / t.
  by rewrite /reserve_tail_coefficient; ring.
rewrite eqc; apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
apply: ler_wpM2l => //; exact: reserve_tail_coefficient_ge0.
Qed.

(* The right-hand side is random only through a separate probability law.
   Truncation of its norm, rather than a moment bound, is all that is used. *)
Theorem reserve_independent_correction_tail
    (Q : probability 'M[R]_(k,d) R) (nu : probability 'cV[R]_d R)
    (L M eta A h S B t : R) :
  (0 < k)%N -> (0 < d)%N -> reserve_sign_invariant Q ->
  0 <= L -> 0 <= M -> 0 <= eta -> eta <= 2^-1 ->
  0 <= A -> 0 <= h -> 0 <= S -> 0 <= B -> 0 < t ->
  ((Q \x nu) (reserve_failure (Num.sqrt (2 / k%:R) * B)
      (t + (2 * B / k%:R) * (L * A * eta + h * S))) <=
    nu [set b | (B < frobenius b)%R] +
    Q (~` reserve_intrinsic L M) + Q (~` reserve_covariance_event eta A h S) +
    (reserve_tail_coefficient L M * B / t)%:E)%E.
Proof.
move=> k0 d0 symQ L0 M0 eta0 eta2 A0 h0 S0 B0 t0.
pose E : set 'M[R]_(k,d) := reserve_intrinsic L M.
pose G : set 'M[R]_(k,d) := reserve_covariance_event eta A h S.
have mE : measurable E := reserve_intrinsic_measurable L M.
have mG : measurable G := reserve_covariance_event_measurable eta A h S.
pose qe := fine (Q (~` E)).
pose qg := fine (Q (~` G)).
have Ee : Q (~` E) = qe%:E.
  rewrite /qe; symmetry; apply: fineK; exact: fin_num_measure (measurableC mE).
have Ge : Q (~` G) = qg%:E.
  rewrite /qg; symmetry; apply: fineK; exact: fin_num_measure (measurableC mG).
have qe0 : 0 <= qe := proj1 (andP (prob_fine_itv Q (measurableC mE))).
have qg0 : 0 <= qg := proj1 (andP (prob_fine_itv Q (measurableC mG))).
pose c := reserve_tail_coefficient L M * B / t.
have c0 : 0 <= c.
  by rewrite /c divr_ge0 ?mulr_ge0 ?reserve_tail_coefficient_ge0 ?(ltW t0).
pose T := [set b : 'cV[R]_d | B < frobenius b].
have mT : measurable T.
  have mf : measurable_fun [set: 'cV[R]_d] (@frobenius R d 1).
    apply: continuous_measurable_mx; exact: reserve_frobenius_continuous.
  have mt : measurable ([set true] : set bool) by [].
  have ht := measurable_fun_ltr (measurable_cst B) mf measurableT mt.
  by rewrite setTI preimage_true in ht.
have bound0 : 0 <= qe + qg + c by rewrite !addr_ge0.
have htr := @reserve_product_truncation R _ _ _ _ Q nu
  (reserve_failure (Num.sqrt (2 / k%:R) * B)
    (t + (2 * B / k%:R) * (L * A * eta + h * S))) (~` T) (qe + qg + c)
  (reserve_failure_measurable _ _) (measurableC mT) bound0.
have sections b : (~` T) b ->
    (Q (ysection (reserve_failure (Num.sqrt (2 / k%:R) * B)
      (t + (2 * B / k%:R) * (L * A * eta + h * S))) b) <=
      (qe + qg + c)%:E)%E.
  move=> bT.
  have bB : frobenius b <= B.
    rewrite leNgt; apply/negP => contra; exact: bT contra.
  have hb := @reserve_correction_tail Q L M eta A h S B t
    k0 d0 symQ L0 M0 eta0 eta2 A0 h0 S0 B0 t0 b bB.
  by rewrite -/E -/G Ee Ge -!EFinD in hb.
have ht := htr sections.
by rewrite setCK !EFinD !addeA -Ee -Ge in ht.
Qed.

End correction_probability.

Section nonsingular_example.
Variable R : realType.

(* For opposite scalar observations the guard is active. The correction
   enforces the prescribed first moment while adding no quadratic term. *)
Example two_rows_guarded_reserve (b : 'cV[R]_1) :
  let H : 'M[R]_(2,1) := \col_i (if i == 0 then 1 else -1) in
  [ /\ centered_covariance H \in unitmx,
      guarded_reserve_correction H b = 2^-1 *: (H *m b) &
      guarded_reserve_quadratic H b = 0 ].
Proof.
move=> H.
have mass : (centering_ones 2)^T *m H = 0.
  apply/matrixP => i j; rewrite !ord1 mxE /centering_ones /H.
  by rewrite !big_ord_recr big_ord0 /= !mxE /=; ring.
have PH : centering_mx 2 *m H = H.
  by rewrite /centering_mx mulmxBl mul1mx -scalemxAl -mulmxA mass
    mulmx0 scaler0 subr0.
have K : centered_covariance H = 2%:M.
  rewrite /centered_covariance -mulmxA PH.
  apply/matrixP => i j; rewrite !ord1 mxE /H.
  by rewrite !big_ord_recr big_ord0 /= !mxE /=; ring.
have Ku : centered_covariance H \in unitmx.
  by rewrite K unitmxE det_mx11 mxE eqxx /= unitfE pnatr_eq0.
split => //.
- rewrite /guarded_reserve_correction Ku.
  exact: two_rows_centered_correction.
- rewrite /guarded_reserve_quadratic Ku.
  exact: two_rows_quadratic_correction_zero.
Qed.

End nonsingular_example.
