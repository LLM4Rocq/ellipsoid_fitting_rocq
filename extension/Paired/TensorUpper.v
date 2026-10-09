(* A finite tensorization constant for the latent-sign law, at Stdlib's R:
   item T of phase 10 (the review of the phase 9 release, section 7.3).
   For 0 <= s <= 1 and the uniform law mu, the law P of a point, of
   density rho against the product Q of d copies of mu, satisfies the
   tensorization inequality (12) of the frozen LatentTensorization with
   T_0 = 2 ((1 + s) / (1 - 3 s / 7))^d (latent_tensorization_finite).

   1. On the box, -3/7 <= h <= 1 gives
      L = (1/2) (1 - 3 s / 7)^d <= rho <= U = (1 + s)^d
      (latent_density_lower, latent_density_upper); L > 0 even at s = 1.
   2. At s = 0 the density is 1 (latent_density0), so the frozen
      quantities at s = 0 are those of the product law Q:
      latent_point_expectation 0 mu d g is int g dQ, the conditional
      expectation given X_-j is int g (x with x_j := y) dmu(y) and the
      conditional variance is the variance of y |-> g (x with x_j := y)
      under mu (latent_cond_variance0).
   3. Efron-Stein for Q (efron_stein of library/probability/efron_stein.v,
      with the variances of probability.v identified with the real ones by
      variance_bounded): Var_Q f <= sum_j E_Q Var_Q (f | X_-j)
      (latent_efron_stein).
   4. Var_P f <= E_P (f - E_Q f)^2 <= U E_Q (f - E_Q f)^2 = U Var_Q f
      (latent_variance_le).
   5. E_P Var_P (f | X_-j) = E_Q [Z Var_P (f | X_-j)] with Z the
      denominator of the conditional expectation, since the conditional
      variance does not depend on x_j (latent_expectation_indep of
      Paired/Conditional); and Z Var_P (f | X_-j) =
      int (f - E_P (f | X_-j))^2 rho dmu >= L Var_Q (f | X_-j) on the box
      (latent_cond_variance_weight). So
      E_P Var_P (f | X_-j) >= L E_Q Var_Q (f | X_-j)
      (latent_cond_variance_ge).
   Hence Var_P f <= (U / L) sum_j E_P Var_P (f | X_-j), and U / L = T_0. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import exp.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral hoelder probability.
From GaussianAnalysis.probability Require Import lindeberg moments efron_stein.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions LatentSignScope.
From EllipsoidUniversality Require Import LatentTensorization LatentTensorUpper.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Paired Require Import Uniform Law LatentSign Scope.
From EllipsoidUniversality.Paired Require Import Tensorization Conditional.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 0. Arithmetic. *)

Lemma factor_bounds {RT : realType} (s h : RT) :
  0 <= s <= 1 -> - (3%:R / 7%:R) <= h <= 1 ->
  [/\ 0 <= 1 + s * h, 1 + s * h <= 1 + s, 1 - 3%:R * s / 7%:R <= 1 + s * h,
      0 <= 1 + - s * h & 1 + - s * h <= 1 + s].
Proof. by move=> /andP[s0 s1] /andP[h1 h2]; split; nra. Qed.

Lemma lower_factor_ge0 {RT : realType} (s : RT) :
  0 <= s <= 1 -> 0 <= 1 - 3%:R * s / 7%:R.
Proof. by move=> /andP[s0 s1]; lra. Qed.

Lemma lower_factor_gt0 {RT : realType} (s : RT) :
  0 <= s <= 1 -> 0 < 1 - 3%:R * s / 7%:R.
Proof. by move=> /andP[s0 s1]; lra. Qed.

Lemma sq_identity {RT : realType} (A c : RT) :
  A - 2%:R * c * c + c ^+ 2 = A - c ^+ 2.
Proof. by ring. Qed.

Lemma sub_sq_le {RT : realType} (a b : RT) : a - b ^+ 2 <= a.
Proof. by rewrite lerBlDr lerDl sqr_ge0. Qed.

Lemma mul_div_comm {RT : realType} (U S L : RT) : U * (S * L^-1) = U / L * S.
Proof. by ring. Qed.

Lemma tensor_constantE {RT : realType} (s : RT) (d : nat) :
  0 < 1 - 3%:R * s / 7%:R ->
  (1 + s) ^+ d / (2^-1 * (1 - 3%:R * s / 7%:R) ^+ d) =
  2%:R * ((1 + s) / (1 - 3%:R * s / 7%:R)) ^+ d.
Proof.
move=> h; rewrite expr_div_n.
have hn : (1 - 3%:R * s / 7%:R) ^+ d != 0 by rewrite expf_neq0 // gt_eqF.
by field.
Qed.

Lemma var_le_sqr_dev {RT : realType} (A B c : RT) :
  A - B ^+ 2 <= A - 2%:R * c * B + c ^+ 2.
Proof. by have := sqr_ge0 (B - c); nra. Qed.

(* 1. The density on the box. *)

Section density_bounds.
Variables (s : R) (d : nat).
Hypothesis hs : 0 <= s <= 1.

Lemma latent_density_upper (x : paper_main_sample 1 d) : latent_box d x ->
  latent_sample_density s 1 d x <= (1 + s) ^+ d.
Proof.
move=> bx; rewrite latent_densityE /latent_prod.
have pc (c : R) : \prod_(k < 1 * d) c = c ^+ d.
  by rewrite prodr_const card_ord mul1n.
have hb (a : R) : (a = s \/ a = (- s)%R) ->
    \prod_(k < 1 * d) (1 + a * paired_kernel (tnth x k)) <= (1 + s) ^+ d.
  move=> ha; rewrite -pc.
  apply: ler_prod => k _.
  have [f1 f2 _ f4 f5] := factor_bounds s _ hs (paired_kernel_range _ (bx k)).
  by case: ha => ->; apply/andP; split.
have e2 : (1 + s) ^+ d = ((1 + s) ^+ d + (1 + s) ^+ d) / 2%:R :> RR.
  by field.
rewrite [X in _ <= X]e2; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
by apply: lerD; apply: hb; [left|right].
Qed.

Lemma latent_density_lower (x : paper_main_sample 1 d) : latent_box d x ->
  2^-1 * (1 - 3%:R * s / 7%:R) ^+ d <= latent_sample_density s 1 d x.
Proof.
move=> bx; rewrite latent_densityE /latent_prod.
have pc (c : R) : \prod_(k < 1 * d) c = c ^+ d.
  by rewrite prodr_const card_ord mul1n.
have h1 : (1 - 3%:R * s / 7%:R) ^+ d <=
    \prod_(k < 1 * d) (1 + s * paired_kernel (tnth x k)).
  rewrite -pc.
  apply: ler_prod => k _.
  have [f1 f2 f3 _ _] := factor_bounds s _ hs (paired_kernel_range _ (bx k)).
  by rewrite f3 lower_factor_ge0.
have h2 : 0 <= \prod_(k < 1 * d) (1 + (- s)%R * paired_kernel (tnth x k)).
  apply: prodr_ge0 => k _.
  by have [_ _ _ f4 _] := factor_bounds s _ hs (paired_kernel_range _ (bx k)).
rewrite mulrC; apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
by apply: le_trans h1 _; rewrite lerDl.
Qed.

End density_bounds.

(* 2. The product law: the frozen quantities at s = 0. *)

Lemma latent_density0 d (x : paper_main_sample 1 d) :
  latent_sample_density 0%R 1 d x = 1.
Proof.
rewrite latent_densityE /latent_prod.
have e (a : R) : a = 0 ->
    \prod_(k < 1 * d) (1 + a * paired_kernel (tnth x k)) = 1.
  by move=> ->; apply: big1 => k _; rewrite mul0r addr0.
by rewrite (e 0%R) // (e (- 0%R)%R) ?oppr0 //; field.
Qed.

Section product_law.
Variables (mu : probability (measurableTypeR R) R) (d : nat).
Hypothesis hmu : paired_uniform_spec mu.

Local Notation Q := (universality_sample_law (fun=> mu) 1 d).

Lemma latent_expectation_zero (g : paper_main_sample 1 d -> R) :
  latent_point_expectation 0%R mu d g = \int[Q]_x (g x : RR).
Proof.
by apply: eq_Rintegral => x _; rewrite latent_density0 mulr1.
Qed.

Lemma latent_expectationQ (s : R) (g : paper_main_sample 1 d -> R) :
  latent_point_expectation s mu d g =
  latent_point_expectation 0%R mu d
    (fun x => g x * latent_sample_density s 1 d x).
Proof. by rewrite latent_expectation_zero. Qed.

Let mu1 : \int[mu]_y (1 : RR) = 1.
Proof.
by rewrite Rintegral_cst // -[X in fine X]/(mu setT) probability_setT /= mul1r.
Qed.

Lemma latent_cond_expectation0 (j : nat) (g : paper_main_sample 1 d -> R) x :
  latent_cond_expectation 0%R mu d j g x =
  \int[mu]_y (g (latent_replace d j x y) : RR).
Proof.
rewrite /latent_cond_expectation.
under eq_Rintegral do rewrite latent_density0 mulr1.
have -> : \int[mu]_y
    (latent_sample_density 0%R 1 d (latent_replace d j x y) : RR) =
    \int[mu]_y (1 : RR).
  by apply: eq_Rintegral => y _; exact: latent_density0.
by rewrite mu1; exact: divr1.
Qed.

Lemma latent_cond_variance0 (j : nat) (g : paper_main_sample 1 d -> R) x :
  latent_cond_variance 0%R mu d j g x =
  \int[mu]_y (g (latent_replace d j x y) ^+ 2 : RR) -
  (\int[mu]_y (g (latent_replace d j x y) : RR)) ^+ 2.
Proof. by rewrite /latent_cond_variance !latent_cond_expectation0. Qed.

End product_law.

(* 3. Efron-Stein for the product law. *)

Lemma sqr_le_bound {RT : realType} (a M : RT) : `|a| <= M -> `|a ^+ 2| <= M ^+ 2.
Proof.
move=> aM; rewrite normrX; apply: lerXn2r; rewrite ?nnegrE ?normr_ge0 //.
exact: le_trans (normr_ge0 _) aM.
Qed.

Lemma variance_bounded d' (T : measurableType d') (RT : realType)
    (P : probability T RT) (X : T -> RT) (M : RT) :
  measurable_fun setT X -> (forall x, `|X x| <= M) ->
  'V_P[X] = (\int[P]_x (X x ^+ 2) - (\int[P]_x X x) ^+ 2)%:E.
Proof.
move=> mX XM.
have iX := integrable_prob_bounded' _ _ _ P X M mX XM.
have mX2 : measurable_fun setT (fun x => X x ^+ 2) by exact: measurable_funX.
have iX2 := integrable_prob_bounded' _ _ _ P _ _ mX2 (fun x => sqr_le_bound _ _ (XM x)).
rewrite varianceT; set m := fine _.
have em : m = \int[P]_x X x by [].
have mXm : measurable_fun setT (fun x => (X x - m) ^+ 2).
  by apply: measurable_funX; apply: measurable_funB => //; exact: measurable_cst.
have XmM x : `|X x - m| <= M + `|m|.
  by apply: le_trans (ler_normB _ _) _; rewrite lerD2r.
have iXm := integrable_prob_bounded' _ _ _ P _ _ mXm
  (fun x => sqr_le_bound _ _ (XmM x)).
have -> : (\int[P]_x ((X x - m) ^+ 2)%:E)%E = (\int[P]_x ((X x - m) ^+ 2))%:E.
  by rewrite /Rintegral fineK //; exact: (integrable_fin_num measurableT iXm).
congr EFin.
have iZX : P.-integrable setT (EFin \o (fun x => (- (2%:R * m)) * X x)).
  apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT (- (2%:R * m)) iX)).
  by move=> x _ /=; rewrite EFinM.
have i3 : P.-integrable setT
    (EFin \o (fun x => X x ^+ 2 + (- (2%:R * m)) * X x)).
  apply: (eq_integrable measurableT _ _ _ (integrableD measurableT iX2 iZX)).
  by move=> x _ /=; rewrite EFinD.
have ic : P.-integrable setT (EFin \o (fun _ : T => m ^+ 2)).
  exact: finite_measure_integrable_cst.
transitivity (\int[P]_x (X x ^+ 2 + (- (2%:R * m)) * X x + m ^+ 2)).
  by apply: eq_Rintegral => x _; ring.
rewrite (RintegralD measurableT i3 ic) (RintegralD measurableT iX2 iZX).
rewrite (RintegralZl _ measurableT iX) Rintegral_cst //.
rewrite -[X in fine X]/(P setT) probability_setT /= mulr1 -em.
by ring.
Qed.

Lemma Rintegral_bound d' (T : measurableType d') (RT : realType)
    (P : probability T RT) (g : T -> RT) (M : RT) :
  measurable_fun setT g -> (forall x, `|g x| <= M) -> `|\int[P]_x g x| <= M.
Proof.
move=> mg gM.
have ig := integrable_prob_bounded' _ _ _ P g M mg gM.
have cM (c : RT) : \int[P]_x (c : RT) = c.
  by rewrite Rintegral_cst // -[X in fine X]/(P setT) probability_setT /= mulr1.
have ic (c : RT) : P.-integrable setT (EFin \o (fun _ : T => c)).
  exact: finite_measure_integrable_cst.
rewrite ler_norml; apply/andP; split.
  rewrite -[X in X <= _](cM (- M)).
  apply: (le_Rintegral measurableT (ic (- M)) ig) => x _.
  by have := gM x; rewrite ler_norml => /andP[].
rewrite -[X in _ <= X](cM M).
apply: (le_Rintegral measurableT ig (ic M)) => x _.
by have := gM x; rewrite ler_norml => /andP[].
Qed.

Lemma latent_replace_tuple_set d (i : 'I_(1 * d)) (x : paper_main_sample 1 d) t :
  latent_replace d i x t = tuple_set x i t.
Proof. by apply: eq_from_tnth => k; rewrite !tnth_mktuple. Qed.

Section efron.
Variables (mu : probability (measurableTypeR R) R) (d : nat).
Hypothesis hmu : paired_uniform_spec mu.

Local Notation Q := (universality_sample_law (fun=> mu) 1 d).

Let h0 : 0 <= (0%R : R) <= 1. Proof. by rewrite lexx ler01. Qed.

(* The conditional variance at s = 0 is bounded by 2 M^2. *)
Lemma latent_cond_variance0_bound (j : nat) (f : paper_main_sample 1 d -> R)
    (M : R) x :
  measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= M) ->
  `|latent_cond_variance 0%R mu d j f x| <= M ^+ 2 + M ^+ 2.
Proof.
move=> mf fM; rewrite latent_cond_variance0.
have mr : measurable_fun setT (fun y : RR => latent_replace d j x y).
  apply/measurable_fun_tnthP => k.
  apply: (eq_measurable_fun (fun y : RR =>
    if (k == j :> nat) then y else tnth x k)).
    by move=> y _; rewrite /= tnth_mktuple.
  by case: (k == j :> nat); [exact: measurable_id | exact: measurable_cst].
have mG : measurable_fun setT (fun y : RR => f (latent_replace d j x y) : RR).
  exact: measurableT_comp mf mr.
have mG2 : measurable_fun setT (fun y : RR => f (latent_replace d j x y) ^+ 2 : RR).
  exact: measurable_funX.
apply: le_trans (ler_normB _ _) _; apply: lerD.
  exact: (Rintegral_bound _ _ _ mu _ _ mG2 (fun y => sqr_le_bound _ _ (fM _))).
exact: (sqr_le_bound _ _ (Rintegral_bound _ _ _ mu _ _ mG (fun y => fM _))).
Qed.

(* Var_Q f <= sum_j E_Q Var_Q (f | X_-j). *)
Lemma latent_efron_stein (f : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= M) ->
  latent_variance 0%R mu d f <=
  \sum_(j < d) latent_point_expectation 0%R mu d (latent_cond_variance 0%R mu d j f).
Proof.
move=> mf fM.
have mf2 : measurable_fun setT (fun z => f z ^+ 2 : RR) by exact: measurable_funX.
have if2 : Q.-integrable setT (EFin \o (fun z => f z ^+ 2 : RR)).
  exact: (integrable_prob_bounded' _ _ _ Q _ _ mf2 (fun z => sqr_le_bound _ _ (fM z))).
have F2 : f \in Lfun Q 2%:E := integrable_sqr_Lfun2 mf if2.
have es := efron_stein F2.
have eL : ('V_Q[f] = (latent_variance 0%R mu d f)%:E)%E.
  by rewrite (variance_bounded _ _ _ Q f M mf fM) /latent_variance
    !latent_expectation_zero.
have eR (i : 'I_(1 * d)) :
    (\int[Q]_x 'V_mu[fun t => f (tuple_set x i t)] =
     (latent_point_expectation 0%R mu d (latent_cond_variance 0%R mu d i f))%:E)%E.
  have id : (i < d)%N by rewrite -[X in (_ < X)%N]mul1n ltn_ord.
  have [_ mCV] := measurable_latent_cond 0%R mu d i h0 hmu id f M mf fM.
  have eV x : ('V_mu[fun t => f (tuple_set x i t)] =
      (latent_cond_variance 0%R mu d i f x)%:E)%E.
    have mG : measurable_fun setT (fun t : RR => f (tuple_set x i t) : RR).
      apply: measurableT_comp mf _.
      apply/measurable_fun_tnthP => k.
      apply: (eq_measurable_fun (fun y : RR => if k == i then y else tnth x k)).
        by move=> y _; rewrite /= tnth_mktuple.
      by case: (k == i); [exact: measurable_id | exact: measurable_cst].
    rewrite (variance_bounded _ _ _ mu _ M mG (fun t => fM _)).
    rewrite latent_cond_variance0.
    by congr EFin.
  under eq_integral do rewrite eV.
  rewrite latent_expectation_zero /Rintegral fineK //.
  exact: (integrable_fin_num measurableT (integrable_prob_bounded' _ _ _ Q _ _ mCV
    (fun x => latent_cond_variance0_bound i f M x mf fM))).
rewrite -lee_fin -eL.
apply: (le_trans es).
rewrite (eq_bigr _ (fun i _ => eR i)) sumEFin lee_fin.
pose a (j : nat) := latent_point_expectation 0%R mu d (latent_cond_variance 0%R mu d j f).
have -> : \sum_(i < 1 * d) a i = \sum_(j < d) a j.
  by rewrite -!(big_mkord xpredT a) mul1n.
by [].
Qed.

End efron.

(* 4 and 5. The two comparisons. *)

Section compare.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).

Local Notation E := (latent_point_expectation s mu d).
Local Notation EQ := (latent_point_expectation 0%R mu d).
Local Notation rho := (latent_sample_density s 1 d).

Let h0 : 0 <= (0%R : R) <= 1. Proof. by rewrite lexx ler01. Qed.

Let U := (1 + s) ^+ d.
Let L := 2^-1 * (1 - 3%:R * s / 7%:R) ^+ d.

Let U0 : 0 <= U.
Proof. by rewrite /U exprn_ge0 // addr_ge0 //; case/andP: hs. Qed.

Let L0 : 0 < L.
Proof. by rewrite /L mulr_gt0 ?invr_gt0 ?ltr0n // exprn_gt0 // lower_factor_gt0. Qed.

(* E (f - c)^2 for any parameter s'. *)
Let sqr_dev (s' : R) (f : paper_main_sample 1 d -> R) (M c : R) :
  0 <= s' <= 1 -> measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= M) ->
  latent_point_expectation s' mu d (fun x => (f x - c) ^+ 2) =
  latent_point_expectation s' mu d (fun x => f x ^+ 2) -
  2%:R * c * latent_point_expectation s' mu d f + c ^+ 2.
Proof.
move=> hs' mf fM.
have mf2 : measurable_fun setT (fun z => f z ^+ 2 : RR) by exact: measurable_funX.
have f2M z : `|f z ^+ 2| <= M ^+ 2 := sqr_le_bound _ _ (fM z).
have mcf : measurable_fun setT (fun z => (- (2%:R * c)) * f z : RR).
  by apply: measurable_funM => //; exact: measurable_cst.
have cfM z : `|(- (2%:R * c)) * f z| <= `|2%:R * c| * M.
  by rewrite normrM normrN ler_wpM2l // fM.
have m12 : measurable_fun setT (fun z => f z ^+ 2 + (- (2%:R * c)) * f z : RR).
  exact: measurable_funD.
have b12 z : `|f z ^+ 2 + (- (2%:R * c)) * f z| <= M ^+ 2 + `|2%:R * c| * M.
  by apply: le_trans (ler_normD _ _) _; apply: lerD.
have mc : measurable_fun setT (fun _ : paper_main_sample 1 d => c ^+ 2 : RR).
  exact: measurable_cst.
have bc (z : paper_main_sample 1 d) : `|(fun=> c ^+ 2 : RR) z| <= `|c ^+ 2| by [].
have -> : (fun x => (f x - c) ^+ 2) =
    (fun x => (f x ^+ 2 + (- (2%:R * c)) * f x) + (fun=> c ^+ 2) x).
  by apply/funext => x; rewrite /=; ring.
rewrite (latent_expectationD s' mu d hs' hmu _ _ _ _ m12 b12 mc bc).
rewrite (latent_expectationD s' mu d hs' hmu _ _ _ _ mf2 f2M mcf cfM).
rewrite (latent_expectationZ s' mu d hs' hmu _ _ _ mf fM).
rewrite (latent_expectation_cst s' mu d hs' hmu).
by ring.
Qed.

(* Var_P f <= U Var_Q f. *)
Lemma latent_variance_le (f : paper_main_sample 1 d -> R) (M : R) :
  measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= M) ->
  latent_variance s mu d f <= (1 + s) ^+ d * latent_variance 0%R mu d f.
Proof.
move=> mf fM.
set c := EQ f.
have h1 : latent_variance s mu d f <= E (fun x => (f x - c) ^+ 2).
  rewrite (sqr_dev s f M c hs mf fM) /latent_variance.
  exact: var_le_sqr_dev.
have e2 : EQ (fun x => (f x - c) ^+ 2) = latent_variance 0%R mu d f.
  rewrite (sqr_dev 0%R f M c h0 mf fM) /latent_variance -/c.
  exact: sq_identity.
have fcM z : `|f z - c| <= M + `|c|.
  by apply: le_trans (ler_normB _ _) _; rewrite lerD2r.
have mfc : measurable_fun setT (fun x => (f x - c) ^+ 2 : RR).
  by apply: measurable_funX; apply: measurable_funB => //; exact: measurable_cst.
have fc2 z : `|(f z - c) ^+ 2| <= (M + `|c|) ^+ 2 := sqr_le_bound _ _ (fcM z).
apply: le_trans h1 _.
rewrite latent_expectationQ -e2 -(latent_expectationZ 0%R mu d h0 hmu _ _ _ mfc fc2).
have mr : measurable_fun setT (rho : paper_main_sample 1 d -> RR).
  have -> : (rho : paper_main_sample 1 d -> RR) =
      (fun x => (latent_prod s d x + latent_prod (- s)%R d x) / 2%:R).
    by apply/funext => x; rewrite latent_densityE.
  apply: measurable_funM; last exact: measurable_cst.
  by apply: measurable_funD; exact: measurable_latent_prod.
apply: (latent_expectation_le 0%R mu d h0 hmu _ _ ((M + `|c|) ^+ 2 * U)).
- exact: measurable_funM.
- by apply: measurable_funM => //; exact: measurable_cst.
- move=> x bx; have ru := latent_density_upper s d hs x bx.
  have r0 : 0 <= rho x := latent_density_ge0 s d hs x bx.
  split.
    by rewrite normrM (ger0_norm r0); apply: ler_pM => //.
  rewrite normrM (ger0_norm U0) mulrC.
  exact: (ler_wpM2r U0 (fc2 x)).
- move=> x bx; rewrite mulrC; apply: (ler_wpM2r (sqr_ge0 _)).
  exact: latent_density_upper.
Qed.

(* E_P Var_P (f | X_-j) >= L E_Q Var_Q (f | X_-j). *)
Lemma latent_cond_variance_ge (j : nat) (f : paper_main_sample 1 d -> R) (M : R) :
  (j < d)%N -> measurable_fun setT (f : _ -> RR) -> (forall z, `|f z| <= M) ->
  2^-1 * (1 - 3%:R * s / 7%:R) ^+ d * EQ (latent_cond_variance 0%R mu d j f) <=
  E (latent_cond_variance s mu d j f).
Proof.
move=> jd mf fM.
set CV := latent_cond_variance s mu d j f.
set CV0 := latent_cond_variance 0%R mu d j f.
pose Zf x := \int[mu]_y (rho (latent_replace d j x y) : RR).
have [_ mCV] := measurable_latent_cond s mu d j hs hmu jd f M mf fM.
have [_ mCV0] := measurable_latent_cond 0%R mu d j h0 hmu jd f M mf fM.
have mZ : measurable_fun setT Zf := measurable_latent_cond_den s mu d j hs hmu jd.
have mf2 : measurable_fun setT (fun z => f z ^+ 2 : RR) by exact: measurable_funX.
have f2M z : `|f z ^+ 2| <= M ^+ 2 := sqr_le_bound _ _ (fM z).
have CVb x : latent_box d x -> 0 <= CV x <= M ^+ 2.
  move=> bx; rewrite (latent_cond_variance_ge0 s mu d j hs hmu jd f M x mf fM bx).
  apply: le_trans (sub_sq_le _ _) _; apply: le_trans (ler_norm _) _.
  exact: (latent_cond_expectation_bound s mu d j hs hmu jd _ _ x mf2 f2M bx).
pose b0 x := latent_box_ind d (latent_replace d j x 0).
have mb0 : measurable_fun setT (b0 : _ -> RR).
  exact: measurableT_comp (measurable_latent_box_ind d)
    (measurable_latent_replace d j jd 0).
pose g x := CV x * b0 x.
have mg : measurable_fun setT (g : _ -> RR) by exact: measurable_funM.
have CV_rep x t : CV (latent_replace d j x t) = CV x.
  by rewrite /CV /latent_cond_variance !latent_cond_expectation_replace.
have g_rep x t : g (latent_replace d j x t) = g x.
  by rewrite /g /b0 CV_rep latent_replace_idem.
have b00 : `|0 : RR| <= Num.sqrt 3%:R by rewrite normr0 sqrtr_ge0.
have gb x : `|g x| <= M ^+ 2.
  rewrite /g /b0; have [bx|nb] := pselect (latent_box d (latent_replace d j x 0)).
    rewrite latent_box_ind1 // mulr1 -(CV_rep x 0).
    by have /andP[c0 c1] := CVb _ bx; rewrite ger0_norm.
  by rewrite latent_box_ind0 // mulr0 normr0 sqr_ge0.
have gCV x : latent_box d x -> g x = CV x.
  move=> bx; rewrite /g /b0 latent_box_ind1 ?mulr1 //.
  exact: latent_box_replace.
have e1 : E CV = E g.
  by apply: (latent_expectation_eq s mu d hmu CV g mCV mg) => x bx; rewrite gCV.
have e2 : E g = EQ (fun x => g x * Zf x).
  rewrite (latent_expectation_indep s mu d j hs hmu jd g (M ^+ 2) mg gb g_rep).
  by rewrite latent_expectation_zero.
have hpt x : latent_box d x -> L * CV0 x <= g x * Zf x.
  move=> bx; rewrite gCV // /CV0 (latent_cond_variance0 mu d j f x).
  apply: (latent_cond_variance_weight s mu d j hs hmu jd f M L x mf fM bx
    (ltW L0)) => y yc.
  by apply: latent_density_lower => //; exact: latent_box_replace.
have bZ x : latent_box d x -> 0 <= Zf x <= U.
  move=> bx; rewrite (ltW (latent_cond_den_gt0 s mu d j hs hmu jd x bx)) /=.
  apply: (latent_cond_den_le s mu d j hmu jd U x) => y yc.
  by apply: latent_density_upper => //; exact: latent_box_replace.
have CV0b x : `|CV0 x| <= M ^+ 2 + M ^+ 2.
  exact: (latent_cond_variance0_bound mu d j f M x mf fM).
rewrite e1 e2 -(latent_expectationZ 0%R mu d h0 hmu L CV0 _ mCV0 CV0b).
apply: (latent_expectation_le 0%R mu d h0 hmu _ _
  (L * (M ^+ 2 + M ^+ 2) + M ^+ 2 * U)).
- by apply: measurable_funM => //; exact: measurable_cst.
- exact: measurable_funM.
- move=> x bx; have /andP[z0 zU] := bZ x bx.
  have hL : `|L * CV0 x| <= L * (M ^+ 2 + M ^+ 2).
    have L0' : 0 <= L := ltW L0.
    by rewrite normrM (gtr0_norm L0); exact: (ler_wpM2l L0' (CV0b x)).
  have hg : `|g x * Zf x| <= M ^+ 2 * U.
    by rewrite normrM (ger0_norm z0); apply: ler_pM => //; exact: gb.
  have p1 : 0 <= L * (M ^+ 2 + M ^+ 2).
    by apply: le_trans (normr_ge0 _) hL.
  have p2 : 0 <= M ^+ 2 * U by apply: le_trans (normr_ge0 _) hg.
  split.
    by apply: le_trans hL _; rewrite lerDl.
  by apply: le_trans hg _; rewrite lerDr.
- exact: hpt.
Qed.

End compare.

(* Var_P f <= T_0 sum_j E_P Var_P (f | X_-j), with T_0 = U / L. *)
Theorem latent_tensorization_finite (s : R)
    (mu : probability (measurableTypeR R) R) (d : nat) :
  0 <= s <= 1 -> paired_uniform_spec mu ->
  latent_tensorization s mu d (latent_tensor_constant s d).
Proof.
move=> hs hmu f mf [M fM].
have L0 : 0 < 2^-1 * (1 - 3%:R * s / 7%:R) ^+ d :> RR.
  by rewrite mulr_gt0 ?invr_gt0 ?ltr0n // exprn_gt0 // lower_factor_gt0.
have U0 : 0 <= (1 + s) ^+ d :> RR.
  by rewrite exprn_ge0 // addr_ge0 //; case/andP: hs.
have h1 := latent_variance_le s mu d hs hmu f M mf fM.
have h2 := latent_efron_stein mu d hmu f M mf fM.
have h3 (j : 'I_d) :
    latent_point_expectation 0%R mu d (latent_cond_variance 0%R mu d j f) <=
    latent_point_expectation s mu d (latent_cond_variance s mu d j f) /
    (2^-1 * (1 - 3%:R * s / 7%:R) ^+ d).
  rewrite ler_pdivlMr // mulrC.
  exact: (latent_cond_variance_ge s mu d hs hmu j f M (ltn_ord j) mf fM).
apply: le_trans h1 _.
apply: le_trans (ler_wpM2l U0 h2) _.
apply: le_trans (ler_wpM2l U0 (ler_sum _ (fun j _ => h3 j))) _.
rewrite -mulr_suml mul_div_comm (tensor_constantE _ _ (lower_factor_gt0 _ hs)).
by [].
Qed.
