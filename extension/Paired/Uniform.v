(* The uniform law on [-sqrt 3, sqrt 3], the rescaled Legendre polynomial
   h(x) = P_4(x / sqrt 3), and the laws lam_a = (1 + a h) mu, at Stdlib's R:
   item P1 of phase 6 (notes/paired-law-plan-v2.md, section 4.3). The
   definitions of the statement are those of PairedDefinitions:
   paired_uniform_spec and paired_kernel.

   The analysis is done over any realType and any c > 0, then read at
   c = sqrt 3.
   - sym_uniform_pdf, sym_uniform_spec: a law P on the line with
     P A = int_A 1_(|x| <= c) / (2 c) dx for every Borel set A;
     paired_uniform_spec mu is sym_uniform_spec (sqrt 3) mu.
   - sym_uniform_prob, ge0_integral_sym_uniform: such a P is uniform_prob
     of MathComp-Analysis on [-c, c], so
     int f dP = (2 c)^-1 int_(-c)^c f for f >= 0 measurable.
   - integrable_sym_uniform, Rintegral_sym_uniform: a continuous q is
     P-integrable, and int q dP = (2 c)^-1 int_(-c)^c q.
   - sym_uniform_null, sym_uniform_ae: P puts no mass outside [-c, c], so
     functions equal on [-c, c] are P-almost everywhere equal.
   - Rintegral_itv_exprn, Rintegral_sym_uniform_exprn: int_a^b x^k dx by
     the fundamental theorem of calculus (Rintegral_FTC of
     library/fourier/esseen.v), hence
     int x^k dP = (c^(k+1) - (-c)^(k+1)) / (2 c (k + 1)).
   - legendre4, legendre4_range: h(x) = P_4(x / c) takes its values in
     [-3/7, 1] on [-c, c], since h + 3/7 = 5 (7 t^2 - 3)^2 / 56 and
     1 - h = 5 (1 - t^2) (1 + 7 t^2) / 8 with t = x / c.
   - Rintegral_legendre, Rintegral_legendre0, Rintegral_legendre1,
     Rintegral_legendre2, Rintegral_legendre4: int x^j (1 + a h) dP for
     j = 0, 1, 2, 4 is 1, 0, c^2 / 3 and c^4 / 5 + 8 a c^4 / 315, from the
     moments of P: int h dP = int x h dP = int x^2 h dP = 0 and
     int x^4 h dP = 8 c^4 / 315.
   - legendre_density, legendre_law: the density (1 + a h) 1_(|x| <= c),
     nonnegative everywhere for -1 <= a <= 7/3 (legendre_density_ge0),
     and the law lam_a = density_prob P (legendre_density c a) of
     library/probability/density_law.v. legendre_prob_density,
     legendre_law_integrable, integral_legendre_law: the density has
     integral one, every power is lam_a-integrable and
     int x^j dlam_a = int x^j (1 + a h) dP. legendre_law_expR:
     int exp (x^2 / K^2) dlam_a <= exp (c^2 / K^2).
   At c = sqrt 3, for a law mu with paired_uniform_spec mu and
   -1 <= a <= 7/3:
   - paired_density, paired_law: lam_a = density_prob mu (paired_density a).
   - paired_kernel_range: -3/7 <= h <= 1 on [-sqrt 3, sqrt 3].
   - paired_prob_density: paired_density a is a probability density
     against mu, nonnegative everywhere (the interface of density_prob).
   - paired_law_component, paired_law_fourth: lam_a is a component law
     with constant 3 (mixture_component_law 3 of MixtureDefinitions:
     mean 0, variance 1 and E exp (x^2 / 9) <= exp (1/3) <= 2,
     expR_third_le2), of fourth moment 9/5 + 8 a / 35.
   - paired_uniform_null, paired_law0, paired_law0E: mu puts no mass
     outside [-sqrt 3, sqrt 3], and lam_0 is mu.
   - paired_uniform_component, paired_uniform_fourth: mu is a component law
     with constant 3, of fourth moment 9/5. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences exp.
From mathcomp Require Import derive realfun.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability ftc charge.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import density_law.
From GaussianAnalysis.fourier Require Import esseen.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions PairedDefinitions.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section sym_uniform.
Context {RT : realType}.
Local Notation mu := (@lebesgue_measure RT).

Definition sym_uniform_pdf (c x : RT) : RT :=
  if `|x| <= c then (2%:R * c)^-1 else 0.

Definition sym_uniform_spec (c : RT) (P : probability (measurableTypeR RT) RT)
    : Prop :=
  forall A : set (measurableTypeR RT), measurable A ->
    P A = (\int[mu]_(x in A) (sym_uniform_pdf c x)%:E)%E.

(* h(x) = P_4(x / c), P_4(t) = (35 t^4 - 30 t^2 + 3) / 8. *)
Definition legendre4 (c x : RT) : RT :=
  (35%:R * (x / c) ^+ 4 - 30%:R * (x / c) ^+ 2 + 3%:R) / 8%:R.

(* The density 1 + a h against the uniform law, cut to [-c, c]. *)
Definition legendre_density (c a x : RT) : RT :=
  if `|x| <= c then 1 + a * legendre4 c x else 0.

(* The law lam_a with density legendre_density c a against P. *)
Definition legendre_law (c : RT) (P : probability (measurableTypeR RT) RT)
    (a : RT) : probability (measurableTypeR RT) RT :=
  density_prob P (legendre_density c a).

Lemma Rintegral_itv_exprn (a b : RT) k : a < b ->
  \int[mu]_(x in `[a, b]) x ^+ k = (b ^+ k.+1 - a ^+ k.+1) / k.+1%:R.
Proof.
move=> ab.
pose F (x : RT) := x ^+ k.+1.
pose f (x : RT) := k.+1%:R * x ^+ k.
have dF (x : RT) : is_derive x 1 F (f x).
  have := @is_deriveX _ _ (@id RT) k.+1 x 1 1 (is_derive_id x 1).
  have -> : (@id RT) ^+ k.+1 = F by apply/funext => y; rewrite /F exprfctE.
  move=> h; apply: (is_derive_eq h).
  by rewrite /f /GRing.scale /= mulr1.
have cf : continuous f.
  by move=> x; apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
have ik : mu.-integrable `[a, b] (EFin \o (fun x : RT => x ^+ k)).
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: continuous_subspaceT; exact: exprn_continuous.
have := Rintegral_FTC ab cf dF.
rewrite /f RintegralZl //.
rewrite /F => h.
have kn : k.+1%:R != 0 :> RT by rewrite pnatr_eq0.
by rewrite -h mulrC mulKf.
Qed.

Variables (c : RT) (P : probability (measurableTypeR RT) RT).
Hypotheses (c0 : 0 < c) (hP : sym_uniform_spec c P).

Let cc : - c < c.
Proof. by rewrite gtrN. Qed.

Let c2 : c - - c = 2%:R * c.
Proof. by rewrite opprK mulr_natl mulr2n. Qed.

Lemma sym_uniform_pdfE x : sym_uniform_pdf c x = uniform_pdf (- c) c x.
Proof. by rewrite /sym_uniform_pdf /uniform_pdf ler_norml c2. Qed.

Lemma sym_uniform_prob A : measurable A -> P A = uniform_prob cc A.
Proof.
move=> mA; rewrite hP // /uniform_prob; apply: eq_integral => x _.
by rewrite sym_uniform_pdfE.
Qed.

Lemma ge0_integral_sym_uniform (f : RT -> \bar RT) :
  measurable_fun setT f -> (forall x, 0 <= f x)%E ->
  (\int[P]_x f x =
   ((2%:R * c)^-1)%:E * \int[mu]_(x in `[(- c)%R, c]) f x)%E.
Proof.
move=> mf f0.
transitivity (\int[uniform_prob cc]_x f x)%E.
  by apply: eq_measure_integral => A mA _; exact: sym_uniform_prob.
by rewrite integral_uniform // c2.
Qed.

Lemma sym_uniform_null : P [set x | c < `|x|] = 0%E.
Proof.
have mS : measurable [set x : RT | c < `|x|].
  by rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr.
rewrite hP //; apply: integral0_eq => x /= cx.
by rewrite /sym_uniform_pdf leNgt cx.
Qed.

Lemma sym_uniform_ae (f g : RT -> \bar RT) :
  (forall x, `|x| <= c -> f x = g x) -> ae_eq P setT f g.
Proof.
move=> fg; exists [set x | c < `|x|]; split.
- by rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr.
- exact: sym_uniform_null.
- move=> x /= nfg; rewrite ltNge; apply/negP => xc; apply: nfg => _.
  exact: fg.
Qed.

Lemma integrable_sym_uniform (q : RT -> RT) : continuous q ->
  P.-integrable setT (EFin \o q).
Proof.
move=> cq; have mq : measurable_fun setT q := continuous_measurable_fun cq.
have qi : mu.-integrable `[- c, c] (EFin \o q).
  apply: continuous_compact_integrable; first exact: segment_compact.
  exact: continuous_subspaceT.
apply/integrableP; split; first exact/measurable_EFinP.
rewrite ge0_integral_sym_uniform //.
  by apply: (measurableT_comp (f := abse)) => //; exact/measurable_EFinP.
apply: lte_mul_pinfty => //.
  by rewrite lee_fin invr_ge0 mulr_ge0 // ltW.
by move/integrableP : qi => [].
Qed.

Lemma Rintegral_sym_uniform (q : RT -> RT) : continuous q ->
  \int[P]_x q x = (2%:R * c)^-1 * \int[mu]_(x in `[- c, c]) q x.
Proof.
move=> cq; have mq : measurable_fun setT q := continuous_measurable_fun cq.
have qi : mu.-integrable `[- c, c] (EFin \o q).
  apply: continuous_compact_integrable; first exact: segment_compact.
  exact: continuous_subspaceT.
have mI : measurable (`[- c, c] : set RT) by exact: measurable_itv.
rewrite /Rintegral integralE !ge0_integral_sym_uniform //;
  [exact/measurable_funepos/measurable_EFinP|
   exact/measurable_funeneg/measurable_EFinP|].
have fp : (\int[mu]_(x in `[(- c)%R, c]) (fun x0 => (q x0)%:E)^\+ x)%E
    \is a fin_num.
  by apply: integrable_fin_num => //; exact: integrable_funepos.
have fn : (\int[mu]_(x in `[(- c)%R, c]) (fun x0 => (q x0)%:E)^\- x)%E
    \is a fin_num.
  by apply: integrable_fin_num => //; exact: integrable_funeneg.
rewrite -muleBr; [by []|by rewrite fin_num_adde_defr|].
rewrite -integralE fineM //.
by apply: integrable_fin_num.
Qed.

Lemma Rintegral_sym_uniform_exprn k :
  \int[P]_x x ^+ k = (c ^+ k.+1 - (- c) ^+ k.+1) / (k.+1%:R * (2%:R * c)).
Proof.
have ck : continuous (fun x : RT => x ^+ k) := @exprn_continuous RT k.
rewrite Rintegral_sym_uniform // Rintegral_itv_exprn //.
have cn : c != 0 by rewrite gt_eqF.
have kn : k.+1%:R != 0 :> RT by rewrite pnatr_eq0.
by field.
Qed.

(* -3/7 <= h <= 1 on [-c, c]: h + 3/7 = 5 (7 t^2 - 3)^2 / 56 and
   1 - h = 5 (1 - t^2) (1 + 7 t^2) / 8, with t = x / c. *)
Lemma legendre4_range x : `|x| <= c ->
  - (3%:R / 7%:R) <= legendre4 c x <= 1.
Proof.
move=> xc; rewrite /legendre4.
have s1 : (x / c) ^+ 2 <= 1.
  rewrite expr_div_n ler_pdivrMr ?exprn_gt0 // mul1r.
  rewrite -[x ^+ 2]real_normK ?num_real // ler_pXn2r ?nnegrE //.
  exact: ltW.
have s0 : 0 <= (x / c) ^+ 2 := sqr_ge0 _.
have -> : (x / c) ^+ 4 = ((x / c) ^+ 2) ^+ 2 by rewrite -exprM.
move: s0 s1; set s := (x / c) ^+ 2 => s0 s1.
have q := sqr_ge0 (7%:R * s - 3%:R).
by apply/andP; split; nra.
Qed.

Lemma legendre_density_ge0 (a x : RT) : -1 <= a <= 7%:R / 3%:R ->
  0 <= legendre_density c a x.
Proof.
move=> /andP[a1 a2]; rewrite /legendre_density.
case: ifPn => // xc; have /andP[h1 h2] := legendre4_range x xc.
move: h1 h2; set h := legendre4 c x => h1 h2.
nra.
Qed.

Lemma continuous_legendre4 : continuous (legendre4 c).
Proof.
move=> x; apply: cvgM; last exact: cvg_cst.
apply: cvgD; first apply: cvgB.
- apply: cvgM; first exact: cvg_cst.
  apply: (@cvg_comp _ _ _ (fun y => y / c) (fun y => y ^+ 4)).
    by apply: cvgM; [exact: cvg_id|exact: cvg_cst].
  exact: exprn_continuous.
- apply: cvgM; first exact: cvg_cst.
  apply: (@cvg_comp _ _ _ (fun y => y / c) (fun y => y ^+ 2)).
    by apply: cvgM; [exact: cvg_id|exact: cvg_cst].
  exact: exprn_continuous.
- exact: cvg_cst.
Qed.

Lemma measurable_legendre_density a :
  measurable_fun setT (legendre_density c a).
Proof.
have cg : continuous (fun x : RT => 1 + a * legendre4 c x).
  move=> x; apply: cvgD; first exact: cvg_cst.
  by apply: cvgM; [exact: cvg_cst|exact: continuous_legendre4].
rewrite /legendre_density; apply: measurable_fun_if => //.
  by apply: measurable_fun_ler; [exact: normr_measurable|exact: measurable_cst].
by apply: measurable_funTS; exact: continuous_measurable_fun.
Qed.

Let im k : P.-integrable setT (EFin \o (fun x : RT => x ^+ k)).
Proof. exact: integrable_sym_uniform (@exprn_continuous RT k). Qed.

Let cmono (b : RT) k : continuous (fun x : RT => b * x ^+ k).
Proof. by move=> x; apply: cvgM; [exact: cvg_cst|exact: exprn_continuous]. Qed.

Let ims (b : RT) k : P.-integrable setT (EFin \o (fun x : RT => b * x ^+ k)).
Proof. exact: integrable_sym_uniform (cmono b k). Qed.

Lemma Rintegral_sym_uniform_lin3 (b1 b2 b3 : RT) k1 k2 k3 :
  \int[P]_x (b1 * x ^+ k1 + b2 * x ^+ k2 + b3 * x ^+ k3) =
  b1 * \int[P]_x x ^+ k1 + b2 * \int[P]_x x ^+ k2 + b3 * \int[P]_x x ^+ k3.
Proof.
have i12 : P.-integrable setT
    (EFin \o (fun x : RT => b1 * x ^+ k1 + b2 * x ^+ k2)).
  apply: integrable_sym_uniform => x.
  by apply: cvgD; [exact: cmono|exact: cmono].
have i1 := ims b1 k1; have i2 := ims b2 k2; have i3 := ims b3 k3.
have i1' := im k1; have i2' := im k2; have i3' := im k3.
by rewrite RintegralD // RintegralD // !RintegralZl.
Qed.

(* The moments of x^j (1 + a h) against the uniform law. *)
Lemma Rintegral_legendre a j :
  \int[P]_x (x ^+ j * (1 + a * legendre4 c x)) =
  (1 + 3%:R * a / 8%:R) * \int[P]_x x ^+ j +
  35%:R * a / (8%:R * c ^+ 4) * \int[P]_x x ^+ (j + 4) +
  - (30%:R * a / (8%:R * c ^+ 2)) * \int[P]_x x ^+ (j + 2).
Proof.
rewrite -Rintegral_sym_uniform_lin3; apply: eq_Rintegral => x _.
rewrite /legendre4 !exprD.
have cn : c != 0 by rewrite gt_eqF.
by field.
Qed.

Let M k : \int[P]_x x ^+ k =
  (c ^+ k.+1 - (- c) ^+ k.+1) / (k.+1%:R * (2%:R * c)).
Proof. exact: Rintegral_sym_uniform_exprn. Qed.

Lemma Rintegral_legendre0 a :
  \int[P]_x (x ^+ 0 * (1 + a * legendre4 c x)) = 1.
Proof.
rewrite Rintegral_legendre !M /=.
have cn : c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma Rintegral_legendre1 a :
  \int[P]_x (x ^+ 1 * (1 + a * legendre4 c x)) = 0.
Proof.
rewrite Rintegral_legendre !M /=.
have cn : c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma Rintegral_legendre2 a :
  \int[P]_x (x ^+ 2 * (1 + a * legendre4 c x)) = c ^+ 2 / 3%:R.
Proof.
rewrite Rintegral_legendre !M /=.
have cn : c != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma Rintegral_legendre4 a :
  \int[P]_x (x ^+ 4 * (1 + a * legendre4 c x)) =
  c ^+ 4 / 5%:R + 8%:R * a * c ^+ 4 / 315%:R.
Proof.
rewrite Rintegral_legendre !M /=.
have cn : c != 0 by rewrite gt_eqF.
by field.
Qed.

Let EFin_Rintegral (f : RT -> RT) : P.-integrable setT (EFin \o f) ->
  (\int[P]_x (f x)%:E)%E = (\int[P]_x f x)%:E.
Proof.
by move=> fi; rewrite /Rintegral fineK //; exact: integrable_fin_num.
Qed.

Let cpoly a j : continuous (fun x : RT => x ^+ j * (1 + a * legendre4 c x)).
Proof.
move=> x; apply: cvgM; first exact: exprn_continuous.
apply: cvgD; first exact: cvg_cst.
by apply: cvgM; [exact: cvg_cst|exact: continuous_legendre4].
Qed.

Lemma legendre_prob_density a : -1 <= a <= 7%:R / 3%:R ->
  prob_density P (legendre_density c a).
Proof.
move=> ha; split; [exact: measurable_legendre_density|
  by move=> x; exact: legendre_density_ge0|].
transitivity (\int[P]_x (x ^+ 0 * (1 + a * legendre4 c x))%:E)%E.
  apply: ae_eq_integral => //.
  - apply/measurable_EFinP; exact: measurable_legendre_density.
  - apply/measurable_EFinP; exact: continuous_measurable_fun (cpoly a 0).
  - apply: sym_uniform_ae => x xc.
    by rewrite /legendre_density xc expr0 mul1r.
rewrite EFin_Rintegral ?Rintegral_legendre0 //.
exact: integrable_sym_uniform.
Qed.

Lemma legendre_law_integrable a j : -1 <= a <= 7%:R / 3%:R ->
  (legendre_law c P a).-integrable setT (EFin \o (fun x : RT => x ^+ j)).
Proof.
move=> ha; have hd := legendre_prob_density a ha.
have mj : measurable_fun setT (EFin \o (fun x : RT => x ^+ j)).
  apply/measurable_EFinP.
  exact: continuous_measurable_fun (@exprn_continuous RT j).
apply/(integrable_density_prob hd measurableT mj).
have hi := integrable_sym_uniform _ (cpoly a j).
apply: (le_integrable measurableT _ _ hi).
  apply: emeasurable_funM => //.
  by apply/measurable_EFinP; exact: measurable_legendre_density.
move=> x _; rewrite /legendre_density /=; case: ifPn => _ //.
by rewrite mulr0 normr0 lee_fin normr_ge0.
Qed.

Lemma integral_legendre_law a j : -1 <= a <= 7%:R / 3%:R ->
  (\int[legendre_law c P a]_x (x ^+ j)%:E =
   (\int[P]_x (x ^+ j * (1 + a * legendre4 c x)))%:E)%E.
Proof.
move=> ha; have hd := legendre_prob_density a ha.
rewrite (integral_density_prob hd measurableT (legendre_law_integrable a j ha)).
rewrite -(EFin_Rintegral _ (integrable_sym_uniform _ (cpoly a j))).
apply: ae_eq_integral => //.
- apply: emeasurable_funM => //.
    apply/measurable_EFinP.
    exact: continuous_measurable_fun (@exprn_continuous RT j).
  by apply/measurable_EFinP; exact: measurable_legendre_density.
- apply/measurable_EFinP; exact: continuous_measurable_fun (cpoly a j).
- apply: sym_uniform_ae => x xc /=.
  by rewrite /legendre_density xc.
Qed.

Lemma legendre_law_expR a (K : RT) : -1 <= a <= 7%:R / 3%:R ->
  (\int[legendre_law c P a]_x (expR (x ^+ 2 / K ^+ 2))%:E <=
   (expR (c ^+ 2 / K ^+ 2))%:E)%E.
Proof.
move=> ha; have hd := legendre_prob_density a ha.
have ce : continuous (fun x : RT => expR (x ^+ 2 / K ^+ 2)).
  move=> x; apply: (continuous_comp (f := fun y : RT => y ^+ 2 / K ^+ 2)).
    by apply: cvgM; [exact: exprn_continuous|exact: cvg_cst].
  exact: continuous_expR.
have mf : measurable_fun setT (fun x : RT => (expR (x ^+ 2 / K ^+ 2))%:E).
  by apply/measurable_EFinP; exact: continuous_measurable_fun.
have mg : measurable_fun setT (fun x : RT => (legendre_density c a x)%:E).
  by apply/measurable_EFinP; exact: measurable_legendre_density.
have g0 x : (0 <= (legendre_density c a x)%:E)%E.
  by rewrite lee_fin legendre_density_ge0.
rewrite (ge0_integral_density_prob hd measurableT _ mf); first by move=> x;
  rewrite lee_fin expR_ge0.
apply: (@le_trans _ _ (\int[P]_x ((expR (c ^+ 2 / K ^+ 2))%:E *
    (legendre_density c a x)%:E))%E).
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite mule_ge0 // lee_fin expR_ge0.
  - exact: emeasurable_funM.
  - by apply: emeasurable_funM => //; exact: measurable_cst.
  move=> x _; have := legendre_density_ge0 a x ha.
  rewrite /legendre_density; case: ifPn => xc gx; last by rewrite !mule0.
  apply: lee_wpmul2r; first by rewrite lee_fin.
  rewrite lee_fin ler_expR; apply: ler_wpM2r.
    by rewrite invr_ge0 sqr_ge0.
  rewrite -[x ^+ 2]real_normK ?num_real // ler_pXn2r ?nnegrE //.
  exact: ltW.
rewrite ge0_integralZl //.
by case: hd => _ _ ->; rewrite mule1.
Qed.

End sym_uniform.

Local Notation RR := (R : realType).

Lemma expR_third_le2 {RT : realType} : expR (3%:R^-1 : RT) <= 2%:R.
Proof.
have h := expR_ge1Dx (- 3%:R^-1 : RT).
have e : expR (3%:R^-1 : RT) = (expR (- 3%:R^-1))^-1 by rewrite expRN invrK.
have p : (0 : RT) < 1 - 3%:R^-1.
  by rewrite subr_gt0 invf_lt1 ?ltr0n // ltr1n.
rewrite e; apply: (@le_trans _ _ ((1 - 3%:R^-1)^-1)).
  by rewrite lef_pV2 ?posrE ?expR_gt0.
have -> : (1 - 3%:R^-1 : RT) = 2%:R / 3%:R by field.
rewrite invf_div ler_pdivrMr ?ltr0n // -natrM ler_nat.
by [].
Qed.

Lemma paired_moment_arith {RT : realType} (a c : RT) : c ^+ 2 = 3%:R ->
  [/\ c ^+ 2 / 3%:R = 1, c ^+ 2 / 3%:R ^+ 2 = 3%:R^-1 &
    c ^+ 4 / 5%:R + 8%:R * a * c ^+ 4 / 315%:R =
    9%:R / 5%:R + 8%:R * a / 35%:R].
Proof.
move=> c2; have c4 : c ^+ 4 = 9%:R by rewrite (exprM c 2 2) c2 -natrX.
by rewrite c4 c2; split; field.
Qed.

Definition paired_density (a x : R) : R := legendre_density (Num.sqrt 3%:R) a x.

Definition paired_law (mu : probability (measurableTypeR R) R) (a : R) :
  probability (measurableTypeR R) R := density_prob mu (paired_density a).

Section paired_uniform.
Variable mu : probability (measurableTypeR R) R.
Hypothesis hmu : paired_uniform_spec mu.

Let c0 : (0 : RR) < Num.sqrt 3%:R. Proof. by rewrite sqrtr_gt0 ltr0n. Qed.
Let hP : sym_uniform_spec (Num.sqrt 3%:R : RR) mu. Proof. exact: hmu. Qed.
Let c2 : (Num.sqrt 3%:R : RR) ^+ 2 = 3%:R.
Proof. by rewrite sqr_sqrtr // ler0n. Qed.

Lemma paired_kernel_legendre x : paired_kernel x = legendre4 (Num.sqrt 3%:R) x.
Proof. by []. Qed.

Lemma paired_kernel_range x : `|x| <= Num.sqrt 3%:R ->
  - (3%:R / 7%:R) <= paired_kernel x <= 1.
Proof. exact: legendre4_range. Qed.

Lemma paired_uniform_null : mu [set x | Num.sqrt 3%:R < `|x|] = 0%E.
Proof. exact: sym_uniform_null. Qed.

Lemma paired_prob_density a : -1 <= a <= 7%:R / 3%:R ->
  prob_density mu (paired_density a).
Proof. exact: legendre_prob_density. Qed.

Let Epow a j : -1 <= a <= 7%:R / 3%:R ->
  ('E_(paired_law mu a)[universality_power j] =
   (\int[mu]_x (x ^+ j * (1 + a * legendre4 (Num.sqrt 3%:R) x)))%:E)%E.
Proof.
move=> ha; rewrite unlock /universality_power.
exact: integral_legendre_law.
Qed.

Lemma paired_law_fourth a : -1 <= a <= 7%:R / 3%:R ->
  ('E_(paired_law mu a)[universality_power 4] =
   (9%:R / 5%:R + 8%:R * a / 35%:R)%:E)%E.
Proof.
move=> ha; rewrite Epow // (Rintegral_legendre4 _ _ c0 hP).
by have [_ _ ->] := paired_moment_arith a _ c2.
Qed.

Lemma paired_law_component a : -1 <= a <= 7%:R / 3%:R ->
  mixture_component_law 3%:R (paired_law mu a).
Proof.
move=> ha; have [m2 m3 _] := paired_moment_arith a _ c2.
split; first by rewrite ltr0n.
split; first by rewrite Epow // (Rintegral_legendre1 _ _ c0 hP).
split; first by rewrite Epow // (Rintegral_legendre2 _ _ c0 hP) m2.
rewrite unlock /universality_subgaussian_test.
apply: le_trans (legendre_law_expR _ _ c0 hP a 3%:R ha) _.
by rewrite m3 lee_fin; exact: expR_third_le2.
Qed.

Lemma paired_law0 A : measurable A -> paired_law mu 0 A = mu A.
Proof.
move=> mA; have ha : -1 <= (0 : RR) <= 7%:R / 3%:R.
  by rewrite lerN10 divr_ge0 ?ler0n.
transitivity (density_prob mu (paired_density 0) A); first by [].
rewrite (density_probE (paired_prob_density 0 ha)).
transitivity (\int[mu]_(x in A) (cst 1%E) x)%E.
  apply: ae_eq_integral => //.
  - apply/measurable_EFinP; apply: measurable_funTS.
    exact: measurable_legendre_density.
  - apply: ae_eq_subset (subsetT A) _.
    apply: (sym_uniform_ae _ _ hP) => x xc.
    by rewrite /paired_density /legendre_density xc mul0r addr0.
by rewrite integral_cst // mul1e.
Qed.

Lemma paired_law0E (f : RR -> RR) : ('E_mu[f] = 'E_(paired_law mu 0)[f])%E.
Proof.
rewrite unlock; apply: eq_measure_integral => A mA _.
by symmetry; exact: paired_law0.
Qed.

Lemma paired_uniform_component : mixture_component_law 3%:R mu.
Proof.
have ha : -1 <= (0 : RR) <= 7%:R / 3%:R.
  by rewrite lerN10 divr_ge0 ?ler0n.
have [K0 [h1 [h2 h3]]] := paired_law_component 0 ha.
by split => //; rewrite !paired_law0E.
Qed.

Lemma paired_uniform_fourth :
  ('E_mu[universality_power 4] = (9%:R / 5%:R)%:E)%E.
Proof.
have ha : -1 <= (0 : RR) <= 7%:R / 3%:R.
  by rewrite lerN10 divr_ge0 ?ler0n.
by rewrite paired_law0E paired_law_fourth // mulr0 mul0r addr0.
Qed.

End paired_uniform.
