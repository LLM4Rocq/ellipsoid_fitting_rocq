(* The scope of the latent-sign law, at Stdlib's R: item S1 of phase 8
   (notes/three-extensions-plan.md, sections 1.2 and 4.5;
   notes/phase6-three-extensions.md, section 2, (10) and (11)). The
   statements are those of LatentSignScope, about latent_point_expectation:
   the integral of a function of one point against the density
   latent_sample_density s 1 d of LatentSignDefinitions.

   1. One coordinate, over any realType and any c > 0, for a law P with
      sym_uniform_spec c P (Paired/Uniform), h = legendre4 c and the law
      lam_a = legendre_law c P a with density 1 + a h:
      - continuous_poly, Rintegral_itv_poly: a polynomial is continuous,
        and int_a^b sum_i e_i x^i dx = sum_i e_i (b^(i+1) - a^(i+1)) / (i+1),
        from Rintegral_itv_exprn of Paired/Uniform;
      - legendre_law_cont: a continuous f is lam_a-integrable, and
        int f dlam_a = int f (1 + a h) dP;
      - Rintegral_legendre_sqr, Rintegral_legendre_h: int x^2 dlam_a = c^2 / 3
        and int h dlam_a = a / 9, from the moments Rintegral_legendre0,
        Rintegral_legendre2 and Rintegral_legendre4 of Paired/Uniform;
      - Rintegral_legendre_abs: int |x| dlam_a = c / 2 - a c / 48, since
        int_(-c)^c = 2 int_0^c for an even function (Rintegral_even of
        library/fourier/esseen.v) and |x| (1 + a h(x)) is a polynomial on
        [0, c];
      - legendre_law_sum: lam_a A + lam_(-a) A = 2 P A, since the two
        densities add up to 2 on [-c, c], which carries P.
   2. One point. Its density is (latent_prod s + latent_prod (- s)) / 2,
      with latent_prod a d x = prod_k (1 + a h(x_k)) (latent_densityE). The
      product law latent_side mu d a of d coordinates of law paired_law mu a
      has the density latent_prod a d against the product of d copies of
      mu, outside the null event where a coordinate leaves
      [-sqrt 3, sqrt 3] (latent_box_ae, latent_side_integral, from
      tuple_prod_density of library/probability/density_law.v). Hence
      latent_point_expectationE: for f integrable under both product laws,
      latent_point_expectation s mu d f is the average of the two
      expectations of f.
   3. The product laws. Rintegral_sum_ord: the integral of a finite sum of
      integrable functions. Under latent_side mu d a, a coordinate has the
      law paired_law mu a (latent_side_coord), and two distinct coordinates
      are independent (latent_side_coordM), from integral_tuple_prod_coord
      and integral_tuple_prod_coordM of library/probability/efron_stein.v.
   4. The statements, for 0 <= s <= 1 and paired_uniform_spec mu.
      - latent_covariance_at, (10): the law of x_j is mu, by
        legendre_law_sum; E h(x_j) = (s / 9 - s / 9) / 2 = 0; and for j != k,
        E h(x_j) h(x_k) = ((s / 9)^2 + (s / 9)^2) / 2 = s^2 / 81.
      - latent_variance_at, (11): with k_a = 1/2 - a / 48, the coordinates
        under latent_side mu d a have E |x_j| = sqrt 3 k_a, E x_j^2 = 1 and
        E |x_j| |x_k| = 3 k_a^2 for j != k. So S = sum_j |x_j| has
        E S = d sqrt 3 k_a and E S^2 = d (1 - 3 k_a^2 + 3 d k_a^2). Averaging
        over a = s and a = - s, with k_s + k_(-s) = 1, gives
        E F = sqrt (3 d) / 2 and the variance 1/4 + (d - 1) s^2 / 768 of
        F = S / sqrt d. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import derive realfun.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg density_law.
From GaussianAnalysis.probability Require Import efron_stein.
From GaussianAnalysis.fourier Require Import esseen.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignDefinitions LatentSignScope.
From GaussianAnalysis.random_matrix Require Import restricted_isometry.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Paired Require Import Uniform Law LatentSign.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* 1. One coordinate. *)

Section poly_integrals.
Context {RT : realType}.
Local Notation leb := (@lebesgue_measure RT).

Lemma continuous_poly (e : nat -> RT) n :
  continuous (fun x : RT => \sum_(i < n) e i * x ^+ i).
Proof.
elim: n => [|n IH].
  have -> : (fun x : RT => \sum_(i < 0) e i * x ^+ i) = fun=> 0.
    by apply/funext => x; rewrite big_ord0.
  exact: cst_continuous.
have -> : (fun x : RT => \sum_(i < n.+1) e i * x ^+ i) =
    (fun x => \sum_(i < n) e i * x ^+ i + e n * x ^+ n).
  by apply/funext => x; rewrite big_ord_recr.
move=> x; apply: cvgD; first exact: IH.
by apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
Qed.

Lemma Rintegral_itv_poly (e : nat -> RT) n (a b : RT) : a < b ->
  \int[leb]_(x in `[a, b]) (\sum_(i < n) e i * x ^+ i) =
  \sum_(i < n) e i * ((b ^+ i.+1 - a ^+ i.+1) / i.+1%:R).
Proof.
move=> ab; have mI : measurable (`[a, b] : set RT) by exact: measurable_itv.
have ic (f : RT -> RT) : continuous f -> leb.-integrable `[a, b] (EFin \o f).
  move=> cf; apply: continuous_compact_integrable; first exact: segment_compact.
  exact: continuous_subspaceT.
elim: n => [|n IH].
  under eq_Rintegral do rewrite big_ord0.
  by rewrite Rintegral_cst // mul0r big_ord0.
under eq_Rintegral do rewrite big_ord_recr /=.
have cm : continuous (fun x : RT => e n * x ^+ n).
  by move=> x; apply: cvgM; [exact: cvg_cst|exact: exprn_continuous].
have i1 := ic _ (continuous_poly e n); have i2 := ic _ cm.
have i3 := ic _ (@exprn_continuous RT n).
rewrite RintegralD // IH RintegralZl // Rintegral_itv_exprn //.
by rewrite [in RHS]big_ord_recr.
Qed.

End poly_integrals.

Section legendre_integrals.
Context {RT : realType}.
Local Notation leb := (@lebesgue_measure RT).
Variables (c : RT) (P : probability (measurableTypeR RT) RT).
Hypotheses (c0 : 0 < c) (hP : sym_uniform_spec c P).

Let cn : c != 0. Proof. by rewrite gt_eqF. Qed.

Let continuous_h : continuous (legendre4 c).
Proof. exact: continuous_legendre4. Qed.

(* A continuous f is integrable against lam_a, with
   int f dlam_a = int f (1 + a h) dP. *)
Lemma legendre_law_cont a (f : RT -> RT) : -1 <= a <= 7%:R / 3%:R ->
  continuous f ->
  (legendre_law c P a).-integrable setT (EFin \o f) /\
  \int[legendre_law c P a]_x f x = \int[P]_x (f x * (1 + a * legendre4 c x)).
Proof.
move=> ha cf; have hd := legendre_prob_density c P c0 hP a ha.
have cq : continuous (fun x => f x * (1 + a * legendre4 c x)).
  move=> x; apply: cvgM; first exact: cf.
  apply: cvgD; first exact: cvg_cst.
  by apply: cvgM; [exact: cvg_cst|exact: continuous_h].
have mf : measurable_fun setT (EFin \o f).
  by apply/measurable_EFinP; exact: continuous_measurable_fun.
have md : measurable_fun setT (fun x => (legendre_density c a x)%:E).
  by apply/measurable_EFinP; exact: measurable_legendre_density.
have iq := integrable_sym_uniform c P c0 hP _ cq.
have i1 : (legendre_law c P a).-integrable setT (EFin \o f).
  apply/(integrable_density_prob hd measurableT mf).
  apply: (le_integrable measurableT _ _ iq); first exact: emeasurable_funM.
  move=> x _; rewrite /legendre_density /=; case: ifPn => _ //.
  by rewrite mulr0 normr0 lee_fin normr_ge0.
split => //; rewrite /Rintegral (integral_density_prob hd measurableT i1).
congr fine; apply: ae_eq_integral => //.
- exact: emeasurable_funM.
- by apply/measurable_EFinP; exact: continuous_measurable_fun.
- apply: (sym_uniform_ae _ _ hP) => x xc /=.
  by rewrite /legendre_density xc.
Qed.

Let Emon a j : -1 <= a <= 7%:R / 3%:R ->
  \int[legendre_law c P a]_x (x ^+ j) =
  \int[P]_x (x ^+ j * (1 + a * legendre4 c x)).
Proof.
by move=> ha; have [_ ->] := legendre_law_cont _ _ ha (@exprn_continuous RT j).
Qed.

Let imon a j : -1 <= a <= 7%:R / 3%:R ->
  (legendre_law c P a).-integrable setT (EFin \o (fun x : RT => x ^+ j)).
Proof.
by move=> ha; have [] := legendre_law_cont _ _ ha (@exprn_continuous RT j).
Qed.

Lemma Rintegral_legendre_sqr a : -1 <= a <= 7%:R / 3%:R ->
  \int[legendre_law c P a]_x (x ^+ 2) = c ^+ 2 / 3%:R.
Proof. by move=> ha; rewrite Emon // (Rintegral_legendre2 _ _ c0 hP). Qed.

(* int h dlam_a = a / 9. *)
Lemma Rintegral_legendre_h a : -1 <= a <= 7%:R / 3%:R ->
  \int[legendre_law c P a]_x legendre4 c x = a / 9%:R.
Proof.
move=> ha.
have e x : legendre4 c x = 35%:R / (8%:R * c ^+ 4) * x ^+ 4 +
    - (30%:R / (8%:R * c ^+ 2)) * x ^+ 2 + 3%:R / 8%:R * x ^+ 0.
  by rewrite /legendre4; field.
under eq_Rintegral do rewrite e.
have iZ (b : RT) j : (legendre_law c P a).-integrable setT
    (EFin \o (fun x : RT => b * x ^+ j)).
  apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT b (imon a j ha))) => x _ /=.
  by rewrite EFinM.
have i4 := iZ (35%:R / (8%:R * c ^+ 4)) 4%N.
have i2 := iZ (- (30%:R / (8%:R * c ^+ 2))) 2%N.
have i0 := iZ (3%:R / 8%:R) 0%N.
have m4 := imon a 4 ha; have m2 := imon a 2 ha; have m0 := imon a 0 ha.
have i42 : (legendre_law c P a).-integrable setT (EFin \o (fun x : RT =>
    35%:R / (8%:R * c ^+ 4) * x ^+ 4 + - (30%:R / (8%:R * c ^+ 2)) * x ^+ 2)).
  apply: (eq_integrable measurableT _ _ _
    (integrableD measurableT i4 i2)) => x _ /=.
  by rewrite EFinD.
rewrite RintegralD // RintegralD // !RintegralZl // !Emon //.
rewrite (Rintegral_legendre4 _ _ c0 hP) (Rintegral_legendre2 _ _ c0 hP).
rewrite (Rintegral_legendre0 _ _ c0 hP).
by field.
Qed.

(* int |x| dlam_a = c / 2 - a c / 48. *)
Lemma Rintegral_legendre_abs a : -1 <= a <= 7%:R / 3%:R ->
  \int[legendre_law c P a]_x `|x| = c / 2%:R - a * c / 48%:R.
Proof.
move=> ha; have [_ ->] := legendre_law_cont _ _ ha (@norm_continuous _ RT^o).
have cq : continuous (fun x : RT => `|x| * (1 + a * legendre4 c x)).
  move=> x; apply: cvgM; first exact: (@norm_continuous _ RT^o).
  apply: cvgD; first exact: cvg_cst.
  by apply: cvgM; [exact: cvg_cst|exact: continuous_h].
have ev (t : RT) :
    `|- t| * (1 + a * legendre4 c (- t)) = `|t| * (1 + a * legendre4 c t).
  by rewrite normrN /legendre4; ring.
rewrite (Rintegral_sym_uniform c P c0 hP _ cq) Rintegral_even //.
(* on [0, c], |x| (1 + a h(x)) is a polynomial of degree 5 *)
pose e (i : nat) : RT := nth 0 [:: 0; 1 + 3%:R * a / 8%:R; 0;
  - (30%:R * a / (8%:R * c ^+ 2)); 0; 35%:R * a / (8%:R * c ^+ 4)] i.
transitivity ((2%:R * c)^-1 * (2%:R *
    \int[leb]_(x in `[0, c]) (\sum_(i < 6) e i * x ^+ i))).
  congr (_ * (_ * _)); apply: eq_Rintegral => x.
  rewrite inE /= in_itv /= => /andP[x0 _].
  rewrite ger0_norm // !big_ord_recr big_ord0 /= /legendre4 /e /=.
  by field.
rewrite Rintegral_itv_poly // !big_ord_recr big_ord0 /e /= expr0n /=.
by field.
Qed.

(* lam_a A + lam_(-a) A = 2 P A. *)
Lemma legendre_law_sum a A : -1 <= a <= 7%:R / 3%:R ->
  -1 <= - a <= 7%:R / 3%:R -> measurable A ->
  (legendre_law c P a A + legendre_law c P (- a) A = 2%:R%:E * P A)%E.
Proof.
move=> ha hna mA.
have hd := legendre_prob_density c P c0 hP a ha.
have hnd := legendre_prob_density c P c0 hP (- a) hna.
transitivity (density_prob P (legendre_density c a) A +
  density_prob P (legendre_density c (- a)) A)%E; first by [].
rewrite (density_probE hd) (density_probE hnd).
have md b : measurable_fun A (fun x => (legendre_density c b x)%:E).
  apply/measurable_funTS/measurable_EFinP.
  exact: measurable_legendre_density.
have f0 b : -1 <= b <= 7%:R / 3%:R ->
    forall x, A x -> (0 <= (legendre_density c b x)%:E)%E.
  by move=> hb x _; rewrite lee_fin legendre_density_ge0.
rewrite -(ge0_integralD P mA (f0 _ ha) (md a) (f0 _ hna) (md (- a))).
transitivity (\int[P]_(x in A) (cst (2%:R%:E : \bar RT)) x)%E.
  apply: ae_eq_integral => //.
  - by apply: emeasurable_funD; exact: md.
  - apply: ae_eq_subset (subsetT A) _.
    apply: (sym_uniform_ae _ _ hP) => x xc /=.
    by rewrite /legendre_density xc -EFinD mulNr; congr (_%:E); ring.
by rewrite integral_cst.
Qed.

End legendre_integrals.

(* 2. One point. *)

(* The product law of the d coordinates of a point, each of law
   paired_law mu a. *)
Definition latent_side (mu : probability (measurableTypeR R) R) (d : nat)
    (a : R) : probability (paper_main_sample 1 d) R :=
  tuple_prod (fun=> paired_law mu a) (1 * d).

(* prod_k (1 + a h(x_k)). *)
Definition latent_prod (a : R) (d : nat) (x : paper_main_sample 1 d) : R :=
  \prod_(k < 1 * d) (1 + a * paired_kernel (tnth x k)).

Lemma latent_densityE (s : R) (d : nat) (x : paper_main_sample 1 d) :
  latent_sample_density s 1 d x =
  (latent_prod s d x + latent_prod (- s) d x) / 2%:R.
Proof.
have e (a : R) : \prod_(j < d)
    (1 + a * paired_kernel (List.nth (0 * d + j) (tval x) 0)) =
    latent_prod a d x.
  have ek (k : 'I_(1 * d)) : 1 + a * paired_kernel (tnth x k) =
      1 + a * paired_kernel (List.nth k (tval x) 0).
    by rewrite (tnth_nth 0) List_nthE.
  rewrite /latent_prod (eq_bigr _ (fun k _ => ek k)).
  by rewrite (prod_flat 1 d (fun k => 1 + a * paired_kernel
    (List.nth k (tval x) 0))) big_ord1.
rewrite /latent_sample_density big_ord1 -(e s) -(e (- s)).
by congr ((_ + _) / _); apply: eq_bigr => j _; rewrite ?mulNr.
Qed.

Lemma measurable_latent_prod a d :
  measurable_fun setT (fun x : paper_main_sample 1 d => latent_prod a d x : RR).
Proof.
apply: measurable_prod => k _.
apply: measurable_funD; first exact: measurable_cst.
apply: measurable_funM; first exact: measurable_cst.
exact: measurableT_comp measurable_paired_kernel (measurable_tnth k).
Qed.

Section latent_point.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).
Local Notation U := (universality_sample_law (fun=> mu) 1 d).

Let hsp : -1 <= s <= 7%:R / 3%:R.
Proof. exact: (latent_param_range s 0 hs). Qed.

Let hsn : -1 <= - s <= 7%:R / 3%:R.
Proof. exact: (latent_param_range s 1 hs). Qed.

(* Every coordinate lies in [-sqrt 3, sqrt 3] almost surely. *)
Lemma latent_box_ae (G H : paper_main_sample 1 d -> \bar R) :
  (forall x, (forall k, `|tnth x k| <= Num.sqrt 3%:R) -> G x = H x) ->
  ae_eq U setT G H.
Proof.
move=> GH.
pose B (k : 'I_(1 * d)) :=
  [set x : paper_main_sample 1 d | Num.sqrt 3%:R < `|tnth x k|].
have mB0 : measurable [set y : RR | Num.sqrt 3%:R < `|y|].
  by rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr.
have mB k : measurable (B k).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_tnth k) measurableT _ mB0.
pose Nul := \big[setU/set0]_(k <- enum 'I_(1 * d)) B k.
have mN : measurable Nul by apply: bigsetU_measurable => k _; exact: mB.
have PN : U Nul = 0%E.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  apply: le_trans (measure_bigsetU_le _ _ mB) _.
  rewrite big1 // => k _.
  transitivity (mu [set y | Num.sqrt 3%:R < `|y|]).
    exact: (@tuple_prod_tnth _ _ (fun=> mu) (1 * d) k _ mB0).
  exact: paired_uniform_null.
exists Nul; split => // x /= hx; apply: contrapT => nx; apply: hx => _.
apply: GH => k; rewrite leNgt; apply/negP => hk; apply: nx.
by apply: (bigsetU_mem (mem_enum _ k)).
Qed.

(* Against the product of the d copies of mu, the product law
   latent_side mu d a has the density prod_k (1 + a h(x_k)). *)
Lemma latent_side_integral (a : R) (g : paper_main_sample 1 d -> RR) :
  -1 <= a <= 7%:R / 3%:R -> measurable_fun setT g ->
  (latent_side mu d a).-integrable setT (EFin \o g) ->
  U.-integrable setT (fun x => (g x * latent_prod a d x)%:E) /\
  \int[latent_side mu d a]_x g x = \int[U]_x (g x * latent_prod a d x).
Proof.
move=> ha mg ig.
pose Q (x : paper_main_sample 1 d) :=
  \prod_(k < 1 * d) paired_density a (tnth x k).
have hd := paired_prob_density mu hmu a ha.
have hQ : prob_density U Q.
  exact: (@prob_density_tuple_prod _ _ RR (fun=> mu) (fun=> paired_density a)
    (1 * d) (fun k _ => hd)).
have eqm A : measurable A -> latent_side mu d a A = density_prob U Q A.
  move=> mA; rewrite (density_probE hQ).
  exact: (@tuple_prod_density _ _ RR (fun=> mu) (fun=> paired_density a)
    (1 * d) A (fun k _ => hd) mA).
have ei (f : paper_main_sample 1 d -> \bar R) :
    (\int[latent_side mu d a]_x f x = \int[density_prob U Q]_x f x)%E.
  by apply: eq_measure_integral => A mA _; exact: eqm.
have mgE : measurable_fun setT (EFin \o g) by exact/measurable_EFinP.
have gi : (density_prob U Q).-integrable setT (EFin \o g).
  apply/integrableP; split => //; rewrite -ei.
  by case/integrableP: ig.
have giQ := (integrable_density_prob hQ measurableT mgE).1 gi.
have mP : measurable_fun setT (fun x => (g x * latent_prod a d x)%:E).
  by apply/measurable_EFinP; apply: measurable_funM => //;
    exact: measurable_latent_prod.
have mQ : measurable_fun setT (fun x => ((EFin \o g) x * (Q x)%:E)%E).
  apply: emeasurable_funM => //; apply/measurable_EFinP.
  apply: measurable_prod => k _.
  exact: measurableT_comp (measurable_legendre_density _ _) (measurable_tnth k).
have box x : (forall k, `|tnth x k| <= Num.sqrt 3%:R) ->
    ((EFin \o g) x * (Q x)%:E)%E = (g x * latent_prod a d x)%:E.
  move=> hx /=; rewrite -EFinM; congr (_%:E); congr (_ * _).
  apply: eq_bigr => k _.
  by rewrite /paired_density /legendre_density (hx k) paired_kernel_legendre.
split.
  apply/integrableP; split => //.
  have <- : (\int[U]_x `|(EFin \o g) x * (Q x)%:E| =
      \int[U]_x `|(g x * latent_prod a d x)%:E|)%E.
    apply: ae_eq_integral => //; [exact: measurableT_comp|
      exact: measurableT_comp|].
    by apply: latent_box_ae => x hx; rewrite box.
  by case/integrableP: giQ.
rewrite /Rintegral ei (integral_density_prob hQ measurableT gi).
congr fine; apply: ae_eq_integral => //.
by apply: latent_box_ae => x hx; rewrite box.
Qed.

(* The law of a point is the average of the two product laws. *)
Theorem latent_point_expectationE (g : paper_main_sample 1 d -> RR) :
  measurable_fun setT g ->
  (latent_side mu d s).-integrable setT (EFin \o g) ->
  (latent_side mu d (- s)).-integrable setT (EFin \o g) ->
  latent_point_expectation s mu d g =
  (\int[latent_side mu d s]_x g x + \int[latent_side mu d (- s)]_x g x) /
    2%:R.
Proof.
move=> mg i1 i2.
have [j1 e1] := latent_side_integral s g hsp mg i1.
have [j2 e2] := latent_side_integral (- s) g hsn mg i2.
rewrite e1 e2 /latent_point_expectation.
under eq_Rintegral do rewrite latent_densityE.
have iZ (f : paper_main_sample 1 d -> RR) :
    U.-integrable setT (fun x => (f x)%:E) ->
    U.-integrable setT (EFin \o (fun x => 2^-1 * f x)).
  move=> fi; apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT 2^-1 fi)) => x _ /=.
  by rewrite EFinM.
have k1 := iZ _ j1; have k2 := iZ _ j2.
transitivity (\int[U]_x (2^-1 * (g x * latent_prod s d x)) +
    \int[U]_x (2^-1 * (g x * latent_prod (- s) d x))).
  by rewrite -RintegralD //; apply: eq_Rintegral => x _; ring.
by rewrite !RintegralZl // -mulrDr mulrC.
Qed.

End latent_point.

(* 3. The two product laws. *)

(* The integral of a finite sum of integrable functions. *)
Lemma Rintegral_sum_ord d' (T : measurableType d') (RT : realType)
    (m : {measure set T -> \bar RT}) n (f : 'I_n -> T -> RT) :
  (forall i, m.-integrable setT (EFin \o f i)) ->
  \int[m]_x (\sum_(i < n) f i x) = \sum_(i < n) \int[m]_x f i x.
Proof.
move=> fi; rewrite /Rintegral.
under eq_integral do rewrite -sumEFin.
rewrite (integral_sum measurableT fi).
have e i : (\int[m]_x (f i x)%:E)%E = (fine (\int[m]_x (f i x)%:E))%:E.
  by rewrite fineK //; exact: integrable_fin_num (fi i).
by rewrite (eq_bigr _ (fun i _ => e i)) sumEFin.
Qed.

Section latent_side_coords.
Variables (mu : probability (measurableTypeR R) R) (d : nat) (a : R).

(* A coordinate has the law paired_law mu a. *)
Lemma latent_side_coord (f : RR -> RR) (j : 'I_(1 * d)) :
  measurable_fun setT f -> (paired_law mu a).-integrable setT (EFin \o f) ->
  (latent_side mu d a).-integrable setT (EFin \o (fun x => f (tnth x j))) /\
  \int[latent_side mu d a]_x f (tnth x j) = \int[paired_law mu a]_t f t.
Proof.
move=> mf fi.
have mfE : measurable_fun setT (EFin \o f) by exact/measurable_EFinP.
have ma : measurable_fun setT (fun t : RR => (`|(f t)%:E|)%E).
  exact: measurableT_comp.
split.
  apply/integrableP; split.
    by apply/measurable_EFinP; exact: measurableT_comp mf (measurable_tnth j).
  rewrite (@ge0_integral_tuple_prod_coord _ _ RR (fun=> paired_law mu a)
    (1 * d) j _ ma (fun t => abse_ge0 _)).
  by case/integrableP: fi.
by rewrite /Rintegral (@integral_tuple_prod_coord _ _ RR
  (fun=> paired_law mu a) (1 * d) j _ mfE).
Qed.

(* Two distinct coordinates are independent. *)
Lemma latent_side_coordM (f g : RR -> RR) (j k : 'I_(1 * d)) : j != k ->
  measurable_fun setT f -> measurable_fun setT g ->
  (paired_law mu a).-integrable setT (EFin \o f) ->
  (paired_law mu a).-integrable setT (EFin \o g) ->
  (latent_side mu d a).-integrable setT
    (EFin \o (fun x => f (tnth x j) * g (tnth x k))) /\
  \int[latent_side mu d a]_x (f (tnth x j) * g (tnth x k)) =
  \int[paired_law mu a]_t f t * \int[paired_law mu a]_t g t.
Proof.
move=> jk mf mg fi gi.
have [gi' ge] := latent_side_coord g k mg gi.
have Hind x t : g (tnth (tuple_set x j t) k) = g (tnth x k).
  by rewrite /tuple_set tnth_mktuple eq_sym (negbTE jk).
have [iP eP] := @integral_tuple_prod_coordM _ _ RR (fun=> paired_law mu a)
  (1 * d) j f (fun x => g (tnth x k)) fi gi' Hind.
have f1 := integrable_fin_num measurableT fi.
have f2 := integrable_fin_num measurableT gi'.
split => //; rewrite /Rintegral eP fineM //.
by congr (_ * _); exact: ge.
Qed.

End latent_side_coords.

(* 4. The statements. *)

Section latent_scope.
Variables (s : R) (mu : probability (measurableTypeR R) R) (d : nat).
Hypotheses (hs : 0 <= s <= 1) (hmu : paired_uniform_spec mu).

Let c0 : (0 : RR) < Num.sqrt 3%:R. Proof. by rewrite sqrtr_gt0 ltr0n. Qed.
Let hP : sym_uniform_spec (Num.sqrt 3%:R : RR) mu. Proof. exact: hmu. Qed.
Let hsp : -1 <= s <= 7%:R / 3%:R.
Proof. exact: (latent_param_range s 0 hs). Qed.
Let hsn : -1 <= - s <= 7%:R / 3%:R.
Proof. exact: (latent_param_range s 1 hs). Qed.

Let mh : measurable_fun setT (paired_kernel : RR -> RR).
Proof. exact: measurable_paired_kernel. Qed.

Let ch : continuous (paired_kernel : RR -> RR).
Proof. exact: continuous_legendre4. Qed.

Let hi a : -1 <= a <= 7%:R / 3%:R ->
  (paired_law mu a).-integrable setT (EFin \o (paired_kernel : RR -> RR)).
Proof. by move=> ha; have [] := legendre_law_cont _ _ c0 hP a _ ha ch. Qed.

Let vh a : -1 <= a <= 7%:R / 3%:R ->
  \int[paired_law mu a]_t paired_kernel t = a / 9%:R.
Proof. exact: (Rintegral_legendre_h _ _ c0 hP). Qed.

Let coord_tnth j (jd : (j < 1 * d)%N) (x : paper_main_sample 1 d) :
  List.nth j (tval x) 0 = tnth x (Ordinal jd).
Proof. by rewrite (tnth_nth 0) List_nthE. Qed.

(* (10): x_j has the law mu, E h(x_j) = 0 and E h(x_j) h(x_k) = s^2 / 81. *)
Lemma latent_covariance_at (j k : nat) : (j < d)%N -> (k < d)%N -> j <> k ->
  (forall A : set (measurableTypeR R), measurable A ->
     latent_point_expectation s mu d
       (fun x => \1_A (List.nth j (tval x) 0)) = fine (mu A)) /\
  latent_point_expectation s mu d
    (fun x => paired_kernel (List.nth j (tval x) 0)) = 0 /\
  latent_point_expectation s mu d
    (fun x => paired_kernel (List.nth j (tval x) 0) *
              paired_kernel (List.nth k (tval x) 0)) = s ^+ 2 / 81%:R.
Proof.
move=> jd kd jk.
have jd' : (j < 1 * d)%N by rewrite mul1n.
have kd' : (k < 1 * d)%N by rewrite mul1n.
set j' := Ordinal jd'; set k' := Ordinal kd'.
have jk' : j' != k' by apply/eqP => -[] /jk.
split; [|split].
- move=> A mA.
  have mf : measurable_fun setT (\1_A : RR -> RR) := measurable_indic mA.
  have fi b : (paired_law mu b).-integrable setT (EFin \o (\1_A : RR -> RR)).
    exact: integrable_indic.
  have [i1 e1] := latent_side_coord mu d s _ j' mf (fi s).
  have [i2 e2] := latent_side_coord mu d (- s) _ j' mf (fi (- s)).
  have mg : measurable_fun setT
      (fun x : paper_main_sample 1 d => (\1_A (tnth x j') : RR)).
    exact: measurableT_comp mf (measurable_tnth j').
  have -> : (fun x : paper_main_sample 1 d =>
      \1_A (List.nth j (tval x) 0) : RR) = (fun x => \1_A (tnth x j')).
    by apply/funext => x; rewrite (coord_tnth j jd').
  rewrite (latent_point_expectationE s mu d hs hmu _ mg i1 i2) e1 e2.
  have ind b : \int[paired_law mu b]_t (\1_A t : RR) =
      fine (paired_law mu b A).
    by rewrite /Rintegral integral_indic // setIT.
  have fin b : paired_law mu b A \is a fin_num := fin_num_measure _ A mA.
  rewrite !ind -fineD // (legendre_law_sum _ _ c0 hP s A hsp hsn mA).
  have fm : mu A \is a fin_num := fin_num_measure _ A mA.
  by rewrite fineM //=; field.
- have mg : measurable_fun setT
      (fun x : paper_main_sample 1 d => (paired_kernel (tnth x j') : RR)).
    exact: measurableT_comp mh (measurable_tnth j').
  have [i1 e1] := latent_side_coord mu d s _ j' mh (hi s hsp).
  have [i2 e2] := latent_side_coord mu d (- s) _ j' mh (hi (- s) hsn).
  have -> : (fun x : paper_main_sample 1 d =>
      paired_kernel (List.nth j (tval x) 0) : RR) =
      (fun x => paired_kernel (tnth x j')).
    by apply/funext => x; rewrite (coord_tnth j jd').
  rewrite (latent_point_expectationE s mu d hs hmu _ mg i1 i2) e1 e2.
  by rewrite (vh _ hsp) (vh _ hsn); field.
have mg : measurable_fun setT (fun x : paper_main_sample 1 d =>
    (paired_kernel (tnth x j') * paired_kernel (tnth x k') : RR)).
  by apply: measurable_funM; exact: measurableT_comp mh (measurable_tnth _).
have [i1 e1] := latent_side_coordM mu d s _ _ j' k' jk' mh mh
  (hi s hsp) (hi s hsp).
have [i2 e2] := latent_side_coordM mu d (- s) _ _ j' k' jk' mh mh
  (hi (- s) hsn) (hi (- s) hsn).
have -> : (fun x : paper_main_sample 1 d =>
    paired_kernel (List.nth j (tval x) 0) *
    paired_kernel (List.nth k (tval x) 0) : RR) =
    (fun x => paired_kernel (tnth x j') * paired_kernel (tnth x k')).
  by apply/funext => x; rewrite (coord_tnth j jd') (coord_tnth k kd').
rewrite (latent_point_expectationE s mu d hs hmu _ mg i1 i2) e1 e2.
by rewrite (vh _ hsp) (vh _ hsn); field.
Qed.

Let cabs : continuous (fun t : RR => `|t|).
Proof. exact: (@norm_continuous _ RR^o). Qed.

Let mabs : measurable_fun setT (fun t : RR => `|t|).
Proof. exact: continuous_measurable_fun. Qed.

Let csq : continuous (fun t : RR => t ^+ 2).
Proof. exact: exprn_continuous. Qed.

Let msq : measurable_fun setT (fun t : RR => t ^+ 2).
Proof. exact: continuous_measurable_fun. Qed.

(* E |x_j| = sqrt 3 (1/2 - a/48) under the product law of paired_law mu a. *)
(* The body is read in ring_scope, not in Stdlib's R_scope. *)
Let kab (a : R) : R := (2%:R^-1 - a / 48%:R)%R.

Let e_abs a (ha : -1 <= a <= 7%:R / 3%:R) (j : 'I_(1 * d)) :
  (latent_side mu d a).-integrable setT (EFin \o (fun x => `|tnth x j|)) /\
  \int[latent_side mu d a]_x `|tnth x j| = Num.sqrt 3%:R * kab a.
Proof.
have [ia _] := legendre_law_cont _ _ c0 hP a _ ha cabs.
have [i e] := latent_side_coord mu d a _ j mabs ia.
split => //; rewrite e (Rintegral_legendre_abs _ _ c0 hP a ha) /kab.
by field.
Qed.

(* E |x_j| |x_k| is 1 for j = k and 3 (1/2 - a/48)^2 for j != k. *)
Let e_abs2 a (ha : -1 <= a <= 7%:R / 3%:R) (j k : 'I_(1 * d)) :
  (latent_side mu d a).-integrable setT
    (EFin \o (fun x => `|tnth x j| * `|tnth x k|)) /\
  \int[latent_side mu d a]_x (`|tnth x j| * `|tnth x k|) =
  if j == k then 1 else 3%:R * kab a ^+ 2.
Proof.
have c2 : (Num.sqrt 3%:R : RR) ^+ 2 = 3%:R by rewrite sqr_sqrtr // ler0n.
(* eqVneq substitutes the value of j == k *)
have [<-|jk] := eqVneq j k.
  have ex (x : paper_main_sample 1 d) :
      `|tnth x j| * `|tnth x j| = tnth x j ^+ 2.
    by rewrite -expr2 real_normK // num_real.
  have [isq _] := legendre_law_cont _ _ c0 hP a _ ha csq.
  have [i e] := latent_side_coord mu d a _ j msq isq.
  split.
    by apply: (eq_integrable measurableT _ _ _ i) => x _ /=; rewrite ex.
  rewrite (eq_Rintegral _ (fun x _ => ex x)) e.
  by rewrite (Rintegral_legendre_sqr _ _ c0 hP a ha) c2 divff // pnatr_eq0.
have [ia _] := legendre_law_cont _ _ c0 hP a _ ha cabs.
have [i e] := latent_side_coordM mu d a _ _ j k jk mabs mabs ia ia.
split => //; rewrite e (Rintegral_legendre_abs _ _ c0 hP a ha) /kab.
transitivity ((Num.sqrt 3%:R : RR) ^+ 2 * (2%:R^-1 - a / 48%:R) ^+ 2).
  by field.
by rewrite c2.
Qed.

Let S (x : paper_main_sample 1 d) := \sum_(j < 1 * d) `|tnth x j|.

Let e_S a (ha : -1 <= a <= 7%:R / 3%:R) :
  (latent_side mu d a).-integrable setT (EFin \o S) /\
  \int[latent_side mu d a]_x S x = (Num.sqrt 3%:R * kab a) *+ (1 * d).
Proof.
have i j := (e_abs a ha j).1.
split.
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun j _ => i j))) => x _ /=.
  by rewrite sumEFin.
rewrite /S (Rintegral_sum_ord _ _ _ _ _ _ i).
rewrite (eq_bigr (fun=> Num.sqrt 3%:R * kab a) (fun j _ => (e_abs a ha j).2)).
by rewrite sumr_const card_ord.
Qed.

Let e_S2 a (ha : -1 <= a <= 7%:R / 3%:R) :
  (latent_side mu d a).-integrable setT (EFin \o (fun x => S x ^+ 2)) /\
  \int[latent_side mu d a]_x (S x ^+ 2) =
  (1 - 3%:R * kab a ^+ 2 + (3%:R * kab a ^+ 2) *+ (1 * d)) *+ (1 * d).
Proof.
set v := 3%:R * kab a ^+ 2.
have ex x : S x ^+ 2 =
    \sum_(j < 1 * d) \sum_(k < 1 * d) (`|tnth x j| * `|tnth x k|).
  by rewrite /S expr2 mulr_suml; apply: eq_bigr => j _; rewrite mulr_sumr.
have i j k := (e_abs2 a ha j k).1.
have ij j : (latent_side mu d a).-integrable setT
    (EFin \o (fun x => \sum_(k < 1 * d) (`|tnth x j| * `|tnth x k|))).
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun k _ => i j k))) => x _ /=.
  by rewrite sumEFin.
have ek j k : \int[latent_side mu d a]_x (`|tnth x j| * `|tnth x k|) =
    (1 - v) * (j == k)%:R + v.
  by rewrite (e_abs2 a ha j k).2 /v; case: eqP => _;
    rewrite ?mulr1 ?subrK ?mulr0 ?add0r.
(* the row j: E |x_j|^2 = 1 and E |x_j| |x_k| = v for k != j *)
have row j : \int[latent_side mu d a]_x
    (\sum_(k < 1 * d) (`|tnth x j| * `|tnth x k|)) = 1 - v + v *+ (1 * d).
  rewrite (Rintegral_sum_ord _ _ _ _ _ _ (i j)) (eq_bigr _ (fun k _ => ek j k)).
  rewrite big_split /= sumr_const card_ord -mulr_sumr (bigD1 j) //= eqxx.
  have z : \sum_(k < 1 * d | k != j) ((j == k)%:R : RR) = 0.
    by apply: big1 => k kj; rewrite eq_sym (negbTE kj).
  by rewrite z addr0 mulr1.
split.
  apply: (eq_integrable measurableT _ _ _ (integrable_sum measurableT
    (index_enum 'I_(1 * d)) (P := xpredT) (fun j _ => ij j))) => x _ /=.
  by rewrite sumEFin ex.
rewrite (eq_Rintegral _ (fun x _ => ex x)) (Rintegral_sum_ord _ _ _ _ _ _ ij).
by rewrite (eq_bigr _ (fun j _ => row j)) sumr_const card_ord.
Qed.

(* (11): F = (sum_j |x_j|) / sqrt d has variance 1/4 + (d - 1) s^2 / 768. *)
Lemma latent_variance_at : (0 < d)%N ->
  let F := fun x : paper_main_sample 1 d =>
    (\sum_(j < d) `|List.nth j (tval x) 0|) / Num.sqrt d%:R in
  latent_point_expectation s mu d (fun x => F x ^+ 2) -
    latent_point_expectation s mu d F ^+ 2 =
  4%:R^-1 + (d%:R - 1) * s ^+ 2 / 768%:R.
Proof.
move=> d0 F.
pose w : RR := Num.sqrt d%:R.
have w0 : 0 < w by rewrite /w sqrtr_gt0 ltr0n.
have w2 : w ^+ 2 = d%:R by rewrite /w sqr_sqrtr // ler0n.
have FS x : F x = S x / w.
  rewrite /F /S /w; congr (_ / _).
  have e : index_iota 0 (1 * d) = index_iota 0 d by rewrite mul1n.
  transitivity (\sum_(j < 1 * d) `|List.nth j (tval x) 0|); last first.
    by apply: eq_bigr => j _; rewrite (tnth_nth 0) List_nthE.
  by rewrite -!(big_mkord xpredT (fun j => `|List.nth j (tval x) 0|)) e.
have eF : F = (fun x => S x / w) by apply/funext => x; exact: FS.
rewrite eF.
have mS : measurable_fun setT (fun x : paper_main_sample 1 d => S x : RR).
  apply: measurable_sum => j.
  exact: measurableT_comp mabs (measurable_tnth j).
have mF : measurable_fun setT (fun x : paper_main_sample 1 d => S x / w : RR).
  by apply: measurable_funM => //; exact: measurable_cst.
have eF2 : (fun x : paper_main_sample 1 d => (S x / w) ^+ 2) =
    (fun x => S x ^+ 2 / d%:R).
  by apply/funext => x; rewrite expr_div_n w2.
rewrite eF2.
have iZ (a : R) (g : paper_main_sample 1 d -> RR) (k : RR) :
    (latent_side mu d a).-integrable setT (EFin \o g) ->
    (latent_side mu d a).-integrable setT (EFin \o (fun x => g x / k)).
  move=> gi; apply: (eq_integrable measurableT _ _ _
    (integrableZl measurableT k^-1 gi)) => x _ /=.
  by rewrite -EFinM mulrC.
have [iSs eSs] := e_S s hsp.
have [iSn eSn] := e_S (- s) hsn.
have [iS2s eS2s] := e_S2 s hsp.
have [iS2n eS2n] := e_S2 (- s) hsn.
have mF2 : measurable_fun setT
    (fun x : paper_main_sample 1 d => S x ^+ 2 / d%:R : RR).
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurableT_comp msq mS.
rewrite (latent_point_expectationE s mu d hs hmu _ mF2
  (iZ _ _ _ iS2s) (iZ _ _ _ iS2n)).
rewrite (latent_point_expectationE s mu d hs hmu _ mF
  (iZ _ _ _ iSs) (iZ _ _ _ iSn)).
rewrite !RintegralZr // eSs eSn eS2s eS2n.
(* the arithmetic, with sqrt 3 ^ 2 = 3 and sqrt d ^ 2 = d *)
have c2 : (Num.sqrt 3%:R : RR) ^+ 2 = 3%:R by rewrite sqr_sqrtr // ler0n.
have D0 : (d%:R : RR) != 0 by rewrite pnatr_eq0 -lt0n.
have wn : w != 0 by rewrite gt_eqF.
have -> : ((Num.sqrt 3%:R * kab s *+ (1 * d) / w +
    Num.sqrt 3%:R * kab (- s)%R *+ (1 * d) / w) / 2%:R) ^+ 2 =
    (Num.sqrt 3%:R : RR) ^+ 2 * ((kab s + kab (- s)%R) *+ (1 * d)) ^+ 2 /
    (4%:R * w ^+ 2).
  by field.
by rewrite c2 w2 /kab; field.
Qed.

End latent_scope.
