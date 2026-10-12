(* The integral formula of the curve at fourth moment kappa, at Stdlib's
   R: item S5 of phase 11 (notes/phase11-plan.md, section 5; the math plan
   notes/general-fourth-moment-condition-plan.md, sections 2 and 3; lane B).
   The definitions are those of ConditionKappaDefinitions; the root and the
   cutoff are item S1 (Scalar).

   Setting. nu is the semicircle law on [-sqrt 2, sqrt 2], of density
   sc2_dens x = sqrt (2 - x^2) / pi (universality_semicircle_density), and
   J(w) = v(w) + w m(w) (condition_kappa_J), so that
   alpha(C, kappa) = J(ell) - J(u). Since (x - w)_+^2 + w (x - w)_+ =
   x (x - w)_+, J(w) = sc2_J w = int x (x - w)_+ dnu(x)
   (condition_kappa_JE).

   Proved, for every real w and h.
   - is_derive_taylor: a quadratic Taylor bound
     |F(x + h) - F(x) - h g| <= K h^2 gives is_derive x 1 F g.
   - upper_kink_abs, upper_kink_zero: with
     q(x) = (x - w - h)_+ - (x - w)_+ + h 1_{x >= w}, |q(x)| <= |h|, and
     q(x) = 0 when |x - w| > |h|.
   - sc2_dens_xle: |x| sc2_dens x <= 1 / pi, since
     2 |x| sqrt (2 - x^2) <= x^2 + (2 - x^2).
   - sc2_J_taylor: |J(w + h) - J(w) + h psi(w)| <= (2 / pi) h^2, with
     psi(w) = int x 1_{x >= w} dnu(x) (sc2_psi): the difference is
     int x q(x) dnu(x), bounded by (1 / pi) |h| times the Lebesgue measure
     2 |h| of [w - |h|, w + |h|].
   - sc2_psiE: psi(w) = phi(w) = (2 - w^2)_+^(3/2) / (3 pi) (sc2_phi), by
     the fundamental theorem of calculus on [w, sqrt 2] (continuous_FTC2)
     with the antiderivative -(2 - x^2)^(3/2) / (3 pi) of x sc2_dens x for
     -sqrt 2 <= w < sqrt 2; both sides are 0 for w >= sqrt 2, and psi is
     constant on ]-oo, -sqrt 2].
   - sc2_J_derive, sc2_J_integral: J has derivative -phi everywhere, so
     J(a) - J(b) is the Lebesgue integral of phi over [a, b] for a < b
     (Rintegral_FTC_R of library/probability/semicircle_law.v).
   - condition_kappa_integral_holds: conjunct (c) of the curve statement,
     condition_kappa_integral kappa for kappa > 1:
       alpha(C, kappa) = (3 pi)^-1 int_[ell, u] (2 - z^2)^(3/2) dz,
     with -sqrt 2 < ell < u (condition_kappa_ell_spec).
   - sc2_A_derive, condition_kappa_alpha_arcsine: the arcsine evaluation,
     a supporting lemma. With
       A(z) = arcsin (z / sqrt 2) / (2 pi)
              + z (5 - z^2) sqrt (2 - z^2) / (12 pi),
     A' = (2 - z^2)^(3/2) / (3 pi) on ]-sqrt 2, sqrt 2[ (is_derive1_asin),
     so alpha(C, kappa) = A(u) - A(ell) for C > 1 and kappa > 1. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From mathcomp Require Import sequences trigo realfun derive ftc numfun.
From GaussianAnalysis.probability Require Import semicircle_law.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaCurveStatement.
From EllipsoidUniversality.Gaussian Require Import Cones Threshold.
From EllipsoidUniversality.ConditionKappa Require Import Scalar.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section taylor_derive.
Context {R : realType}.

(* A derivative given by a Taylor bound with a quadratic remainder. *)
Lemma is_derive_taylor (F : R -> R) (x g K : R) :
  (forall h : R, `|F (x + h) - F x - h * g| <= K * h ^+ 2) ->
  is_derive x 1 F g.
Proof.
move=> hT.
have K1 : 0 < `|K| + 1 by rewrite ltr_pwDr.
have hlim : (fun h : R => h^-1 *: ((F \o shift x) (h *: 1) - F x)) @ 0^'
    --> g.
  apply/cvgrPdist_lt => e e0.
  have eK : 0 < e / (`|K| + 1) by rewrite divr_gt0.
  near=> h.
  have h0 : h != 0 by near: h; exact: nbhs_dnbhs_neq.
  have hs : `|h| < e / (`|K| + 1) by near: h; exact: dnbhs0_lt.
  have -> : (F \o shift x) (h *: 1) = F (x + h).
    by rewrite /= [h *: 1]mulr1 addrC.
  have -> : h^-1 *: (F (x + h) - F x) = h^-1 * (F (x + h) - F x) by [].
  have E : g - h^-1 * (F (x + h) - F x) =
      - (h^-1 * (F (x + h) - F x - h * g)).
    by field.
  rewrite E normrN normrM normfV.
  have hp : 0 < `|h| by rewrite normr_gt0.
  apply: le_lt_trans (_ : _ <= `|h|^-1 * (K * h ^+ 2)) _.
    by apply: ler_wpM2l; [rewrite invr_ge0 ltW | exact: hT].
  have -> : `|h|^-1 * (K * h ^+ 2) = K * `|h|.
    rewrite -[h ^+ 2]real_normK ?num_real //.
    by have := lt0r_neq0 hp; move=> hn; field.
  apply: le_lt_trans (_ : _ <= `|K| * `|h|) _.
    by apply: ler_wpM2r; [exact: ltW | exact: ler_norm].
  rewrite ltr_pdivlMr // in hs.
  apply: le_lt_trans (_ : _ <= (`|K| + 1) * `|h|) _.
    by apply: ler_wpM2r; [exact: ltW | rewrite lerDl].
  by rewrite mulrC.
apply: DeriveDef; first exact: cvgP hlim.
exact: cvg_lim hlim.
Unshelve. all: by end_near.
Qed.

End taylor_derive.

Section semicircle_J.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).

(* The density of the semicircle law on [-sqrt 2, sqrt 2]. *)
Definition sc2_dens (x : R) : R := Num.sqrt (2 - x ^+ 2) / pi.

Let pi0 : 0 < pi :> R. Proof. exact: pi_gt0. Qed.
Let sq2n : Num.sqrt 2 != 0 :> R.
Proof. by rewrite gt_eqF // sqrtr_gt0 ltr0n. Qed.
Let sq2 : Num.sqrt 2 ^+ 2 = 2 :> R. Proof. by rewrite sqr_sqrtr // ler0n. Qed.

Lemma sc2_densE x : sc2_dens x = semicircle_pdf (Num.sqrt 2) x.
Proof.
rewrite semicircle_pdfE // sq2 /sc2_dens.
have pn : pi != 0 :> R by rewrite gt_eqF.
by move: (pi : R) pn => p pn; field.
Qed.

Lemma sc2_dens_ge0 x : 0 <= sc2_dens x.
Proof. by rewrite /sc2_dens divr_ge0 ?sqrtr_ge0 // ltW. Qed.

Lemma continuous_sc2_dens : continuous sc2_dens.
Proof.
have -> : sc2_dens = semicircle_pdf (Num.sqrt 2).
  by apply/funext => x; exact: sc2_densE.
exact: continuous_semicircle_pdf.
Qed.

(* |x| sqrt (2 - x^2) <= 1. *)
Lemma sc2_dens_xle x : `|x| * sc2_dens x <= pi^-1.
Proof.
rewrite /sc2_dens mulrA ler_pdivrMr // mulVf ?gt_eqF //.
have [h|h] := leP (x ^+ 2) 2; last first.
  by rewrite ler0_sqrtr ?mulr0 ?ler01 // subr_le0 ltW.
set s := Num.sqrt (2 - x ^+ 2).
have s2 : s ^+ 2 = 2 - x ^+ 2 by rewrite sqr_sqrtr // subr_ge0.
have nx : `|x| ^+ 2 = x ^+ 2 by rewrite real_normK ?num_real.
have : 0 <= (`|x| - s) ^+ 2 by exact: sqr_ge0.
by rewrite sqrrB nx s2; lra.
Qed.

Lemma sc2_dens_integrable (f : R -> R) : continuous f ->
  mu.-integrable setT (EFin \o (fun x => f x * sc2_dens x)).
Proof.
move=> cf; have := integrable_semicircle_pdfM sq2n cf.
by apply: eq_integrable => // x _; rewrite /= sc2_densE.
Qed.

(* The kink of x |-> (x - w)_+ at w. *)
Lemma upper_kink_abs (x w h : R) :
  `|Num.max (x - (w + h)) 0 - Num.max (x - w) 0 + (if w <= x then h else 0)|
  <= `|h|.
Proof.
have [xw|xw] := leP w x => /=.
  have [a|a] := leP (x - (w + h)) 0; have [b|b] := leP (x - w) 0.
  - by rewrite subrr add0r.
  - rewrite sub0r; have [h0|h0] := leP 0 h; last by lra.
    by rewrite (ger0_norm h0) ger0_norm; lra.
  - have e : x - (w + h) - 0 + h = 0 by lra.
    by rewrite e normr0 normr_ge0.
  - have e : x - (w + h) - (x - w) + h = 0 by ring.
    by rewrite e normr0 normr_ge0.
rewrite addr0.
have [a|a] := leP (x - (w + h)) 0; have [b|b] := leP (x - w) 0.
- by rewrite subrr normr0 normr_ge0.
- by lra.
- rewrite subr0 gtr0_norm //; have [h0|h0] := leP 0 h; first by lra.
  by rewrite ltr0_norm //; lra.
- by lra.
Qed.

Lemma upper_kink_zero (x w h : R) : `|h| < `|x - w| ->
  Num.max (x - (w + h)) 0 - Num.max (x - w) 0 + (if w <= x then h else 0)
  = 0.
Proof.
have hn := normr_ge0 h.
have hN : - h <= `|h| by rewrite -normrN ler_norm.
have hP : h <= `|h| by exact: ler_norm.
have [xw|xw] := leP w x => /= hh.
  have xw' : 0 <= x - w by rewrite subr_ge0.
  rewrite (ger0_norm xw') in hh.
  have [a|a] := leP (x - (w + h)) 0; first by lra.
  have [b|b] := leP (x - w) 0; first by lra.
  by ring.
have xw' : x - w < 0 by rewrite subr_lt0.
rewrite (ltr0_norm xw') in hh.
have [a|a] := leP (x - (w + h)) 0; last by lra.
have [b|b] := leP (x - w) 0; last by lra.
by rewrite subrr addr0.
Qed.

(* J(w) = int x (x - w)_+ dnu, psi(w) = int x 1_{x >= w} dnu, and the
   target derivative phi(w) = (2 - w^2)_+^(3/2) / (3 pi). *)
Definition sc2_J (w : R) : R :=
  \int[mu]_x (x * Num.max (x - w) 0 * sc2_dens x).
Definition sc2_psi (w : R) : R :=
  \int[mu]_x (x * (if w <= x then 1 else 0) * sc2_dens x).
Definition sc2_phi (w : R) : R := Num.sqrt (2 - w ^+ 2) ^+ 3 / (3 * pi).

Local Notation lint f := (mu.-integrable setT (EFin \o f)).

Let lintZ (k : R) (f : R -> R) : lint f -> lint (fun x => k * f x).
Proof.
move=> fi; have := integrableZl measurableT k fi.
by apply: eq_integrable => // x _; rewrite /= EFinM.
Qed.

Let lintD (f g : R -> R) : lint f -> lint g -> lint (fun x => f x + g x).
Proof.
move=> fi gi; have := integrableD measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinD.
Qed.

Let lintB (f g : R -> R) : lint f -> lint g -> lint (fun x => f x - g x).
Proof.
move=> fi gi; have := integrableB measurableT fi gi.
by apply: eq_integrable => // x _; rewrite /= EFinB.
Qed.

Let lint_norm (f : R -> R) : lint f -> lint (fun x => `|f x|).
Proof.
move=> fi; have := integrable_abse fi.
by apply: eq_integrable => // x _; rewrite /= abse_EFin.
Qed.

Let cj (v : R) : continuous (fun x : R => x * Num.max (x - v) 0).
Proof.
move=> x; apply: cvgM; first exact: cvg_id.
apply: (continuous_max (f := fun y : R => y - v) (g := fun=> 0)).
  by apply: cvgB; [exact: cvg_id|exact: cvg_cst].
exact: cvg_cst.
Qed.

Let ind_ge (w : R) :
  (fun x : R => if w <= x then 1 else 0) = \1_`[w, +oo[ :> (R -> R).
Proof.
apply/funext => x; rewrite indicE.
have [xw|xw] := leP w x.
  have hx : x \in `[w, +oo[ by rewrite in_itv /= andbT.
  by rewrite mem_set.
have hx : ~ (x \in `[w, +oo[) by apply/negP; rewrite in_itv /= andbT -ltNge.
by rewrite memNset.
Qed.

Let ipsi (w : R) : lint (fun x => x * (if w <= x then 1 else 0) * sc2_dens x).
Proof.
have ix : lint (fun x => x * sc2_dens x) :=
  sc2_dens_integrable _ (fun x => cvg_id).
apply: (le_integrable measurableT _ _ ix).
- apply/measurable_EFinP.
  have -> : (fun x : R => x * (if w <= x then 1 else 0) * sc2_dens x) =
      (fun x => x * \1_`[w, +oo[ x * sc2_dens x).
    by apply/funext => x; rewrite -(ind_ge w).
  apply: measurable_funM.
    by apply: measurable_funM => //; exact: measurable_indic.
  exact: continuous_measurable_fun continuous_sc2_dens.
- move=> x _ /=; rewrite lee_fin !normrM.
  case: (w <= x); first by rewrite normr1 mulr1.
  rewrite normr0 mulr0 mul0r.
  by apply: mulr_ge0; [exact: normr_ge0 | apply: mulr_ge0; exact: normr_ge0].
Qed.

(* |J(w + h) - J(w) + h psi(w)| <= (2 / pi) h^2. *)
Lemma sc2_J_taylor (w h : R) :
  `|sc2_J (w + h) - sc2_J w - h * (- sc2_psi w)| <= 2 / pi * h ^+ 2.
Proof.
pose q (x : R) := Num.max (x - (w + h)) 0 - Num.max (x - w) 0 +
  (if w <= x then h else 0).
have i1 := sc2_dens_integrable _ (cj (w + h)).
have i2 := sc2_dens_integrable _ (cj w).
have i3 := lintZ h _ (ipsi w).
have iq : lint (fun x => x * q x * sc2_dens x).
  have := lintD _ _ (lintB _ _ i1 i2) i3.
  by apply: eq_integrable => // x _ /=; rewrite /q; case: (w <= x);
    congr EFin; ring.
have E : sc2_J (w + h) - sc2_J w - h * (- sc2_psi w) =
    \int[mu]_x (x * q x * sc2_dens x).
  rewrite mulrN opprK /sc2_J /sc2_psi -(RintegralZl h measurableT (ipsi w)).
  rewrite -(RintegralB measurableT i1 i2).
  rewrite -(RintegralD measurableT (lintB _ _ i1 i2) i3).
  by apply: eq_Rintegral => x _; rewrite /q; case: (w <= x); ring.
rewrite E.
pose I := [set` Interval (BSide true (w - `|h|)) (BSide false (w + `|h|))].
have iI : lint (\1_I : R -> R) :=
  integrable_indic_itv (w - `|h|) (w + `|h|) true false.
have iB : lint (fun x => pi^-1 * `|h| * \1_I x) := lintZ _ _ iI.
have bnd x : `|x * q x * sc2_dens x| <= pi^-1 * `|h| * \1_I x.
  rewrite indicE normrM (ger0_norm (sc2_dens_ge0 x)) normrM.
  have [xi|xi] := leP (`|x - w|) (`|h|).
  - have xI : x \in I by apply: mem_set; rewrite /I /= in_itv /= -ler_distl.
    rewrite xI mulr1.
    have k : `|q x| <= `|h| := upper_kink_abs x w h.
    have s := sc2_dens_xle x.
    have qx0 : 0 <= `|q x| := normr_ge0 _.
    have xs0 : 0 <= `|x| * sc2_dens x.
      by rewrite mulr_ge0 ?sc2_dens_ge0 ?normr_ge0.
    have e : `|x| * `|q x| * sc2_dens x = (`|x| * sc2_dens x) * `|q x| by ring.
    by rewrite e; apply: ler_pM.
  - rewrite /q upper_kink_zero // normr0 mulr0 mul0r.
    apply: mulr_ge0; last exact: ler0n.
    by apply: mulr_ge0; [rewrite invr_ge0 ltW | exact: normr_ge0].
have intI : \int[mu]_x (\1_I x : R) = 2 * `|h|.
  rewrite /Rintegral.
  have -> : (\int[mu]_x (\1_I x : R)%:E)%E = mu (I `&` setT).
    exact: (integral_indic mu measurableT (measurable_itv _)).
  rewrite setIT /I lebesgue_measure_itv /= lte_fin.
  case: ifPn => hc; first by rewrite -EFinB /=; ring.
  move: hc; rewrite -leNgt => hc.
  have h0 : `|h| = 0.
    by apply/eqP; rewrite eq_le normr_ge0 andbT; lra.
  by rewrite h0 mulr0.
apply: le_trans (le_normr_Rintegral measurableT iq) _.
apply: le_trans (le_Rintegral measurableT (lint_norm _ iq) iB
  (fun x _ => bnd x)) _.
rewrite (RintegralZl (pi^-1 * `|h|) measurableT iI) intI.
rewrite -[h ^+ 2]real_normK ?num_real //.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by move: (pi : R) (`|h|) => p a; ring.
Qed.


Let sq2_ge (x : R) : Num.sqrt 2 <= x -> 2 - x ^+ 2 <= 0.
Proof.
move=> h; have s0 : 0 <= Num.sqrt 2 :> R := sqrtr_ge0 _.
have x0 : 0 <= x := le_trans s0 h.
by rewrite subr_le0 -{1}sq2 ler_pXn2r // ?nnegrE.
Qed.

Let sq2_le (x : R) : x <= - Num.sqrt 2 -> 2 - x ^+ 2 <= 0.
Proof. by move=> h; rewrite -sqrrN; apply: sq2_ge; rewrite lerNr. Qed.

Let sc2_dens_out (x : R) : 2 - x ^+ 2 <= 0 -> sc2_dens x = 0.
Proof. by move=> h; rewrite /sc2_dens ler0_sqrtr // mul0r. Qed.

Let sc2_phi_out (x : R) : 2 - x ^+ 2 <= 0 -> sc2_phi x = 0.
Proof. by move=> h; rewrite /sc2_phi ler0_sqrtr // expr0n /= mul0r. Qed.

(* The antiderivative of x sc2_dens x on ]-sqrt 2, sqrt 2[. *)
Let su (x : R) : R := 2 - x ^+ 2.
Let sG (x : R) : R := - 3^-1 * (su x * Num.sqrt (su x)).
Let sg (x : R) : R := x * Num.sqrt (su x).

Let dsu (y : R) : is_derive y 1 su (- (2 * y)).
Proof.
have := is_deriveB (is_derive_cst (2 : R) y 1)
  (@is_deriveX _ _ (@id R) 2 y 1 1 (is_derive_id y 1)).
have -> : (cst 2 - (@id R) ^+ 2) = su by apply/funext => z; rewrite /su /=.
move=> h; apply: (is_derive_eq h).
by rewrite /GRing.scale /= sub0r mulr1 expr1.
Qed.

Let dsG (x : R) : 0 < su x -> is_derive x 1 sG (sg x).
Proof.
move=> ux.
have ds := @is_derive1_comp R Num.sqrt su x _ _ (is_derive1_sqrt ux) (dsu x).
have := is_deriveZ (- 3^-1) (is_deriveM (dsu x) ds).
have -> : (- 3^-1) \*: (su * (Num.sqrt \o su)) = sG.
  by apply/funext => z; rewrite /sG /= /GRing.scale /=.
move=> h; apply: (is_derive_eq h); rewrite /sg /GRing.scale /=.
have s0 : 0 < Num.sqrt (su x) by rewrite sqrtr_gt0.
have us : su x = Num.sqrt (su x) ^+ 2 by rewrite sqr_sqrtr // ltW.
rewrite [in X in X * (_ * _)]us.
move: (Num.sqrt (su x)) s0 => q q0.
have qn0 : q != 0 by rewrite gt_eqF.
by field.
Qed.

Lemma continuous_sqrt2 : continuous (fun x : R => Num.sqrt (2 - x ^+ 2)).
Proof.
move=> x; apply: continuous_comp; last exact: sqrt_continuous.
by apply: continuousB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
Qed.

Let csG : continuous sG.
Proof.
move=> x; apply: cvgM; first exact: cvg_cst.
apply: cvgM; last exact: continuous_sqrt2.
by apply: cvgB; [exact: cvg_cst|exact: (@continuousM _ _ id id)].
Qed.

(* sc2_psi w = (2 - w^2)^(3/2) / (3 pi) for -sqrt 2 <= w < sqrt 2. *)
Let sc2_psi_in (w : R) : - Num.sqrt 2 <= w -> w < Num.sqrt 2 ->
  sc2_psi w = sc2_phi w.
Proof.
move=> w1 w2.
have pn : pi != 0 :> R by rewrite gt_eqF.
have -> : sc2_psi w = \int[mu]_(x in `[w, Num.sqrt 2]) (x * sc2_dens x).
  rewrite Rintegral_mkcond /sc2_psi; apply: eq_Rintegral => x _.
  rewrite patchE; have [wx|wx] := leP w x; rewrite /=.
    case: ifPn => xD; first by rewrite mulr1.
    have xs : Num.sqrt 2 < x.
      rewrite ltNge; apply/negP => xs; move/negP: xD; apply.
      by apply: mem_set; rewrite /= in_itv /= wx xs.
    by rewrite mulr1 sc2_dens_out ?mulr0 // sq2_ge // ltW.
  rewrite mulr0 mul0r; case: ifPn => xD //.
  have := set_mem xD; rewrite /= in_itv /= => /andP[wx' _].
  by move: wx'; rewrite leNgt wx.
have uin x : x \in `]w, Num.sqrt 2[ -> 0 < su x.
  rewrite in_itv /= => /andP[a b].
  rewrite /su subr_gt0 -sq2 -[x ^+ 2]real_normK ?num_real //.
  rewrite ltr_pXn2r // ?nnegrE // ?normr_ge0 ?sqrtr_ge0 // ltr_norml.
  by rewrite b andbT; apply: le_lt_trans a.
have cf : {within `[w, Num.sqrt 2], continuous (fun x => x * sc2_dens x)}.
  apply: continuous_subspaceT => x; apply: cvgM; first exact: cvg_id.
  exact: continuous_sc2_dens.
have cF : continuous (fun x => pi^-1 * sG x).
  by move=> x; apply: cvgM; [exact: cvg_cst | exact: csG].
have dF : derivable_oo_LRcontinuous (fun x => pi^-1 * sG x) w (Num.sqrt 2).
  split.
  - move=> x xI.
    exact: (@ex_derive _ _ _ _ _ _ _ (is_deriveZ _ (dsG x (uin x xI)))).
  - by apply: cvg_at_right_filter; exact: cF.
  - by apply: cvg_at_left_filter; exact: cF.
have F'f : {in `]w, Num.sqrt 2[, (fun x => pi^-1 * sG x)^`() =1
    (fun x => x * sc2_dens x)}.
  move=> x xI.
  have d := is_deriveZ pi^-1 (dsG x (uin x xI)).
  rewrite derive1E (@derive_val _ _ _ _ _ _ _ d).
  rewrite /GRing.scale /= /sg /sc2_dens /su.
  by move: (pi : R) (Num.sqrt _) => p q; ring.
have ftc := continuous_FTC2 w2 cf dF F'f.
rewrite /Rintegral ftc /=.
rewrite /sG /su sq2 subrr sqrtr0 mul0r mulr0 mulr0 /sc2_phi.
have uw : 0 <= 2 - w ^+ 2.
  rewrite subr_ge0 -{1}sq2 -[w ^+ 2]real_normK ?num_real //.
  rewrite ler_pXn2r // ?nnegrE // ?normr_ge0 ?sqrtr_ge0 // ler_norml.
  by rewrite w1 ltW.
have e3 : Num.sqrt (2 - w ^+ 2) ^+ 3 =
    (2 - w ^+ 2) * Num.sqrt (2 - w ^+ 2).
  by rewrite exprS (sqr_sqrtr uw) mulrC.
rewrite e3; move: (2 - w ^+ 2) (Num.sqrt _) => a b.
by move: (pi : R) pn => p pn; field.
Qed.

Lemma sc2_psiE (w : R) : sc2_psi w = sc2_phi w.
Proof.
have s0 : 0 < Num.sqrt 2 :> R by rewrite sqrtr_gt0 ltr0n.
have [ws|ws] := leP (Num.sqrt 2) w.
  rewrite sc2_phi_out ?sq2_ge // /sc2_psi.
  transitivity (\int[mu]_x (0 : R)); last first.
    by rewrite Rintegral_cst // mul0r.
  apply: eq_Rintegral => x _.
  have [wx|wx] := leP w x; last by rewrite mulr0 mul0r.
  by rewrite sc2_dens_out ?mulr0 // sq2_ge // (le_trans ws).
have [wl|wl] := ltP w (- Num.sqrt 2); last exact: sc2_psi_in.
have -> : sc2_psi w = sc2_psi (- Num.sqrt 2).
  rewrite /sc2_psi; apply: eq_Rintegral => x _.
  have [xl|xl] := leP (- Num.sqrt 2) x.
    by rewrite (le_trans (ltW wl) xl).
  rewrite sc2_dens_out ?mulr0 //; exact: sq2_le (ltW xl).
rewrite sc2_psi_in ?lexx ?gtrN // !sc2_phi_out //; last exact: sq2_le (ltW wl).
by rewrite sqrrN sq2 subrr.
Qed.

(* J' = - phi. *)
Lemma sc2_J_derive (w : R) : is_derive w 1 sc2_J (- sc2_phi w).
Proof.
apply: (@is_derive_taylor _ sc2_J w (- sc2_phi w) (2 / pi)) => h.
by rewrite -sc2_psiE; exact: sc2_J_taylor.
Qed.

Lemma continuous_sqrt2_cube :
  continuous (fun y : R => Num.sqrt (2 - y ^+ 2) ^+ 3).
Proof.
move=> y; apply: (@continuous_comp _ _ _
  (fun y : R => Num.sqrt (2 - y ^+ 2)) (fun y : R => y ^+ 3)).
  exact: continuous_sqrt2.
exact: exprn_continuous.
Qed.

Lemma continuous_sc2_phi : continuous sc2_phi.
Proof.
by move=> x; apply: cvgM; [exact: continuous_sqrt2_cube | exact: cvg_cst].
Qed.

(* J(a) - J(b) = int_[a, b] phi. *)
Lemma sc2_J_integral (a b : R) : a < b ->
  sc2_J a - sc2_J b = \int[mu]_(x in `[a, b]) sc2_phi x.
Proof.
move=> ab.
have dJ (x : R) : is_derive x 1 (fun y => - sc2_J y) (sc2_phi x).
  have := is_deriveN (sc2_J_derive x); rewrite opprK.
  by move=> h.
rewrite (Rintegral_FTC_R ab continuous_sc2_phi dJ).
by rewrite opprK addrC.
Qed.

End semicircle_J.

(* The arcsine primitive of phi. *)

Section arcsine.
Context {R : realType}.

(* A(z) = arcsin (z / sqrt 2) / (2 pi)
          + z (5 - z^2) sqrt (2 - z^2) / (12 pi). *)
Definition sc2_A (z : R) : R :=
  (2 * pi)^-1 * asin ((Num.sqrt 2)^-1 * z) +
  (12 * pi)^-1 * ((5 * z - z ^+ 3) * Num.sqrt (2 - z ^+ 2)).

Lemma sc2_A_derive (z : R) : - Num.sqrt 2 < z < Num.sqrt 2 ->
  is_derive z 1 sc2_A (sc2_phi z).
Proof.
move=> /andP[z1 z2].
have r0 : 0 < Num.sqrt 2 :> R by rewrite sqrtr_gt0 ltr0n.
have rn : Num.sqrt 2 != 0 :> R by rewrite gt_eqF.
have r2 : Num.sqrt 2 ^+ 2 = 2 :> R by rewrite sqr_sqrtr // ler0n.
have pn : pi != 0 :> R by rewrite gt_eqF // pi_gt0.
(* the positive quantities *)
have zs : z ^+ 2 < 2.
  rewrite -r2 -[z ^+ 2]real_normK ?num_real //.
  by rewrite ltr_pXn2r // ?nnegrE // ?normr_ge0 ?ltW // ltr_norml z1 z2.
have u0 : 0 < 2 - z ^+ 2 by rewrite subr_gt0.
set s := Num.sqrt (2 - z ^+ 2).
have s0 : 0 < s by rewrite sqrtr_gt0.
have s2 : s ^+ 2 = 2 - z ^+ 2 by rewrite sqr_sqrtr // ltW.
(* the arcsine part *)
have y1 : -1 < (Num.sqrt 2)^-1 * z < 1.
  by rewrite mulrC ltr_pdivlMr // ltr_pdivrMr // mulN1r mul1r z1 z2.
have dlin : is_derive z 1 (fun y : R => (Num.sqrt 2)^-1 * y) (Num.sqrt 2)^-1.
  have := is_deriveZ (Num.sqrt 2)^-1 (is_derive_id z (1 : R)).
  by move=> h; apply: (is_derive_eq h); rewrite /GRing.scale /= mulr1.
have dasin := @is_derive1_comp R asin (fun y : R => (Num.sqrt 2)^-1 * y) z _ _
  (is_derive1_asin y1) dlin.
set t := Num.sqrt (1 - ((Num.sqrt 2)^-1 * z) ^+ 2) in dasin.
have tE : t = s / Num.sqrt 2.
  have q1 : 1 - ((Num.sqrt 2)^-1 * z) ^+ 2 = (2 - z ^+ 2) / 2.
    by rewrite exprMn exprVn r2; field.
  have t0 : 0 <= t := sqrtr_ge0 _.
  have st0 : 0 <= s / Num.sqrt 2 by rewrite divr_ge0 // ltW.
  apply/eqP; rewrite -(eqrXn2 (isT : (0 < 2)%N) t0 st0).
  by rewrite /t q1 sqr_sqrtr ?divr_ge0 ?ltW // expr_div_n s2 r2.
(* the algebraic part *)
have du : is_derive z 1 (fun y : R => 2 - y ^+ 2) (- (2 * z)).
  have := is_deriveB (is_derive_cst (2 : R) z 1)
    (@is_deriveX _ _ (@id R) 2 z 1 1 (is_derive_id z 1)).
  have -> : (cst (2 : R) - (@id R) ^+ 2) = (fun y : R => 2 - y ^+ 2).
    by apply/funext => y.
  move=> h; apply: (is_derive_eq h).
  by rewrite /GRing.scale /= sub0r mulr1 expr1.
have dsq := @is_derive1_comp R Num.sqrt (fun y : R => 2 - y ^+ 2) z _ _
  (is_derive1_sqrt u0) du.
have dp : is_derive z 1 (fun y : R => 5 * y - y ^+ 3) (5 - 3 * z ^+ 2).
  have h1 := is_derive_id z (1 : R).
  have h3 : is_derive z 1 (@GRing.exp R ^~ 3) (3%:R *: z ^+ 2 *: 1).
    by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
  have h := is_deriveB (is_deriveZ 5 h1) h3.
  have -> : (fun y : R => 5 * y - y ^+ 3) = 5 \*: id - (@GRing.exp R ^~ 3).
    by apply/funext => y.
  apply: (is_derive_eq h).
  by rewrite /GRing.scale /= !mulr1.
have dA := is_deriveD (is_deriveZ (2 * pi)^-1 dasin)
  (is_deriveZ (12 * pi)^-1 (is_deriveM dp dsq)).
have -> : sc2_A = (2 * pi)^-1 \*: (asin \o (fun y : R => (Num.sqrt 2)^-1 * y))
    + (12 * pi)^-1 \*: ((fun y : R => 5 * y - y ^+ 3) *
                        (Num.sqrt \o (fun y : R => 2 - y ^+ 2))).
  by apply/funext => y.
apply: (is_derive_eq dA).
rewrite /GRing.scale /= tE -/s /sc2_phi -/s.
have sn : s != 0 by rewrite gt_eqF.
have key : (2 * pi)^-1 * ((s / Num.sqrt 2)^-1 * (Num.sqrt 2)^-1) +
    (12 * pi)^-1 * ((5 * z - z ^+ 3) * ((2 * s)^-1 * - (2 * z)) +
                    s * (5 - 3 * z ^+ 2)) =
    s ^+ 3 / (3 * pi) +
    (s ^+ 2 + z ^+ 2 - 2) * (z ^+ 2 - 4 * s ^+ 2 - 3) / (12 * pi * s).
  by move: (pi : R) pn => p pn; field.
rewrite key.
have -> : s ^+ 2 + z ^+ 2 - 2 = 0 by rewrite s2; ring.
by rewrite !mul0r addr0.
Qed.

End arcsine.

(* 3. Conjunct (c) of the curve statement, at Stdlib's R. *)

Local Notation RR := (R : realType).

Lemma condition_kappa_JE (w : R) : condition_kappa_J w = sc2_J w.
Proof.
have dE (x : R) : universality_semicircle_density x = sc2_dens x.
  by rewrite /universality_semicircle_density RdivE.
have c2 := continuous_upper_part w 2.
have c1 := continuous_upper_part w 1.
have i2 := sc2_dens_integrable _ c2.
have i1 := sc2_dens_integrable _ c1.
rewrite /condition_kappa_J.
have -> : universality_s w = \int[lebesgue_measure]_x
    (Num.max (x - w) 0 ^+ 2 * sc2_dens x).
  rewrite /universality_s /universality_semicircle_integral.
  by apply: eq_Rintegral => x _; rewrite dE /universality_positive_part RminusE.
have -> : universality_m w = \int[lebesgue_measure]_x
    (Num.max (x - w) 0 ^+ 1 * sc2_dens x).
  rewrite /universality_m /universality_semicircle_integral.
  apply: eq_Rintegral => x _.
  by rewrite dE /universality_positive_part RminusE expr1.
rewrite -(RintegralZl w measurableT i1).
have i1w : lebesgue_measure.-integrable setT
    (EFin \o (fun x : RR => w * (Num.max (x - w) 0 ^+ 1 * sc2_dens x))).
  have := integrableZl measurableT w i1.
  by apply: eq_integrable => // x _; rewrite /= EFinM.
rewrite -(RintegralD measurableT i2 i1w) /sc2_J.
apply: eq_Rintegral => x _.
have [h|h] := leP (x - w) 0; first by ring.
by rewrite expr1; ring.
Qed.

Theorem condition_kappa_integral_holds (kappa : R) : 1 < kappa ->
  condition_kappa_integral kappa.
Proof.
move=> k1 C C1.
have /andP[_ lu] := condition_kappa_ell_spec C kappa C1 k1.
rewrite /condition_kappa_alpha !condition_kappa_JE (sc2_J_integral _ _ lu).
set l := condition_kappa_ell C kappa; set u := condition_kappa_u C kappa.
have -> : [set z : R | l <= z <= u] = [set` `[l, u]].
  by apply/seteqP; split => z /=; rewrite in_itv.
rewrite -RintegralZl //; last first.
  by apply: eq_Rintegral => z _; rewrite /sc2_phi mulrC.
apply: continuous_compact_integrable; first exact: segment_compact.
by apply: continuous_subspaceT; exact: continuous_sqrt2_cube.
Qed.

(* The arcsine evaluation: alpha(C, kappa) = A(u) - A(ell). *)
Lemma condition_kappa_alpha_arcsine (C kappa : R) : 1 < C -> 1 < kappa ->
  condition_kappa_alpha C kappa =
  sc2_A (condition_kappa_u C kappa) - sc2_A (condition_kappa_ell C kappa).
Proof.
move=> C1 k1.
have [u0 us _ _] := condition_kappa_u_spec C kappa C1 k1.
have /andP[le lu] := condition_kappa_ell_spec C kappa C1 k1.
rewrite /condition_kappa_alpha !condition_kappa_JE (sc2_J_integral _ _ lu).
set l := condition_kappa_ell C kappa in le lu *.
set u := condition_kappa_u C kappa in u0 us lu *.
have inI (x : RR) : l <= x <= u -> - Num.sqrt 2%:R < x < Num.sqrt 2%:R.
  move=> /andP[a b]; apply/andP; split; first exact: lt_le_trans a.
  exact: le_lt_trans us.
have dA (x : RR) : l <= x <= u -> is_derive x 1 (@sc2_A RR) (sc2_phi x).
  by move=> xI; apply: sc2_A_derive; exact: inI.
have cA (x : RR) : l <= x <= u -> {for x, continuous (@sc2_A RR)}.
  move=> xI; apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (dA x xI)).
have cf : {within `[l, u], continuous (@sc2_phi RR)}.
  by apply: continuous_subspaceT; exact: continuous_sc2_phi.
have dF : derivable_oo_LRcontinuous (@sc2_A RR) l u.
  split.
  - move=> x; rewrite in_itv /= => /andP[a b].
    by apply: (@ex_derive _ _ _ _ _ _ _ (dA x _)); rewrite !ltW.
  - by apply: cvg_at_right_filter; apply: cA; rewrite lexx ltW.
  - by apply: cvg_at_left_filter; apply: cA; rewrite lexx ltW.
have F'f : {in `]l, u[, (@sc2_A RR)^`() =1 (@sc2_phi RR)}.
  move=> x; rewrite in_itv /= => /andP[a b].
  have xI : l <= x <= u by rewrite !ltW.
  by rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dA x xI)).
have ftc := continuous_FTC2 lu cf dF F'f.
by rewrite /Rintegral ftc /=.
Qed.
