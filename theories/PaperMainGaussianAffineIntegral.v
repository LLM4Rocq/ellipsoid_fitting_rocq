(* Positive affine change of variables for whole-line Lebesgue integrals.
   This specializes the MathComp-Analysis FTC substitution theorem. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype sequences ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun numfun derive ftc.
From mathcomp Require Import ring_tactic arithmetic_tactic.
Import Order.TTheory GRing.Theory Num.Theory numFieldNormedType.Exports.
Open Scope classical_set_scope.
Open Scope ring_scope.

Lemma paper_main_affine_derivable (R : realType) (m s x : R) :
  derivable (fun y : R => m + s * y) x 1.
Proof.
apply: derivableD; first exact: derivable_cst.
apply: derivableM; [exact: derivable_cst | exact: derivable_id].
Qed.

Lemma paper_main_affine_derive (R : realType) (m s : R) :
  (fun y : R => m + s * y)^`() = (fun _ => s).
Proof.
apply/funext => x.
have Hc : derivable (fun _ : R => m) x 1 by exact: derivable_cst.
have Hl : derivable (fun y : R => s * y) x 1.
  apply: derivableM; [exact: derivable_cst | exact: derivable_id].
rewrite derive1E (deriveD Hc Hl) derive_cst.
have Hi : derivable (id : R -> R) x 1 by exact: derivable_id.
rewrite (@deriveMl R R^o id s x 1 Hi).
by rewrite derive_id mulr1 add0r.
Qed.

Lemma paper_main_affine_pinfty (R : realType) (m s : R) :
  0 < s -> (fun x : R => m + s * x) @ +oo --> +oo.
Proof.
move=> Hs; apply/cvgryPgt => A.
apply: filterS (nbhs_pinfty_gt (num_real ((A - m) / s))) => x Hx.
have H := Hx; rewrite ltr_pdivrMr // in H.
nra.
Qed.

Lemma paper_main_affine_ninfty (R : realType) (m s : R) :
  0 < s -> (fun x : R => m + s * x) @ -oo --> -oo.
Proof.
move=> Hs; apply/cvgrNyPlt => A.
apply: filterS (nbhs_ninfty_lt (num_real ((A - m) / s))) => x Hx.
have H := Hx; rewrite ltr_pdivlMr // in H.
nra.
Qed.

Theorem paper_main_affine_integral_nonnegative (R : realType)
    (m s : R) (G : R^o -> R^o) :
  0 < s -> continuous G -> (forall x, 0 <= G x) ->
  (\int[lebesgue_measure]_x (G x)%:E)%E =
  (\int[lebesgue_measure]_x (G (m + s * x) * s)%:E)%E.
Proof.
move=> Hs cG G0.
have HF := @increasing_ge0_integration_by_substitutionT R
  (fun x : R => m + s * x) G.
rewrite paper_main_affine_derive in HF.
apply: HF.
- by move=> x y Hxy; rewrite ltrD2l ltr_pM2l.
- by move=> x; exact: cvg_cst.
- exact: is_cvg_cst.
- exact: is_cvg_cst.
- move=> x; exact: paper_main_affine_derivable.
- exact: paper_main_affine_ninfty.
- exact: paper_main_affine_pinfty.
- exact: cG.
- exact: G0.
Qed.

Lemma paper_main_real_integral_parts (R : realType) (G : R^o -> R^o) :
  (\int[lebesgue_measure]_x (G x)%:E)%E =
  ((\int[lebesgue_measure]_x (Num.max (G x) 0)%:E) -
   (\int[lebesgue_measure]_x (Num.max (- G x) 0)%:E))%E.
Proof.
rewrite [LHS]integralE; congr (_ - _)%E.
- apply: eq_integral => x _; by rewrite funeposE EFin_max.
- apply: eq_integral => x _; by rewrite funenegE EFin_max.
Qed.

Theorem paper_main_affine_integral (R : realType)
    (m s : R) (G : R^o -> R^o) :
  0 < s -> continuous G ->
  (\int[lebesgue_measure]_x (G x)%:E)%E =
  (\int[lebesgue_measure]_x (G (m + s * x) * s)%:E)%E.
Proof.
move=> Hs cG.
have cp : continuous (fun x : R^o => Num.max (G x) 0).
  by move=> x; apply: continuous_max; [exact: cG | exact: cvg_cst].
have cn : continuous (fun x : R^o => Num.max (- G x) 0).
  move=> x; apply: (@continuous_max R R^o (fun y : R => - G y) (fun _ => 0) x); last exact: cvg_cst.
  exact: cvgN (cG x).
have Gp0 : forall x, 0 <= Num.max (G x) 0.
  by move=> x; rewrite le_max lexx orbT.
have Gn0 : forall x, 0 <= Num.max (- G x) 0.
  by move=> x; rewrite le_max lexx orbT.
have Hp := paper_main_affine_integral_nonnegative R m s _ Hs cp Gp0.
have Hn := paper_main_affine_integral_nonnegative R m s _ Hs cn Gn0.
rewrite [LHS]paper_main_real_integral_parts [RHS]paper_main_real_integral_parts Hp Hn.
congr (_ - _)%E.
- apply: eq_integral => x _; by rewrite maxr_pMl ?(ltW Hs) ?mul0r.
- apply: eq_integral => x _; by rewrite maxr_pMl ?(ltW Hs) ?mul0r ?mulNr.
Qed.

Theorem paper_main_affine_integrable (R : realType)
    (m s : R) (G : R^o -> R^o) :
  0 < s -> continuous G ->
  lebesgue_measure.-integrable setT (EFin \o G) <->
  lebesgue_measure.-integrable setT
    (EFin \o (fun x : R => G (m + s * x) * s)).
Proof.
move=> Hs cG.
have cH : continuous (fun x : R^o => G (m + s * x) * s).
  move=> x; apply: cvgM; last exact: cvg_cst.
  apply: (cvg_comp _ G); last exact: cG.
  apply: cvgD; first exact: cvg_cst.
  apply: cvgM; [exact: cvg_cst | exact: cvg_id].
have cN : continuous (fun x : R^o => `|G x|).
  by move=> x; exact: cvg_norm (cG x).
have Hnorm := paper_main_affine_integral_nonnegative R m s _ Hs cN
  (fun x => normr_ge0 (G x)).
have HE : (\int[lebesgue_measure]_x `|(G x)%:E|)%E =
    (\int[lebesgue_measure]_x `|(G (m + s * x) * s)%:E|)%E.
  rewrite Hnorm; apply: eq_integral => x _.
  by rewrite /= normrM (ger0_norm (ltW Hs)).
split=> /integrableP[_ HB]; apply/integrableP; split.
- apply/measurable_EFinP; exact: continuous_measurable_fun cH.
- by rewrite -HE.
- apply/measurable_EFinP; exact: continuous_measurable_fun cG.
- by rewrite HE.
Qed.
