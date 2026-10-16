(* Moment bounds for the head-coordinate targets of sparse shifted fits.
   The component second moments are all one, so centered squares remain
   uncorrelated after mixing. Only the common subgaussian bound is used;
   no fourth-moment matching or symmetry is needed. The head weight stays
   positive for every shift, with no asserted condition-number bound. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.probability Require Import subgaussian lindeberg tuple_rows efron_stein.
From GaussianAnalysis.probability Require Import mixture countable_mixture isotropic_mixtures.
From GaussianAnalysis.random_matrix Require Import isotropic_rows.
From GaussianAnalysis.convex Require Import feature_moments.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component.
From EllipsoidUniversality.Sat Require Import AprioriSparse.
From EllipsoidUniversality.Shifted Require Import MixtureRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sparse_head_center h (z : 'rV[RR]_h) := frobenius z ^+2-h%:R.
Definition sparse_head_scale h (m : 'rV[RR]_h) := (1+frobenius m)^-1.
Definition sparse_head_target h (s : R) (m z : 'rV[RR]_h) :=
  s*(sparse_head_center z+2*mxdot z m).
Definition sparse_head_normalized_target h p (m z : 'rV[RR]_h) :=
  sparse_head_target (sparse_head_scale m) m z / Num.sqrt p%:R.

Lemma sparse_head_scale_bounds h (m : 'rV[RR]_h) :
  [ /\ 0 < sparse_head_scale m, sparse_head_scale m <= 1 &
    sparse_head_scale m*frobenius m <= 1].
Proof.
have m0 := frobenius_ge0 m.
have a0 : 0 < 1+frobenius m by lra.
rewrite /sparse_head_scale; split.
- by rewrite invr_gt0.
- by rewrite invf_le1 //; lra.
- by rewrite mulrC ler_pdivrMr // mul1r; lra.
Qed.

Lemma sparse_head_target_expansion h (s : R) (m z : 'rV[RR]_h) :
  sparse_head_target s m z = s*(frobenius (z+m)^+2-h%:R-frobenius m^+2).
Proof.
rewrite /sparse_head_target /sparse_head_center !frobenius_sqr.
by rewrite mxdotDl !mxdotDr (mxdotC m z); ring.
Qed.

Lemma measurable_sparse_head_center h :
  measurable_fun [set: 'rV[RR]_h] (@sparse_head_center h).
Proof.
apply: (eq_measurable_fun (fun z : 'rV[RR]_h => mxdot z z-h%:R)).
  by move=>z _; rewrite /sparse_head_center frobenius_sqr.
apply: measurable_funB; last exact: measurable_cst.
exact: measurable_norm2.
Qed.

Lemma measurable_sparse_head_target h s (m : 'rV[RR]_h) :
  measurable_fun setT (fun z => sparse_head_target s m z : RR).
Proof.
apply: measurable_funM; first exact: measurable_cst.
apply: measurable_funD; first exact: measurable_sparse_head_center.
apply: measurable_funM; first exact: measurable_cst.
exact: measurable_mxdotl.
Qed.

Lemma measurable_sparse_head_normalized_target h p (m : 'rV[RR]_h) :
  measurable_fun setT (fun z => sparse_head_normalized_target p m z : RR).
Proof.
apply: measurable_funM; last exact: measurable_cst.
exact: measurable_sparse_head_target.
Qed.

Lemma sparse_head_center_tuple h (z : h.-tuple (measurableTypeR R)) :
  sparse_head_center (row_of_tuple h z) = \sum_(j<h) ((tnth z j)^+2-1).
Proof.
rewrite /sparse_head_center frobenius_sqr /mxdot big_ord1 sumrB.
under eq_bigr do rewrite row_of_tupleE -expr2.
by rewrite sumr_const card_ord -mulr_natr mul1r.
Qed.

Section coordinate_square.
Variables (K : R) (mu : probability (measurableTypeR R) R).
Hypothesis hmu : mixture_component_law K mu.

Lemma sparse_coordinate_center_integrable :
  mu.-integrable setT (fun x : measurableTypeR R => ((x:RR)^+2-1)%:E).
Proof.
apply: integrableRB; first exact: (@component_law_integrable K mu hmu 2).
exact: integrable_cst_prob.
Qed.

Lemma sparse_coordinate_center_mean : \int[mu]_x ((x:RR)^+2-1) = 0.
Proof.
rewrite (RintegralB measurableT (@component_law_integrable K mu hmu 2)
  (integrable_cst_prob mu 1)) Rintegral_cst_prob.
by rewrite /Rintegral (@component_law_second K mu hmu) /= subrr.
Qed.

Lemma sparse_coordinate_square_integrable :
  mu.-integrable setT (fun x : measurableTypeR R => (((x:RR)^+2-1)^+2)%:E).
Proof.
have i2 := @component_law_integrable K mu hmu 2.
have i4 := @component_law_integrable K mu hmu 4.
have ib := integrableRB i4 (integrableRZl 2 i2).
have ii := integrableRD ib (integrable_cst_prob mu 1).
apply: eq_integrable ii => // x _ /=; congr EFin; ring.
Qed.

Lemma sparse_coordinate_square_bound :
  \int[mu]_x ((x:RR)^+2-1)^+2 <= 4*K^+4.
Proof.
have i2 := @component_law_integrable K mu hmu 2.
have i4 := @component_law_integrable K mu hmu 4.
have poly (x:RR) : (x^+2-1)^+2 = x^+4-2*x^+2+1 by ring.
under eq_Rintegral do rewrite poly.
rewrite (RintegralD measurableT (integrableRB i4 (integrableRZl 2 i2))
  (integrable_cst_prob mu 1)) Rintegral_cst_prob.
rewrite (RintegralB measurableT i4 (integrableRZl 2 i2))
  (RintegralZl 2 measurableT i2).
have e2 : \int[mu]_x (x:RR)^+2 = 1.
  by rewrite /Rintegral (@component_law_second K mu hmu).
have e4 : \int[mu]_x (x:RR)^+4 <= 4*K^+4.
  rewrite -lee_fin (Rintegral_EFin i4).
  exact: (@component_law_fourth_le K mu hmu).
rewrite e2; lra.
Qed.
End coordinate_square.

Section component_head.
Variables (K : R) (h : nat) (nu : nat -> probability (measurableTypeR R) R).
Hypothesis hnu : forall j, (j<h)%N -> mixture_component_law K (nu j).
Let P := point_law h nu.

Lemma sparse_component_center_second :
  P.-integrable setT (fun z => (sparse_head_center z ^+2)%:E) /\
  \int[P]_z sparse_head_center z ^+2 <= 4*K^+4*h%:R.
Proof.
have [iS eS] := @independent_centered_sum_second_moment RR _ _ h nu
  (fun _ x => (x:RR)^+2-1)
  (fun j => sparse_coordinate_center_integrable (@hnu j (ltn_ord j)))
  (fun j => sparse_coordinate_square_integrable (@hnu j (ltn_ord j)))
  (fun j => sparse_coordinate_center_mean (@hnu j (ltn_ord j))).
have mQ : measurable_fun setT (fun z : 'rV[RR]_h => (sparse_head_center z ^+2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_head_center.
have law : (\int[P]_z (sparse_head_center z^+2)%:E =
    \int[tuple_prod nu h]_t ((\sum_j ((tnth t j)^+2-1))^+2)%:E)%E.
  rewrite /P /point_law integral_distribution_measurable //.
  by apply: eq_integral =>t _; rewrite sparse_head_center_tuple.
split.
- apply/integrableP; split=> //.
  under eq_integral do rewrite abse_EFin (ger0_norm (sqr_ge0 _)).
  rewrite law; have /integrableP[_ fi] := iS.
  move: fi; by under eq_integral do rewrite abse_EFin (ger0_norm (sqr_ge0 _)).
- rewrite /Rintegral law.
  change (\int[tuple_prod nu h]_t (\sum_(j<h) ((tnth t j : RR)^+2-1))^+2 <= 4*K^+4*h%:R).
  rewrite eS.
  apply: le_trans (_ : \sum_(j<h) (4*K^+4) <= _).
  + apply: ler_sum=>j _; exact: sparse_coordinate_square_bound (@hnu j (ltn_ord j)).
  + rewrite sumr_const card_ord -mulr_natr; nra.
Qed.

Lemma sparse_point_integrable (f : 'rV[RR]_h -> RR) :
  measurable_fun setT f ->
  (tuple_prod nu h).-integrable setT (fun t => (f (row_of_tuple h t))%:E) ->
  P.-integrable setT (fun z => (f z)%:E).
Proof.
move=> mf /integrableP[mft ft]; apply/integrableP; split.
- exact/measurable_EFinP.
- rewrite /P /point_law integral_distribution_measurable //.
  apply: measurableT_comp; first exact: abse_measurable.
  exact/measurable_EFinP.
Qed.

Lemma sparse_component_linear_second (m : 'rV[RR]_h) :
  P.-integrable setT (fun z => (mxdot z m ^+2)%:E) /\
  \int[P]_z mxdot z m ^+2 = frobenius m^+2.
Proof.
have ix j (jh : (j<h)%N) : (nu j).-integrable setT (fun x => (x:RR)%:E).
  have ii := @component_law_integrable K (nu j) (@hnu j jh) 1.
  by apply: eq_integrable ii=> // x _; rewrite expr1.
have fi (j : 'I_h) : (nu j).-integrable setT (fun x => (m 0 j*(x:RR))%:E).
  have ii := integrableZl measurableT (m 0 j) (ix j (ltn_ord j)).
  by apply: eq_integrable ii=> // x _; rewrite EFinM.
have f2i (j : 'I_h) : (nu j).-integrable setT (fun x => ((m 0 j*(x:RR))^+2)%:E).
  have ii := integrableRZl (m 0 j ^+2)
    (@component_law_integrable K (nu j) (@hnu j (ltn_ord j)) 2).
  by apply: eq_integrable ii => // x _ /=; rewrite exprMn.
have fc (j : 'I_h) : \int[nu j]_x (m 0 j*(x:RR)) = 0.
  rewrite (RintegralZl _ measurableT (ix j (ltn_ord j))).
  by rewrite /Rintegral (@component_law_mean K (nu j) (@hnu j (ltn_ord j))) mulr0.
have [iS _] := independent_centered_sum_second_moment fi f2i fc.
split.
- apply: sparse_point_integrable.
  + apply: measurable_funX; exact: measurable_mxdotl.
  + apply: eq_integrable iS=> // t _ /=.
    by rewrite mxdot_row_of_tuple.
- exact: (@component_row_second K h nu hnu m).
Qed.

Lemma sparse_target_square_domination (s : R) (m z : 'rV[RR]_h) :
  sparse_head_target s m z ^+2 <=
    2*s^+2*sparse_head_center z^+2+8*s^+2*mxdot z m ^+2.
Proof.
rewrite /sparse_head_target exprMn.
have hz : (sparse_head_center z+2*mxdot z m)^+2 <=
    2*sparse_head_center z^+2+8*mxdot z m^+2.
  have := sqr_ge0 (sparse_head_center z-2*mxdot z m); nra.
have hh := ler_wpM2l (sqr_ge0 s) hz; nra.
Qed.

Theorem sparse_component_target_second (s : R) (m : 'rV[RR]_h) :
  P.-integrable setT (fun z => (sparse_head_target s m z^+2)%:E) /\
  \int[P]_z sparse_head_target s m z^+2 <=
    8*s^+2*K^+4*h%:R+8*s^+2*frobenius m^+2.
Proof.
have [iQ bQ] := sparse_component_center_second.
have [iL eL] := sparse_component_linear_second m.
have iB := integrableRD (integrableRZl (2*s^+2) iQ) (integrableRZl (8*s^+2) iL).
have iT : P.-integrable setT (fun z => (sparse_head_target s m z^+2)%:E).
  apply: (le_integrable measurableT _ _ iB).
  - apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_head_target.
  - move=> z _.
    rewrite /= ?abse_EFin ?lee_fin (ger0_norm (sqr_ge0 _)).
    exact: le_trans (sparse_target_square_domination s m z) (ler_norm _).
split=> //.
have hB := le_Rintegral measurableT iT iB
  (fun z _ => sparse_target_square_domination s m z).
rewrite (RintegralD measurableT (integrableRZl (2*s^+2) iQ)
  (integrableRZl (8*s^+2) iL)) !RintegralZl // eL in hB.
have bQ' := ler_wpM2l (mulr_ge0 (ler0n RR 2) (sqr_ge0 s)) bQ.
have ee : 2*s^+2*(4*K^+4*h%:R) = 8*s^+2*K^+4*h%:R by ring.
apply: le_trans hB _.
rewrite -ee; exact: lerD bQ' (lexx _).
Qed.

End component_head.

Lemma sparse_squared_integrable_of_bound h (P : probability 'rV[RR]_h RR)
    (f : 'rV[RR]_h -> RR) (B : R) :
  measurable_fun setT f -> (\int[P]_z (f z ^+2)%:E <= B%:E)%E ->
  P.-integrable setT (fun z => (f z ^+2)%:E).
Proof.
move=> mf hb; apply/integrableP; split.
- apply/measurable_EFinP; exact: measurable_funX.
- under eq_integral do rewrite abse_EFin (ger0_norm (sqr_ge0 _)).
  exact: le_lt_trans hb (ltry B).
Qed.

Section finite_head.
Context {I : finType}.
Variables (K : R) (h : nat) (w : I -> R).
Variable nu : I -> nat -> probability (measurableTypeR R) R.
Variable hw : mixture_weights w.
Hypothesis hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j).
Let P := mixture (fun i => point_law h (nu i)) hw.

Theorem sparse_finite_target_second (s : R) (m : 'rV[RR]_h) :
  (\int[P]_z (sparse_head_target s m z^+2)%:E <=
    (8*s^+2*K^+4*h%:R+8*s^+2*frobenius m^+2)%:E)%E.
Proof.
have mf : measurable_fun setT (fun z : 'rV[RR]_h => (sparse_head_target s m z^+2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_head_target.
rewrite /P ge0_integral_mixture //; first by move=>z _; rewrite lee_fin sqr_ge0.
apply: (le_trans (y := (\sum_i (w i)%:E*
  (8*s^+2*K^+4*h%:R+8*s^+2*frobenius m^+2)%:E)%E)).
- apply: lee_sum=>i _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: hw.1.
  have [ii hi] := @sparse_component_target_second K h (nu i) (hnu i) s m.
  by rewrite -(@Rintegral_EFin _ _ RR _ _ ii) lee_fin.
- under eq_bigr do rewrite -EFinM.
  by rewrite sumEFin -mulr_suml hw.2 mul1r.
Qed.

Corollary sparse_finite_target_integrable (s : R) (m : 'rV[RR]_h) :
  P.-integrable setT (fun z => (sparse_head_target s m z^+2)%:E).
Proof.
apply: sparse_squared_integrable_of_bound (sparse_finite_target_second s m).
exact: measurable_sparse_head_target.
Qed.
End finite_head.

Section countable_head.
Variables (K : R) (h : nat) (w : nat -> R).
Variable nu : nat -> nat -> probability (measurableTypeR R) R.
Variable hw : cmixture_weights w.
Hypothesis hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j).
Let P := cmixture (fun i => point_law h (nu i)) hw.

Theorem sparse_countable_target_second (s : R) (m : 'rV[RR]_h) :
  (\int[P]_z (sparse_head_target s m z^+2)%:E <=
    (8*s^+2*K^+4*h%:R+8*s^+2*frobenius m^+2)%:E)%E.
Proof.
have mf : measurable_fun setT (fun z : 'rV[RR]_h => (sparse_head_target s m z^+2)%:E).
  apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_head_target.
rewrite /P ge0_integral_cmixture //; first by move=>z _; rewrite lee_fin sqr_ge0.
apply: (le_trans (y := (\sum_(i<oo) (w i)%:E*
  (8*s^+2*K^+4*h%:R+8*s^+2*frobenius m^+2)%:E)%E)).
- apply: lee_nneseries=>i _.
  + move=> _; apply: mule_ge0; first by rewrite lee_fin; exact: hw.1.
    by apply: integral_ge0=>z _; rewrite lee_fin sqr_ge0.
  + apply: lee_wpmul2l; first by rewrite lee_fin; exact: hw.1.
    have [ii hi] := @sparse_component_target_second K h (nu i) (hnu i) s m.
    by rewrite -(@Rintegral_EFin _ _ RR _ _ ii) lee_fin.
- by rewrite cmixture_weighted_const.
Qed.

Corollary sparse_countable_target_integrable (s : R) (m : 'rV[RR]_h) :
  P.-integrable setT (fun z => (sparse_head_target s m z^+2)%:E).
Proof.
apply: sparse_squared_integrable_of_bound (sparse_countable_target_second s m).
exact: measurable_sparse_head_target.
Qed.
End countable_head.

Lemma sparse_head_scale_second_bound K h (m : 'rV[RR]_h) :
  8*(sparse_head_scale m)^+2*K^+4*h%:R+
    8*(sparse_head_scale m)^+2*frobenius m^+2 <= 8*K^+4*h%:R+8.
Proof.
have [s0 s1 sm1] := sparse_head_scale_bounds m.
have s2 : sparse_head_scale m^+2 <= 1.
  have := ler_pM (ltW s0) (ltW s0) s1 s1; nra.
have sm0 : 0 <= sparse_head_scale m*frobenius m
  by exact: mulr_ge0 (ltW s0) (frobenius_ge0 m).
have sm2 : (sparse_head_scale m*frobenius m)^+2 <= 1.
  have := ler_pM sm0 sm0 sm1 sm1; nra.
have kh0 : 0 <= K^+4*h%:R by apply: mulr_ge0; [by rewrite exprn_even_ge0|exact: ler0n].
have h1 := ler_wpM2r kh0 s2.
rewrite exprMn in sm2.
nra.
Qed.

Lemma sparse_normalized_square h p (m z : 'rV[RR]_h) :
  sparse_head_normalized_target p m z^+2 =
    p%:R^-1*sparse_head_target (sparse_head_scale m) m z^+2.
Proof.
by rewrite /sparse_head_normalized_target exprMn exprVn sqr_sqrtr ?ler0n // mulrC.
Qed.

Lemma sparse_normalized_second_of_bound K h p
    (P : probability 'rV[RR]_h RR) (m : 'rV[RR]_h) :
  (\int[P]_z (sparse_head_target (sparse_head_scale m) m z^+2)%:E <=
    (8*(sparse_head_scale m)^+2*K^+4*h%:R+
     8*(sparse_head_scale m)^+2*frobenius m^+2)%:E)%E ->
  P.-integrable setT (fun z => (sparse_head_normalized_target p m z^+2)%:E) /\
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <=
     ((8*K^+4*h%:R+8)/p%:R)%:E)%E.
Proof.
move=> hb.
have it := sparse_squared_integrable_of_bound
  (measurable_sparse_head_target (sparse_head_scale m) m) hb.
have iz := integrableRZl p%:R^-1 it.
have inn : P.-integrable setT
    (fun z => (sparse_head_normalized_target p m z^+2)%:E).
  apply: eq_integrable iz=>// z _; by rewrite sparse_normalized_square.
split=>//.
have ht : (\int[P]_z (sparse_head_target (sparse_head_scale m) m z^+2)%:E
    <= (8*K^+4*h%:R+8)%:E)%E.
  apply: le_trans hb _; rewrite lee_fin; exact: sparse_head_scale_second_bound.
have pi0 : (0 <= (p%:R^-1 : RR)%:E)%E by rewrite lee_fin invr_ge0 ler0n.
have hmul := lee_wpmul2l pi0 ht.
under eq_integral do rewrite sparse_normalized_square EFinM.
rewrite integralZl //.
move: hmul; by rewrite -EFinM mulrC.
Qed.

Corollary sparse_finite_normalized_second {I : finType} K h p
    (w : I -> R) (nu : I -> nat -> probability (measurableTypeR R) R)
    (hw : mixture_weights w)
    (hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j))
    (m : 'rV[RR]_h) :
  let P := mixture (fun i => point_law h (nu i)) hw in
  P.-integrable setT (fun z => (sparse_head_normalized_target p m z^+2)%:E) /\
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <=
     ((8*K^+4*h%:R+8)/p%:R)%:E)%E.
Proof.
apply: sparse_normalized_second_of_bound.
exact: sparse_finite_target_second.
Qed.

Corollary sparse_countable_normalized_second K h p
    (w : nat -> R) (nu : nat -> nat -> probability (measurableTypeR R) R)
    (hw : cmixture_weights w)
    (hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j))
    (m : 'rV[RR]_h) :
  let P := cmixture (fun i => point_law h (nu i)) hw in
  P.-integrable setT (fun z => (sparse_head_normalized_target p m z^+2)%:E) /\
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <=
     ((8*K^+4*h%:R+8)/p%:R)%:E)%E.
Proof.
apply: sparse_normalized_second_of_bound.
exact: sparse_countable_target_second.
Qed.

Example sparse_empty_head p (m z : 'rV[RR]_0) :
  sparse_head_normalized_target p m z = 0.
Proof.
have mz : m = 0 by apply/matrixP=>i j; move: (ltn_ord j); rewrite ltn0.
have zz : z = 0 by apply/matrixP=>i j; move: (ltn_ord j); rewrite ltn0.
rewrite mz zz /sparse_head_normalized_target /sparse_head_target
  /sparse_head_center frobenius0 mxdot0l expr0n /= subr0 !mulr0 add0r.
by rewrite mulr0 mul0r.
Qed.
