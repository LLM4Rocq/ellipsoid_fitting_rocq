(* Uniform bounds for sparse-shift interpolation targets. Independence of
   coordinates is used only within mixture components. A common head weight
   controls every deterministic shift; the resulting row tails are averaged
   before any union bound over observations. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences realfun exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.analysis Require Import family_reindexing.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.random_matrix Require Import goe_entries.
From GaussianAnalysis.probability Require Import subgaussian hanson_wright lindeberg tuple_rows efron_stein.
From GaussianAnalysis.probability Require Import symmetrization small_ball_method.
From GaussianAnalysis.probability Require Import mixture countable_mixture isotropic_mixtures independent_row_signs.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Mixture Require Import Component.
From EllipsoidUniversality.Sat Require Import AprioriSparse.
From EllipsoidUniversality.Features Require Import Regular.
From EllipsoidUniversality.Shifted Require Import MixtureRows SparseTargets GaussianTargets SparseDimensions SparseTargetRates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sparse_center_tail_scale (K : R) h :=
  252*K^+2*(Num.sqrt h%:R+1).
Definition sparse_target_tail_scale (K : R) h :=
  sparse_center_tail_scale K h+8*K.

Lemma sparse_center_tail_scale_gt0 K h : 0<K -> 0<sparse_center_tail_scale K h.
Proof.
by move=> K0; rewrite /sparse_center_tail_scale !mulr_gt0 ?exprn_gt0 //.
Qed.

Section component.
Variables (K : R) (h : nat) (nu : nat -> probability (measurableTypeR R) R).
Hypothesis K0 : 0<K.
Hypothesis hnu : forall j, (j<h)%N -> mixture_component_law K (nu j).
Let P := point_law h nu.

Lemma sparse_component_center_subexponential :
  subexponential P (@sparse_head_center h) (sparse_center_tail_scale K h).
Proof.
have sg j (jh : (j<h)%N) :
    subgaussian (nu j) (fun x : measurableTypeR R => (x:RR)) K.
  exact (@component_law_subgaussian K (nu j) (hnu jh)).
have me j (jh : (j<h)%N) : \int[nu j]_x (x:RR)=0.
  by rewrite /Rintegral (@component_law_mean K (nu j) (hnu jh)).
have fI : frobenius (1%:M : 'M[RR]_h) = Num.sqrt h%:R.
  by rewrite /frobenius mxdot_trace trmx1 mulmx1 mxtrace1.
have bd : 252*K^+2*frobenius (1%:M : 'M[RR]_h) <= sparse_center_tail_scale K h.
  rewrite fI /sparse_center_tail_scale.
  have := sqr_ge0 K; nra.
have hw := @hanson_wright_subexponential _ _ RR nu h
  (fun=>fun x : measurableTypeR R => (x:RR)) K sg me
  (1%:M : 'M[RR]_h) (sparse_center_tail_scale K h)
  (sparse_center_tail_scale_gt0 h K0) bd.
have hc : hw_center nu (fun=>fun x : measurableTypeR R => (x:RR))
    (1%:M : 'M[RR]_h) = h%:R.
  rewrite /hw_center.
  under eq_bigr do rewrite mxE eqxx /= /hw_sqmean /Rintegral
    (@component_law_second K (nu _) (hnu (ltn_ord _))) /= mul1r.
  by rewrite sumr_const card_ord -mulr_natr mul1r.
have hq t : hw_quad (fun=>fun x : measurableTypeR R => (x:RR))
    (1%:M : 'M[RR]_h) t = frobenius (row_of_tuple h t)^+2.
  rewrite /hw_quad frobenius_sqr /mxdot big_ord1.
  apply: eq_bigr=>i _; rewrite (bigD1 i) //= mxE eqxx /= mul1r.
  rewrite big1 ?addr0; first by move=>j ji; rewrite mxE eq_sym (negbTE ji) mul0r.
  by rewrite row_of_tupleE.
rewrite /P /point_law; apply/subexponential_distribution.
  exact: measurable_sparse_head_center.
have ee : (@sparse_head_center h) \o row_of_tuple h =
  (fun t=>hw_quad (fun=>fun x : measurableTypeR R => (x:RR))
    (1%:M : 'M[RR]_h) t -
    hw_center nu (fun=>fun x : measurableTypeR R => (x:RR)) (1%:M : 'M[RR]_h)).
  by apply/boolp.funext=>t; rewrite /= /sparse_head_center hq hc.
by rewrite ee.
Qed.

End component.

Lemma sparse_head_target_abs_bound h (m z : 'rV[RR]_h) :
  `|sparse_head_target (sparse_head_scale m) m z| <=
    `|sparse_head_center z|+2 * `|mxdot z (sparse_head_scale m *: m)|.
Proof.
have [s0 s1 _] := sparse_head_scale_bounds m.
have ee : sparse_head_target (sparse_head_scale m) m z =
  sparse_head_scale m*sparse_head_center z+
  2*mxdot z (sparse_head_scale m *: m).
  rewrite /sparse_head_target mxdotZr; ring.
rewrite ee; apply: le_trans (ler_normD _ _) _.
rewrite !normrM (ger0_norm (ltW s0)) (ger0_norm (ler0n RR 2)).
apply: lerD; last exact: lexx.
have hh := ler_wpM2r (normr_ge0 (sparse_head_center z)) s1.
by rewrite mul1r in hh.
Qed.

Lemma sparse_target_tail_contradiction (a b x y v u : R) :
  x<a*u -> y<4*b*u -> v<=x+2*y -> (a+8*b)*u<=v -> False.
Proof. move=> h1 h2 h3 h4; nra. Qed.

Lemma sparse_target_tail_of_inputs K h (P : probability 'rV[RR]_h RR)
    (m : 'rV[RR]_h) (u : R) :
  0<K -> 1<=u ->
  subexponential P (@sparse_head_center h) (sparse_center_tail_scale K h) ->
  subgaussian P (fun z=>mxdot z (sparse_head_scale m *: m)) (4*K) ->
  (P [set z | (sparse_target_tail_scale K h*u <=
      `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E.
Proof.
move=> K0 u1 sh sl.
pose A := [set z : 'rV[RR]_h | sparse_center_tail_scale K h*u <= `|sparse_head_center z|].
pose B := [set z : 'rV[RR]_h | 4*K*u <= `|mxdot z (sparse_head_scale m *: m)|].
have mA : measurable A.
  rewrite /A -[X in measurable X]setTI; apply: measurable_fun_ler => //; exact: measurableT_comp (@measurable_sparse_head_center h).
have ml : measurable_fun setT (fun z : 'rV[RR]_h => mxdot z (sparse_head_scale m *: m) : RR).
  exact: measurable_mxdotl.
have mB : measurable B.
  rewrite /B -[X in measurable X]setTI; apply: measurable_fun_ler => //.
  exact: measurableT_comp ml.
have mT : measurable [set z | (sparse_target_tail_scale K h*u <=
      `|sparse_head_target (sparse_head_scale m) m z|)%R].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler => //.
  exact: measurableT_comp (measurable_sparse_head_target (sparse_head_scale m) m).
have sub : [set z | (sparse_target_tail_scale K h*u <=
      `|sparse_head_target (sparse_head_scale m) m z|)%R] `<=` A `|` B.
  move=>z /= hz.
  have [ha|ha] := leP (sparse_center_tail_scale K h*u) `|sparse_head_center z|.
    by left.
  have [hb|hb] := leP (4*K*u) `|mxdot z (sparse_head_scale m *: m)|.
    by right.
  exfalso; have hh := sparse_head_target_abs_bound m z.
  rewrite /sparse_target_tail_scale in hz.
  exact: sparse_target_tail_contradiction ha hb hh hz.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  exact: measurableU.
apply: le_trans (measureU2 P mA mB) _.
have ta := subexponential_tail (sparse_center_tail_scale K h*u) sh.
have u0 : 0<=u by lra.
have b0 : 0<=4*K*u by rewrite !mulr_ge0 ?(ltW K0).
have tb := subgaussian_tail sl b0.
have sc0 := sparse_center_tail_scale_gt0 h K0.
have sce : sparse_center_tail_scale K h*u/sparse_center_tail_scale K h=u.
  by rewrite mulrAC divff ?gt_eqF // mul1r.
have k40 : 0<4*K by rewrite mulr_gt0.
have k4 : 4*K !=0 by rewrite gt_eqF.
have leexp : expR(-((4*K*u)^+2/(4*K)^+2)) <= expR(-u).
  rewrite exprMn mulrAC divff ?expf_neq0 // mul1r ler_expR.
  nra.
rewrite sce in ta.
have tb' : (P B <= (2*expR(-u))%:E)%E.
  apply: le_trans tb _; by rewrite lee_fin ler_pM2l //.
have hab := leeD ta tb'.
move: hab; rewrite -EFinD.
have ee : 2*expR(-u)+2*expR(-u)=4*expR(-u) by ring.
by rewrite ee.
Qed.

Theorem sparse_component_target_tail K h
    (nu : nat -> probability (measurableTypeR R) R)
    (hnu : forall j, (j<h)%N -> mixture_component_law K (nu j))
    (m : 'rV[RR]_h) (u : R) :
  0<K -> 1<=u ->
  (point_law h nu [set z | (sparse_target_tail_scale K h*u <=
      `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E.
Proof.
move=> K0 u1; apply: sparse_target_tail_of_inputs =>//.
- exact: sparse_component_center_subexponential.
- apply: component_row_subgaussian =>//.
  have [s0 _ sm1] := sparse_head_scale_bounds m.
  by rewrite frobeniusZ (ger0_norm (ltW s0)).
Qed.

Theorem sparse_finite_target_tail {I : finType} K h
    (w : I -> R) (nu : I -> nat -> probability (measurableTypeR R) R)
    (hw : mixture_weights w)
    (hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j))
    (m : 'rV[RR]_h) (u : R) :
  0<K -> 1<=u ->
  (mixture (fun i=>point_law h (nu i)) hw
     [set z | (sparse_target_tail_scale K h*u <=
       `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E.
Proof.
move=> K0 u1; rewrite /mixture.
apply: (le_trans (y := (\sum_i (w i)%:E*(4*expR(-u))%:E)%E)).
- apply: lee_sum=>i _; apply: lee_wpmul2l; first by rewrite lee_fin; exact: hw.1.
  exact: (@sparse_component_target_tail K h (nu i) (hnu i) m u K0 u1).
- under eq_bigr do rewrite -EFinM.
  by rewrite sumEFin -mulr_suml hw.2 mul1r.
Qed.

Theorem sparse_countable_target_tail K h
    (w : nat -> R) (nu : nat -> nat -> probability (measurableTypeR R) R)
    (hw : cmixture_weights w)
    (hnu : forall i j, (j<h)%N -> mixture_component_law K (nu i j))
    (m : 'rV[RR]_h) (u : R) :
  0<K -> 1<=u ->
  (cmixture (fun i=>point_law h (nu i)) hw
     [set z | (sparse_target_tail_scale K h*u <=
       `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E.
Proof.
move=> K0 u1; rewrite cmixtureE.
apply: (le_trans (y := (\sum_(i<oo) (w i)%:E*(4*expR(-u))%:E)%E)).
- apply: lee_nneseries=>[i _ _|i _].
  + by rewrite mule_ge0 ?lee_fin ?hw.1 // measure_ge0.
  + apply: lee_wpmul2l; first by rewrite lee_fin; exact: hw.1.
    exact: (@sparse_component_target_tail K h (nu i) (hnu i) m u K0 u1).
- by rewrite cmixture_weighted_const.
Qed.

Lemma measurable_sparse_matrix_row n h (i : 'I_n) :
  measurable_fun [set: 'M[RR]_(n,h)] (fun H=>row i H).
Proof.
apply/measurable_fun_mxP=>j l; under eq_fun do rewrite mxE.
exact: measurable_mxentry.
Qed.

Lemma sparse_row_tuple_matrix n h (x : n.-tuple 'rV[RR]_h) (i : 'I_n) :
  row i (restricted_isometry.tuple_mx x) = tnth x i.
Proof. by apply/rowP=>j; rewrite !mxE. Qed.

Lemma sparse_iid_row_integral n h (P : probability 'rV[RR]_h RR)
    (i : 'I_n) (f : 'rV[RR]_h -> \bar RR) :
  measurable_fun setT f ->
  (\int[independent_row_matrix_law (fun=>P) n]_H f(row i H) = \int[P]_z f z)%E.
Proof.
move=> mf; rewrite /independent_row_matrix_law integral_distribution_measurable.
- exact: measurableT_comp mf (measurable_sparse_matrix_row i).
- under eq_integral do rewrite sparse_row_tuple_matrix.
  exact: integral_tuple_prod_coord.
Qed.

Lemma sparse_iid_row_probability n h (P : probability 'rV[RR]_h RR)
    (i : 'I_n) (A : set 'rV[RR]_h) : measurable A ->
  independent_row_matrix_law (fun=>P) n [set H | A(row i H)] = P A.
Proof.
move=> mA.
have mpre : measurable [set H : 'M[RR]_(n,h) | A(row i H)].
  rewrite -[X in measurable X]setTI; exact: measurable_sparse_matrix_row.
transitivity (\int[independent_row_matrix_law (fun=>P) n]_H (\1_A (row i H))%:E)%E.
- transitivity (\int[independent_row_matrix_law (fun=>P) n]_H
    (\1_[set H : 'M[RR]_(n,h) | A(row i H)] H)%:E)%E.
  + by rewrite integral_indic // setIT.
  + by apply: eq_integral=>H _; rewrite !indicE.
- rewrite (@sparse_iid_row_integral n h P i (fun z=>(\1_A z)%:E)); first
    by apply/measurable_EFinP; exact: measurable_indic.
  by rewrite integral_indic // setIT.
Qed.

Definition sparse_matrix_target n h p (m : 'rV[RR]_h) (H : 'M[RR]_(n,h)) (i : 'I_n) :=
  sparse_head_normalized_target p m (row i H).

Lemma measurable_sparse_matrix_target n h p (m : 'rV[RR]_h) (i : 'I_n) :
  measurable_fun [set: 'M[RR]_(n,h)] (fun H=>sparse_matrix_target p m H i : RR).
Proof.
exact: measurableT_comp (measurable_sparse_head_normalized_target p m)
  (measurable_sparse_matrix_row i).
Qed.

Lemma measurable_sparse_matrix_size n h p (m : 'rV[RR]_h) (L : R) :
  measurable_fun [set: 'M[RR]_(n,h)]
    (fun H=>shifted_interpolation_size p L (sparse_matrix_target p m H) : RR).
Proof.
rewrite /shifted_interpolation_size.
apply: measurable_funM; first exact: measurable_cst.
apply: measurable_funD.
- apply: measurable_funM; last exact: measurable_cst.
  have ms : measurable_fun [set: 'M[RR]_(n,h)]
      (fun H=>\sum_(i<n) sparse_matrix_target p m H i^+2 : RR).
    apply: measurable_sum=>i; apply: measurable_funX; exact: measurable_sparse_matrix_target.
  exact: measurableT_comp (continuous_measurable_fun (@sqrt_continuous RR)) ms.
- apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_max_norm=>i; exact: measurable_sparse_matrix_target.
Qed.

Lemma sparse_iid_target_square_sum n h p (P : probability 'rV[RR]_h RR)
    (m : 'rV[RR]_h) (B : R) :
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <= B%:E)%E ->
  (\int[independent_row_matrix_law (fun=>P) n]_H
       (\sum_(i<n) sparse_matrix_target p m H i^+2)%:E <= (n%:R*B)%:E)%E.
Proof.
move=> hb; under eq_integral do rewrite -sumEFin.
rewrite ge0_integral_sum //.
- by move=>i; apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_matrix_target.
- by move=>i z _; rewrite lee_fin sqr_ge0.
apply: (le_trans (y := (\sum_(i<n) B%:E)%E)).
- apply: lee_sum=>i _; rewrite /sparse_matrix_target
    (@sparse_iid_row_integral n h P i (fun z=>(sparse_head_normalized_target p m z^+2)%:E)) //.
  apply/measurable_EFinP; apply: measurable_funX; exact: measurable_sparse_head_normalized_target.
- by rewrite sumEFin sumr_const card_ord -(mulr_natl B n).
Qed.

Lemma sparse_iid_target_square_sum_tail n h p (P : probability 'rV[RR]_h RR)
    (m : 'rV[RR]_h) (B t : R) :
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <= B%:E)%E -> 0<t ->
  (independent_row_matrix_law (fun=>P) n
    [set H | (t < \sum_(i<n) sparse_matrix_target p m H i^+2)%R] <= (n%:R*B/t)%:E)%E.
Proof.
move=> hb t0.
have mf : measurable_fun [set: 'M[RR]_(n,h)]
    (fun H=>\sum_(i<n) sparse_matrix_target p m H i^+2 : RR).
  apply: measurable_sum=>i; apply: measurable_funX; exact: measurable_sparse_matrix_target.
have fn H : 0<=\sum_(i<n) sparse_matrix_target p m H i^+2.
  by apply: sumr_ge0=>i _; exact: sqr_ge0.
have ht := @markov_ge0 _ _ RR (independent_row_matrix_law (fun=>P) n) _ t mf fn t0.
apply: le_trans ht _.
have hi := sparse_iid_target_square_sum n hb.
have ti0 : (0 <= (t^-1)%:E)%E by rewrite lee_fin invr_ge0; exact: ltW t0.
have hp := lee_wpmul2l ti0 hi.
move: hp; by rewrite -EFinM mulrC.
Qed.

Lemma sparse_iid_target_max_tail n h (P : probability 'rV[RR]_h RR)
    (m : 'rV[RR]_h) (t q : R) :
  0<=t ->
  (P [set z | (t<=`|sparse_head_target (sparse_head_scale m) m z|)%R] <= q%:E)%E ->
  (independent_row_matrix_law (fun=>P) n
    [set H | (t<max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H)))%R]
      <= (n%:R*q)%:E)%E.
Proof.
move=> t0 ht.
pose F (i : 'I_n) := [set H : 'M[RR]_(n,h) |
  t<=`|sparse_head_target (sparse_head_scale m) m (row i H)|].
have mf i : measurable_fun [set: 'M[RR]_(n,h)]
    (fun H=>sparse_head_target (sparse_head_scale m) m (row i H) : RR).
  exact: measurableT_comp (measurable_sparse_head_target _ _) (measurable_sparse_matrix_row i).
have mF i : measurable(F i).
  rewrite /F -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurableT_comp (mf i).
have mA : measurable [set z : 'rV[RR]_h | t<=`|sparse_head_target (sparse_head_scale m) m z|].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurableT_comp (measurable_sparse_head_target (sparse_head_scale m) m).
have sub : [set H : 'M[RR]_(n,h) |
    t<max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H))]
      `<=` \bigcup_i F i.
  move=>H hx; apply: contrapT=>hn.
  have hm : max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H))<=t.
    apply: bigmax_le=>// i _.
    have ni : ~ F i H by move=>hi; apply: hn; exists i=>//.
    have hh : `|sparse_head_target (sparse_head_scale m) m (row i H)|<t.
      by rewrite ltNge; apply/negP; exact: ni.
    exact: ltW hh.
  by move: hx; rewrite /= (ltNge t) hm.
have mm : measurable [set H : 'M[RR]_(n,h) |
    t<max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H))].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr=>//.
  exact: measurable_max_norm mf.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  apply: fin_bigcup_measurable=>[|i _]; first exact: cardinality.finite_finset.
  exact: mF.
apply: le_trans (measure_bigcup_fin_le _ mF) _.
apply: (le_trans (y := (\sum_(i<n) q%:E)%E)).
- apply: lee_sum=>i _.
  have he : independent_row_matrix_law (fun=>P) n (F i) =
    P [set z | t<=`|sparse_head_target (sparse_head_scale m) m z|].
    exact: (@sparse_iid_row_probability n h P i
      [set z | t<=`|sparse_head_target (sparse_head_scale m) m z|] mA).
  exact (eq_ind_r (fun a : \bar RR => (a<=q%:E)%E) ht he).
- by rewrite sumEFin sumr_const card_ord -(mulr_natl q n).
Qed.

Lemma sparse_matrix_target_size_le n h p (m : 'rV[RR]_h)
    (H : 'M[RR]_(n,h)) (L B t : R) :
  0<=L -> 0<=t ->
  (\sum_(i<n) sparse_matrix_target p m H i^+2)<=B ->
  max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H))<=t ->
  shifted_interpolation_size p L (sparse_matrix_target p m H) <=
    L*(Num.sqrt B/p%:R+ln(p%:R : RR)^+4/p%:R*t).
Proof.
move=> L0 t0 sB mt; rewrite /shifted_interpolation_size.
apply: ler_wpM2l=>//; apply: lerD.
- apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  exact: ler_wsqrtr sB.
- have hm : max_norm(sparse_matrix_target p m H)<=t/Num.sqrt p%:R.
    apply: bigmax_le; first by rewrite divr_ge0 ?sqrtr_ge0.
    move=>i _; rewrite /sparse_matrix_target /sparse_head_normalized_target normrM
      normfV (ger0_norm (sqrtr_ge0 _)).
    apply: ler_wpM2r; first by rewrite invr_ge0 sqrtr_ge0.
    exact: le_trans (ler_max_norm _ i) mt.
  have ll0 : 0<=ln(p%:R : RR)^+4/Num.sqrt p%:R
    by rewrite divr_ge0 ?sqrtr_ge0 // exprn_even_ge0.
  have hh := ler_wpM2l ll0 hm.
  apply: le_trans hh _.
  have ee : ln(p%:R : RR)^+4/Num.sqrt p%:R*(t/Num.sqrt p%:R) =
      ln(p%:R : RR)^+4/p%:R*t.
    by rewrite mulrACA -invfM -expr2 sqr_sqrtr ?ler0n //; ring.
  by rewrite ee.
Qed.

Lemma sparse_iid_target_size_tail n h p (P : probability 'rV[RR]_h RR)
    (m : 'rV[RR]_h) (L V B t q : R) :
  0<=L -> 0<B -> 0<=t ->
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <= V%:E)%E ->
  (P [set z | (t<=`|sparse_head_target (sparse_head_scale m) m z|)%R] <= q%:E)%E ->
  (independent_row_matrix_law (fun=>P) n
    [set H | (L*(Num.sqrt B/p%:R+ln(p%:R : RR)^+4/p%:R*t)<
      shifted_interpolation_size p L (sparse_matrix_target p m H))%R] <=
      (n%:R*V/B+n%:R*q)%:E)%E.
Proof.
move=> L0 B0 t0 hV ht.
pose Q := independent_row_matrix_law (fun=>P) n.
pose ES := [set H : 'M[RR]_(n,h) | B<\sum_(i<n) sparse_matrix_target p m H i^+2].
pose EM := [set H : 'M[RR]_(n,h) |
  t<max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H))].
have ms : measurable ES.
  rewrite /ES -[X in measurable X]setTI; apply: measurable_fun_ltr=>//.
  apply: measurable_sum=>i; apply: measurable_funX; exact: measurable_sparse_matrix_target.
have mm : measurable EM.
  rewrite /EM -[X in measurable X]setTI; apply: measurable_fun_ltr=>//.
  apply: measurable_max_norm=>i.
  exact: measurableT_comp (measurable_sparse_head_target _ _) (measurable_sparse_matrix_row i).
have mt : measurable [set H : 'M[RR]_(n,h) |
    L*(Num.sqrt B/p%:R+ln(p%:R : RR)^+4/p%:R*t)<
      shifted_interpolation_size p L (sparse_matrix_target p m H)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr=>//.
  exact: measurable_sparse_matrix_size.
have sub : [set H : 'M[RR]_(n,h) |
    L*(Num.sqrt B/p%:R+ln(p%:R : RR)^+4/p%:R*t)<
      shifted_interpolation_size p L (sparse_matrix_target p m H)] `<=` ES `|` EM.
  move=>H hx.
  have [hs|hs] := ltP B (\sum_(i<n) sparse_matrix_target p m H i^+2); first by left.
  have [hm|hm] := ltP t (max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H)));
    first by right.
  have hb := sparse_matrix_target_size_le L0 t0 hs hm.
  by move: hx; rewrite /= ltNge hb.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
  exact: measurableU.
apply: le_trans (measureU2 Q ms mm) _; rewrite EFinD.
exact: leeD (sparse_iid_target_square_sum_tail n hV B0)
  (sparse_iid_target_max_tail n t0 ht).
Qed.

Definition sparse_target_log_level p : RR := 1+4*ln(p%:R+1).

Lemma sparse_target_log_level_ge1 p : 1<=sparse_target_log_level p.
Proof.
rewrite /sparse_target_log_level lerDl mulr_ge0 // ln_ge0 //.
have := ler0n RR p; lra.
Qed.

Lemma sparse_target_log_exp_bound p :
  expR(-sparse_target_log_level p) <= ((p%:R+1)^+4)^-1.
Proof.
have pp : 0<(p%:R : RR)+1 by have := ler0n RR p; lra.
have ee : expR (-(4*ln(p%:R+1))) = ((p%:R+1)^+4)^-1 :> RR.
  by rewrite expRN expRM_natl lnK ?posrE.
rewrite -ee ler_expR /sparse_target_log_level; lra.
Qed.

Lemma sparse_iid_target_log_max_tail n h p K
    (P : probability 'rV[RR]_h RR) (m : 'rV[RR]_h) :
  0<K ->
  (forall u, 1<=u ->
    (P [set z | (sparse_target_tail_scale K h*u<=
      `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E) ->
  (independent_row_matrix_law (fun=>P) n
    [set H | (sparse_target_tail_scale K h*sparse_target_log_level p<
      max_norm(fun i=>sparse_head_target (sparse_head_scale m) m (row i H)))%R]
       <= (4*n%:R/(p%:R+1)^+4)%:E)%E.
Proof.
move=> K0 ht.
have a0 : 0<=sparse_target_tail_scale K h.
  rewrite /sparse_target_tail_scale; apply: addr_ge0.
  - exact: ltW (sparse_center_tail_scale_gt0 h K0).
  - by rewrite mulr_ge0 ?(ltW K0).
have h0 := mulr_ge0 a0 (le_trans ler01 (sparse_target_log_level_ge1 p)).
have hb := sparse_iid_target_max_tail n h0 (ht _ (sparse_target_log_level_ge1 p)).
apply: le_trans hb _; rewrite lee_fin.
have hmul := ler_wpM2l (mulr_ge0 (ler0n RR 4) (ler0n RR n)) (sparse_target_log_exp_bound p).
have ee : n%:R*(4*expR(-sparse_target_log_level p)) =
    4*n%:R*expR(-sparse_target_log_level p) :> RR by ring.
by rewrite ee.
Qed.

Definition sparse_target_l2_budget p (L delta : R) :=
  (delta * p%:R/(4*(L+1)))^+2.

Lemma sparse_target_l2_budget_pos p (L delta : R) :
  (0<p)%N -> 0<=L -> 0<delta -> 0<sparse_target_l2_budget p L delta.
Proof.
move=> p0 L0 d0; rewrite /sparse_target_l2_budget exprn_gt0 // divr_gt0 //.
- by rewrite mulr_gt0 ?ltr0n.
- rewrite mulr_gt0 //; lra.
Qed.

Lemma sparse_target_l2_budget_sqrt p (L delta : R) :
  (0<p)%N -> 0<=L -> 0<delta ->
  Num.sqrt(sparse_target_l2_budget p L delta)/p%:R=delta/(4*(L+1)).
Proof.
move=> p0 L0 d0.
have pR : 0<(p%:R : RR) by rewrite ltr0n.
have l0 : 0<L+1 by lra.
have pp : 0<=delta * p%:R/(4*(L+1)) by rewrite divr_ge0 ?mulr_ge0 ?(ltW d0) ?ler0n ?(ltW l0).
rewrite /sparse_target_l2_budget sqrtr_sqr (ger0_norm pp).
have pn : (p%:R : RR)!=0 by rewrite gt_eqF.
have ln : L+1!=0 by rewrite gt_eqF.
by field.
Qed.

Lemma sparse_target_l2_budget_ratio n h p K L delta :
  (0<p)%N -> 0<=L -> 0<delta ->
  n%:R*((8*K^+4*h%:R+8)/p%:R)/sparse_target_l2_budget p L delta =
    (16*(L+1)^+2/delta^+2)*(n%:R*(8*K^+4*h%:R+8)/p%:R^+3) :> RR.
Proof.
move=> p0 L0 d0; rewrite /sparse_target_l2_budget.
have pn : (p%:R : RR)!=0 by rewrite pnatr_eq0 -lt0n.
have dn : delta!=0 by rewrite gt_eqF.
have l0 : 0<L+1 by lra.
have ln : L+1!=0 by rewrite gt_eqF.
by field.
Qed.

Lemma sparse_target_budget_small (L delta M : R) :
  0<=L -> 0<delta -> M<delta/(4*(L+1)) ->
  L*(delta/(4*(L+1))+M)<delta.
Proof.
move=> L0 d0 hM.
have l0 : 0<L+1 by lra.
have ld : 0<4*(L+1) by rewrite mulr_gt0.
have tt : 0<delta/(4*(L+1)) by rewrite divr_gt0.
have eqd : 4*(L+1)*(delta/(4*(L+1)))=delta.
  have ln : L+1!=0 by rewrite gt_eqF.
  by field.
have hh := ler_wpM2l L0 (ltW hM).
nra.
Qed.

Lemma sparse_iid_target_log_size_tail n h p K
    (P : probability 'rV[RR]_h RR) (m : 'rV[RR]_h) (L V B : R) :
  0<K -> 0<=L -> 0<B ->
  (\int[P]_z (sparse_head_normalized_target p m z^+2)%:E <= V%:E)%E ->
  (forall u, 1<=u ->
    (P [set z | (sparse_target_tail_scale K h*u<=
      `|sparse_head_target (sparse_head_scale m) m z|)%R] <= (4*expR(-u))%:E)%E) ->
  (independent_row_matrix_law (fun=>P) n
    [set H | (L*(Num.sqrt B/p%:R+ln(p%:R : RR)^+4/p%:R*
        (sparse_target_tail_scale K h*sparse_target_log_level p))<
      shifted_interpolation_size p L (sparse_matrix_target p m H))%R] <=
      (n%:R*V/B+4*n%:R/(p%:R+1)^+4)%:E)%E.
Proof.
move=> K0 L0 B0 hV ht.
have a0 : 0<=sparse_target_tail_scale K h.
  rewrite /sparse_target_tail_scale; apply: addr_ge0.
  - exact: ltW (sparse_center_tail_scale_gt0 h K0).
  - by rewrite mulr_ge0 ?(ltW K0).
have t0 := mulr_ge0 a0 (le_trans ler01 (sparse_target_log_level_ge1 p)).
have hb := sparse_iid_target_size_tail n L0 B0 t0 hV
  (ht _ (sparse_target_log_level_ge1 p)).
apply: le_trans hb _; rewrite lee_fin lerD2l.
have he := ler_wpM2l (mulr_ge0 (ler0n RR 4) (ler0n RR n)) (sparse_target_log_exp_bound p).
have ee : n%:R*(4*expR(-sparse_target_log_level p)) =
    4*n%:R*expR(-sparse_target_log_level p) :> RR by ring.
by rewrite ee.
Qed.

Theorem sparse_iid_target_size_small K L alpha (n h p : nat -> nat)
    (P : forall d, probability 'rV[RR]_(h d) RR)
    (m : forall d, 'rV[RR]_(h d)) :
  0<K -> 0<=L -> family_cofinal p ->
  family_sequence_limit (fun d=>(h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d=>(n d)%:R/(p d)%:R^+2 : RR) alpha ->
  (forall d, (\int[P d]_z (sparse_head_normalized_target (p d) (m d) z^+2)%:E <=
      ((8*K^+4*(h d)%:R+8)/(p d)%:R)%:E)%E) ->
  (forall d u, 1<=u ->
    (P d [set z | (sparse_target_tail_scale K (h d)*u<=
      `|sparse_head_target (sparse_head_scale (m d)) (m d) z|)%R] <= (4*expR(-u))%:E)%E) ->
  forall eps delta : R, 0<eps -> 0<delta -> exists D, forall d, (D<=d)%N ->
    (independent_row_matrix_law (fun=>P d) (n d)
      [set H | (delta<=shifted_interpolation_size (p d) L
        (sparse_matrix_target (p d) (m d) H))%R] <= eps%:E)%E.
Proof.
move=> K0 L0 hp hh hn hV ht eps delta eps0 delta0.
have lp0 : 0<L+1 by lra.
pose c : RR := 16*(L+1)^+2/delta^+2.
have c0 : 0<c by rewrite /c divr_gt0 ?mulr_gt0 ?exprn_gt0.
have e20 : 0<eps/2 by rewrite divr_gt0.
have ec0 : 0<eps/(2*c) by rewrite divr_gt0 // mulr_gt0.
have dt0 : 0<delta/(4*(L+1)) by rewrite divr_gt0 // mulr_gt0.
have [D0 hD0] := hp 1%N.
have [D1 hD1] := sparse_target_log_rate K hp hh dt0.
have [D2 hD2] := sparse_target_moment_rate K hp hh hn ec0.
have [D3 hD3] := sparse_target_union_rate hp hn e20.
exists (maxn D0 (maxn D1 (maxn D2 D3)))=>d.
rewrite !geq_max=>/andP[d0 /andP[d1 /andP[d2 d3]]].
have p0 : (0<p d)%N := hD0 d d0.
pose B := sparse_target_l2_budget (p d) L delta.
have B0 : 0<B := sparse_target_l2_budget_pos p0 L0 delta0.
pose M := ln((p d)%:R : RR)^+4/(p d)%:R*
  (sparse_target_tail_scale K (h d)*sparse_target_log_level (p d)).
have Msmall : M<delta/(4*(L+1)).
  have hm := hD1 d d1; rewrite subr0 in hm.
  apply: le_lt_trans (ler_norm M) _.
  exact: hm.
have envelope : L*(Num.sqrt B/(p d)%:R+M)<delta.
  rewrite /B sparse_target_l2_budget_sqrt //.
  exact: sparse_target_budget_small L0 delta0 Msmall.
have mBad : measurable [set H : 'M[RR]_(n d,h d) |
    delta<=shifted_interpolation_size (p d) L (sparse_matrix_target (p d) (m d) H)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ler=>//.
  exact: measurable_sparse_matrix_size.
have mEnv : measurable [set H : 'M[RR]_(n d,h d) |
    L*(Num.sqrt B/(p d)%:R+M)<
      shifted_interpolation_size (p d) L (sparse_matrix_target (p d) (m d) H)].
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr=>//.
  exact: measurable_sparse_matrix_size.
have sub : [set H : 'M[RR]_(n d,h d) |
    delta<=shifted_interpolation_size (p d) L (sparse_matrix_target (p d) (m d) H)] `<=`
    [set H | L*(Num.sqrt B/(p d)%:R+M)<
      shifted_interpolation_size (p d) L (sparse_matrix_target (p d) (m d) H)].
  by move=>H /= hx; exact: lt_le_trans envelope hx.
apply: le_trans (le_measure _ _ _ sub) _; rewrite ?inE //.
have hb := sparse_iid_target_log_size_tail (n d) K0 L0 B0 (hV d) (ht d).
apply: le_trans hb _; rewrite lee_fin /B sparse_target_l2_budget_ratio //.
have h2 := hD2 d d2; rewrite subr0 in h2.
have h3 := hD3 d d3; rewrite subr0 in h3.
have a2 : (n d)%:R*(8*K^+4*(h d)%:R+8)/(p d)%:R^+3<eps/(2*c).
  exact: le_lt_trans (ler_norm _) h2.
have a3 : 4*(n d)%:R/((p d)%:R+1)^+4<eps/2.
  exact: le_lt_trans (ler_norm _) h3.
have a2c : c*((n d)%:R*(8*K^+4*(h d)%:R+8)/(p d)%:R^+3)<c*(eps/(2*c)).
  by rewrite ltr_pM2l.
have cn : c!=0 by rewrite gt_eqF.
have ce : c*(eps/(2*c))=eps/2 by field.
rewrite ce in a2c.
change (c*((n d)%:R*(8*K^+4*(h d)%:R+8)/(p d)%:R^+3)+
    4*(n d)%:R/((p d)%:R+1)^+4<=eps).
have total := ltrD a2c a3.
have halves : eps/2+eps/2=eps by field.
rewrite halves in total; exact: ltW total.
Qed.

Theorem sparse_finite_iid_target_size_small K L alpha (n h p : nat -> nat)
    (I : nat -> finType) (w : forall d, I d -> R)
    (nu : forall d, I d -> nat -> probability (measurableTypeR R) R)
    (hw : forall d, mixture_weights (w d))
    (hnu : forall d (i : I d) j, (j<h d)%N -> mixture_component_law K (nu d i j))
    (m : forall d, 'rV[RR]_(h d)) :
  0<K -> 0<=L -> family_cofinal p ->
  family_sequence_limit (fun d=>(h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d=>(n d)%:R/(p d)%:R^+2 : RR) alpha ->
  forall eps delta : R, 0<eps -> 0<delta -> exists D, forall d, (D<=d)%N ->
    (independent_row_matrix_law
      (fun=>mixture (fun i=>point_law (h d) (nu d i)) (hw d)) (n d)
      [set H | (delta<=shifted_interpolation_size (p d) L
        (sparse_matrix_target (p d) (m d) H))%R] <= eps%:E)%E.
Proof.
move=> K0 L0 hp hh hn.
apply: (@sparse_iid_target_size_small K L alpha n h p
  (fun d=>mixture (fun i=>point_law (h d) (nu d i)) (hw d))
  m K0 L0 hp hh hn).
- move=>d; exact: (@sparse_finite_normalized_second (I d) K (h d) (p d)
    (w d) (nu d) (hw d) (hnu d) (m d)).2.
- move=>d u u1; exact: (@sparse_finite_target_tail (I d) K (h d)
    (w d) (nu d) (hw d) (hnu d) (m d) u K0 u1).
Qed.

Theorem sparse_countable_iid_target_size_small K L alpha (n h p : nat -> nat)
    (w : nat -> nat -> R)
    (nu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (hw : forall d, cmixture_weights (w d))
    (hnu : forall d i j, (j<h d)%N -> mixture_component_law K (nu d i j))
    (m : forall d, 'rV[RR]_(h d)) :
  0<K -> 0<=L -> family_cofinal p ->
  family_sequence_limit (fun d=>(h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d=>(n d)%:R/(p d)%:R^+2 : RR) alpha ->
  forall eps delta : R, 0<eps -> 0<delta -> exists D, forall d, (D<=d)%N ->
    (independent_row_matrix_law
      (fun=>cmixture (fun i=>point_law (h d) (nu d i)) (hw d)) (n d)
      [set H | (delta<=shifted_interpolation_size (p d) L
        (sparse_matrix_target (p d) (m d) H))%R] <= eps%:E)%E.
Proof.
move=> K0 L0 hp hh hn.
apply: (@sparse_iid_target_size_small K L alpha n h p
  (fun d=>cmixture (fun i=>point_law (h d) (nu d i)) (hw d))
  m K0 L0 hp hh hn).
- move=>d; exact: (@sparse_countable_normalized_second K (h d) (p d)
    (w d) (nu d) (hw d) (hnu d) (m d)).2.
- move=>d u u1; exact: (@sparse_countable_target_tail K (h d)
    (w d) (nu d) (hw d) (hnu d) (m d) u K0 u1).
Qed.
