(* Existence of conditioned fits for shifted Gaussian samples.
   The coordinate split is an exact law identity. Every construction of a
   fitting matrix is existential, with no measurable selection asserted. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences exp.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun realfun measurable_realfun probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss normal_integral gauss_moments.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.
From GaussianAnalysis.probability Require Import symmetrization small_ball_method.
From GaussianAnalysis.comparison Require Import normal_mgf.
From GaussianAnalysis.random_matrix Require Import goe_entries.
From EllipsoidUniversality.Shifted Require Import GaussianTargets GaussianTargetBounds
  GaussianRows GaussianExports Translations.
From GaussianAnalysis.probability Require Import lindeberg conditioning tuple_rows.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality.Condition Require Import Curve.
Require Import EllipsoidUniversality.Condition.Theorem.
From EllipsoidUniversality.Gaussian Require Import InProbability FittingError.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions ConditionDefinitions.
From EllipsoidUniversality.Sat Require Import Universality.
From EllipsoidUniversality.Model Require Import Measurability.
From EllipsoidUniversality.Condition Require Import Unsat.
From GaussianAnalysis.matrix Require Import condition_perturbation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation RR := (R : realType).


Definition gaussian_split_index n p (k : 'I_(n + n * p)) : 'I_(n * (1 + p)) :=
  match fintype.split k with
  | inl i => row_index i (lshift p (ord0 : 'I_1))
  | inr j => row_index (sample_flat_row j) (rshift 1 (sample_flat_col j))
  end.

Lemma gaussian_split_index_left n p (i : 'I_n) :
  gaussian_split_index (lshift (n * p) i) = row_index i (lshift p (ord0 : 'I_1)).
Proof. by rewrite /gaussian_split_index -/(unsplit (inl i)) unsplitK. Qed.

Lemma gaussian_split_index_right n p (j : 'I_(n * p)) :
  gaussian_split_index (rshift n j) =
    row_index (sample_flat_row j) (rshift 1 (sample_flat_col j)).
Proof. by rewrite /gaussian_split_index -/(unsplit (inr j)) unsplitK. Qed.

Lemma gaussian_split_index_injective n p : injective (@gaussian_split_index n p).
Proof.
move=> k l; rewrite -[k]splitK -[l]splitK.
case: (fintype.split k) => i; case: (fintype.split l) => j /=;
  rewrite ?gaussian_split_index_left ?gaussian_split_index_right => h.
- have := congr1 (@sample_flat_row n (1 + p)) h.
  by rewrite !sample_flat_rowK => ->.
- have := congr1 (@sample_flat_col n (1 + p)) h.
  by rewrite !sample_flat_colK => /eqP; rewrite eq_lrshift.
- have := congr1 (@sample_flat_col n (1 + p)) h.
  by rewrite !sample_flat_colK => /eqP; rewrite eq_rlshift.
- have hr := congr1 (@sample_flat_row n (1 + p)) h; have hc := congr1 (@sample_flat_col n (1 + p)) h.
  rewrite !sample_flat_rowK in hr.
  rewrite !sample_flat_colK in hc.
  have hc' : sample_flat_col i = sample_flat_col j := rshift_inj hc.
  congr rshift.
  by rewrite -[i]sample_flat_indicesK -[j]sample_flat_indicesK hr hc'.
Qed.

Definition gaussian_regroup n p (x : paper_main_sample n (1 + p)) :
    'rV[RR]_(n + n * p) :=
  row_of_tuple _ (tuple_pick (@gaussian_split_index n p) x).
Definition gaussian_first n p (x : paper_main_sample n (1 + p)) : 'rV[RR]_n :=
  lsubmx (gaussian_regroup x).
Definition gaussian_rest n p (x : paper_main_sample n (1 + p)) :
    paper_main_sample n p := tuple_of_row (rsubmx (gaussian_regroup x)).

Lemma measurable_gaussian_regroup n p :
  measurable_fun setT (@gaussian_regroup n p).
Proof.
apply: measurableT_comp; first exact: measurable_row_of_tuple.
exact: measurable_tuple_pick.
Qed.

Lemma measurable_gaussian_first n p : measurable_fun setT (@gaussian_first n p).
Proof.
rewrite /gaussian_first.
apply: measurableT_comp; first exact: measurable_lsubmx.
exact: measurable_gaussian_regroup.
Qed.

Lemma measurable_gaussian_rest n p : measurable_fun setT (@gaussian_rest n p).
Proof.
rewrite /gaussian_rest.
apply: measurableT_comp; first exact: measurable_tuple_of_row.
apply: measurableT_comp; first exact: measurable_rsubmx.
exact: measurable_gaussian_regroup.
Qed.

Lemma gaussian_firstE n p (x : paper_main_sample n (1 + p)) (i : 'I_n) :
  gaussian_first x 0 i = tnth x (row_index i (lshift p (ord0 : 'I_1))).
Proof.
rewrite /gaussian_first /gaussian_regroup /lsubmx !mxE /tuple_pick tnth_mktuple.
by rewrite gaussian_split_index_left.
Qed.

Lemma gaussian_restE n p (x : paper_main_sample n (1 + p)) (k : 'I_(n * p)) :
  tnth (gaussian_rest x) k =
    tnth x (row_index (sample_flat_row k) (rshift 1 (sample_flat_col k))).
Proof.
rewrite /gaussian_rest tnth_tuple_of_row /gaussian_regroup /rsubmx !mxE
  /tuple_pick tnth_mktuple.
by rewrite gaussian_split_index_right.
Qed.

Lemma gaussian_regroup_law n p (A : set 'rV[RR]_(n + n * p)) : measurable A ->
  gaussian_product_law (n * (1 + p)) (@gaussian_regroup n p @^-1` A) =
    gauss (n + n * p) A.
Proof.
move=> mA; rewrite gauss_gaussian_product_law // !gaussian_product_law_tuple_prod.
change (tuple_prod (fun=> gaussian_law_probability) (n * (1 + p))
  (tuple_pick (@gaussian_split_index n p) @^-1` (row_of_tuple _ @^-1` A)) =
  tuple_prod (fun=> gaussian_law_probability) (n + n * p) (row_of_tuple _ @^-1` A)).
apply: tuple_prod_pick; first exact: gaussian_split_index_injective.
- by move=> i.
- rewrite -[X in measurable X]setTI; exact: measurable_row_of_tuple.
Qed.

Lemma gaussian_first_law n p (A : set 'rV[RR]_n) : measurable A ->
  gaussian_product_law (n * (1 + p)) (@gaussian_first n p @^-1` A) = gauss n A.
Proof.
move=> mA.
have mlA : measurable (@lsubmx RR 1 n (n * p) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_lsubmx.
rewrite /gaussian_first (gaussian_regroup_law mlA).
exact: gauss_lsubmx.
Qed.

Lemma gaussian_tuple_of_row_law d (A : set (d.-tuple (measurableTypeR R))) :
  measurable A -> gauss d (@tuple_of_row d @^-1` A) = gaussian_product_law d A.
Proof.
move=> mA.
have mtA : measurable (@tuple_of_row d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_of_row.
rewrite gauss_gaussian_product_law //; congr (gaussian_product_law d _).
apply/funext => x /=; congr (A _); apply: eq_from_tnth => i.
by rewrite tnth_tuple_of_row row_of_tupleE.
Qed.

Lemma gaussian_rest_law n p (A : set (paper_main_sample n p)) : measurable A ->
  gaussian_product_law (n * (1 + p)) (@gaussian_rest n p @^-1` A) =
    gaussian_product_law (n * p) A.
Proof.
move=> mA.
have mtA : measurable (@tuple_of_row (n * p) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_of_row.
have mrA : measurable
    ((fun z : 'rV[RR]_(n + n * p) => tuple_of_row (rsubmx z)) @^-1` A).
  have mf : measurable_fun setT
      (fun z : 'rV[RR]_(n + n * p) => tuple_of_row (rsubmx z)).
    apply: measurableT_comp; first exact: measurable_tuple_of_row.
    exact: measurable_rsubmx.
  by rewrite -[X in measurable X]setTI; exact: mf.
rewrite /gaussian_rest (gaussian_regroup_law mrA).
rewrite (gauss_rsubmx _ mtA).
exact: gaussian_tuple_of_row_law.
Qed.

Lemma gaussian_first_rest_joint_law n p
    (A : set ('rV[RR]_n * 'rV[RR]_(n * p))) : measurable A ->
  gaussian_product_law (n * (1 + p))
    ((fun x => (gaussian_first x, row_of_tuple _ (gaussian_rest x))) @^-1` A) =
  (gauss n \x gauss (n * p))%E A.
Proof.
move=> mA.
have rt (x : paper_main_sample n (1 + p)) : row_of_tuple _ (gaussian_rest x) = rsubmx (gaussian_regroup x).
  apply/rowP => k; by rewrite row_of_tupleE /gaussian_rest tnth_tuple_of_row.
have -> : ((fun x => (gaussian_first x, row_of_tuple _ (gaussian_rest x))) @^-1` A) =
    @gaussian_regroup n p @^-1` ((fun z : 'rV[RR]_(n + n * p) => (lsubmx z, rsubmx z)) @^-1` A).
  by apply/funext => x; rewrite /= rt.
have msA : measurable
    ((fun z : 'rV[RR]_(n + n * p) => (lsubmx z, rsubmx z)) @^-1` A).
  have mf : measurable_fun setT
      (fun z : 'rV[RR]_(n + n * p) => (lsubmx z, rsubmx z)).
    apply: measurable_fun_pair.
    - exact: measurable_lsubmx.
    - exact: measurable_rsubmx.
  by rewrite -[X in measurable X]setTI; exact: mf.
rewrite gaussian_regroup_law //.
exact: gaussian_row_coordinate_split_law.
Qed.

Lemma gaussian_split_point_entry n d (x : paper_main_sample n d)
    (i : 'I_n) (j : 'I_d) :
  paper_main_point x i j 0 = tnth x (row_index i j).
Proof.
by rewrite -sample_row_tuple_entry /sample_row_tuple tnth_mktuple !mxE.
Qed.

Lemma gaussian_first_rest_point n p (x : paper_main_sample n (1 + p)) (i : 'I_n) :
  paper_main_point x i =
    col_mx (const_mx (gaussian_first x 0 i) : 'cV[RR]_1)
      (paper_main_point (gaussian_rest x) i).
Proof.
apply/colP => j; rewrite -[j]splitK; case: (fintype.split j) => k /=.
- by rewrite (ord1 k) col_mxEu gaussian_split_point_entry
    [RHS]mxE gaussian_firstE (ord1 ord0).
- rewrite col_mxEd !gaussian_split_point_entry gaussian_restE
    sample_flat_rowK sample_flat_colK.
  by [].
Qed.

Definition gaussian_axis_shift p (a : R) : 'cV[RR]_(1 + p) :=
  col_mx (const_mx a : 'cV[RR]_1) 0.

Lemma gaussian_axis_shift_point n p (x : paper_main_sample n (1 + p))
    (a : R) (i : 'I_n) :
  paper_main_point (sample_translate (gaussian_axis_shift p a) x) i =
    col_mx (const_mx (gaussian_first x 0 i + a) : 'cV[RR]_1)
      (paper_main_point (gaussian_rest x) i).
Proof.
rewrite sample_translate_point gaussian_first_rest_point /gaussian_axis_shift
  add_col_mx addr0.
by congr col_mx; apply/matrixP => j k; rewrite !mxE.
Qed.

Lemma gaussian_fit_common_level n p (g : paper_main_sample n p) (C : R) :
  (0 < p)%N -> universality_conditioned_fit_event n p C g ->
  exists (S : 'M[R]_p) (q : R), cond_slice C S /\
    forall i : 'I_n, paper_main_quadratic_form S (paper_main_point g i) = q.
Proof.
move=> p0 hfit.
have [S [b [hS hq]]] := cond_fit_slice n p g C p0 hfit.
exists S, (Num.sqrt p%:R * b + paper_main_trace S); split => // i.
have h := qf_sample_W n p g i S p0.
by rewrite hq in h.
Qed.

Lemma gaussian_conditioned_point_nonzero n d (x : paper_main_sample n d)
    (C : R) (i : 'I_n) :
  universality_conditioned_fit_event n d C x -> paper_main_point x i != 0.
Proof.
move=> [S [lm [_ [_ [_ hfit]]]]]; apply/eqP => hi.
have h := hfit i.
rewrite hi pm_qf_col mulmx0 mxdot0r in h.
by move: h => /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma gaussian_axis_point_nonzero n p (x : paper_main_sample n (1 + p))
    (a C : R) (i : 'I_n) :
  universality_conditioned_fit_event n p C (gaussian_rest x) ->
  paper_main_point (sample_translate (gaussian_axis_shift p a) x) i != 0.
Proof.
move=> hfit.
have hg := gaussian_conditioned_point_nonzero i hfit.
apply/eqP => h.
have h' := congr1 (@dsubmx R 1 p 1) h.
have dz : @dsubmx R 1 p 1 0 = 0 by apply/matrixP => j k; rewrite !mxE.
rewrite gaussian_axis_shift_point col_mxKd dz in h'.
by move: hg; rewrite h' eqxx.
Qed.

Lemma gaussian_axis_small_fit n p (x : paper_main_sample n (1 + p))
    (a C D delta L : R) :
  (0 < n)%N -> (0 < p)%N -> 1 <= D -> 0 <= delta -> delta < D^-1 ->
  0 <= L -> condition_perturbation_bound D delta <= C ->
  universality_conditioned_fit_event n p D (gaussian_rest x) ->
  mixture_interpolation n p L (gaussian_rest x) ->
  shifted_interpolation_size p L (gaussian_shift_target p 1 a (gaussian_first x)) <= delta ->
  universality_conditioned_fit_event n (1 + p) C
    (sample_translate (gaussian_axis_shift p a) x).
Proof.
move=> n0 p0 D1 de0 deD L0 DC hfit hI hsize.
have [A [q [hA hq]]] := gaussian_fit_common_level p0 hfit.
apply: (conditioned_fit_mono n (1 + p) (condition_perturbation_bound D delta) C _ DC).
apply: (@shifted_unit_block_interpolation n p (gaussian_rest x)
  (sample_translate (gaussian_axis_shift p a) x)
  (fun i => gaussian_first x 0 i + a) A D delta L (1 + a ^+ 2) q
  p0 D1 de0 deD L0 hA hI).
- exact: gaussian_axis_shift_point.
- exact: hq.
- exists (Ordinal n0); exact: gaussian_axis_point_nonzero hfit.
- have he : (fun i : 'I_n =>
      - ((gaussian_first x 0 i + a) ^+ 2 - (1 + a ^+ 2)) / Num.sqrt p%:R) =
      gaussian_shift_target p 1 a (gaussian_first x).
    apply/funext => i; rewrite /gaussian_shift_target /gaussian_centered_shift_square.
    by rewrite mulN1r.
  by rewrite he.
Qed.

Lemma gaussian_condition_perturbation_margin (D C : R) :
  1 < D -> D < C -> exists delta : R,
    [/\ 0 < delta, delta < D^-1 & condition_perturbation_bound D delta <= C].
Proof.
move=> D1 DC.
have D0 : 0 < D := lt_trans ltr01 D1.
have Dn : D != 0 by rewrite gt_eqF.
have C10 : 0 < C + 1 by nra.
have C1n : C + 1 != 0 by rewrite gt_eqF.
have den0 : 0 < 2 * D * (C + 1) by rewrite !mulr_gt0.
pose delta := (C - D) / (2 * D * (C + 1)).
have de0 : 0 < delta by rewrite /delta divr_gt0 // subr_gt0.
have deD : delta < D^-1.
  rewrite /delta ltr_pdivrMr //.
  have -> : D^-1 * (2 * D * (C + 1)) = 2 * (C + 1) by field.
  nra.
have denom0 : 0 < D^-1 - delta by rewrite subr_gt0.
have denomn : D^-1 - delta != 0 by rewrite gt_eqF.
have CD20 : 0 < C + D + 2 by nra.
have CD2n : C + D + 2 != 0 by rewrite gt_eqF.
exists delta; split => //.
have he : condition_perturbation_bound D delta =
    D + (D + 1) * (C - D) / (C + D + 2).
  rewrite /condition_perturbation_bound /delta; field.
have hf : (D + 1) * (C - D) / (C + D + 2) <= C - D.
  rewrite ler_pdivrMr //; nra.
rewrite he; nra.
Qed.

Lemma gaussian_density_positive (N : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to N alpha ->
  exists D : nat, forall p, (D <= p)%N -> (0 < N p)%N.
Proof.
move=> a0 hN.
have a20 : 0 < alpha / 2 by rewrite divr_gt0.
have [D hD] := hN _ a20.
exists D => p pD.
have h := hD p pD; rewrite /paper_main_density ltr_norml in h.
move/andP: h => [h _].
rewrite lt0n; apply/eqP => hz.
move: h; rewrite hz /= => h.
change (is_true (- (alpha / 2) < (0 : RR) / p%:R ^+ 2 - alpha)) in h.
rewrite mul0r sub0r in h; nra.
Qed.

Lemma gaussian_complement_probability dT (T : measurableType dT)
    (P : probability T RR) (A : set T) (z : R) :
  measurable A -> (`|P A - 1%:E| < z%:E)%E -> (P (~` A) <= z%:E)%E.
Proof.
move=> mA hA.
rewrite probability_setC //.
have finA : P A \is a fin_num := fin_num_measure P _ mA.
move: hA; rewrite -(fineK finA) /= lte_fin lee_fin ltr_norml.
move=> /andP[h _]; lra.
Qed.

Lemma measurable_gaussian_axis_fit n p (a C : R) :
  measurable [set x : paper_main_sample n (1 + p) |
    universality_conditioned_fit_event n (1 + p) C
      (sample_translate (gaussian_axis_shift p a) x)].
Proof.
change (measurable (sample_translate (gaussian_axis_shift p a) @^-1`
  universality_conditioned_fit_event n (1 + p) C)).
rewrite -[X in measurable X]setTI.
exact: measurable_sample_translate (measurable_conditioned_fit_event _ _ _).
Qed.

(* The probability estimates concern three events, with no claim that
   an interpolation event is independent of the random target. *)
Theorem gaussian_axis_small_shift_exists (N : nat -> nat) (a : nat -> R)
    (alpha C : R) :
  0 < alpha -> 1 < C -> alpha < condition_alpha C ->
  universality_density_tends_to N alpha ->
  (forall e : R, 0 < e -> exists D : nat, forall p, (D <= p)%N ->
    `|a p| <= e * Num.sqrt p%:R) ->
  paper_main_tends_to (fun p => gaussian_product_law (N p * (1 + p))
    [set x : paper_main_sample (N p) (1 + p) |
      universality_conditioned_fit_event (N p) (1 + p) C
        (sample_translate (gaussian_axis_shift p (a p)) x)]) 1%R.
Proof.
move=> a0 C1 aC hN ha.
have [D /andP[D1 DC] aD] := condition_alpha_left C alpha C1 aC.
have [delta [de0 deD margin]] := gaussian_condition_perturbation_margin D1 DC.
have a2 : alpha < 2%:R^-1.
  have h := condition_alpha_le4 D D1; apply: lt_le_trans aD _.
  apply: le_trans h _.
  by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
have [L [L0 hI]] := gaussian_interpolation_holds alpha a0 a2.
have [_ hC] := gaussian_condition_threshold_holds D alpha D1 a0.
have [hfit _] := hC N hN.
have fit_limit := hfit aD.
have [Dn hn] := gaussian_density_positive a0 hN.
move=> eps eps0.
have z0 : 0 < eps / 8 by rewrite divr_gt0.
have [D1' h1] := fit_limit (eps / 8) z0.
have [D2 h2] := hI N hN (eps / 8) z0.
have [D3 h3] := gaussian_small_shift_target_size hN (ltW L0) ha de0 z0.
exists (maxn 1 (maxn Dn (maxn D1' (maxn D2 D3)))) => p.
rewrite !geq_max => /andP[p1 /andP[pn /andP[pd1 /andP[pd2 pd3]]]].
have p0 : (0 < p)%N := p1.
have n0 := hn p pn.
have [E [mE PE hE]] := h2 p pd2.
pose F : set (paper_main_sample (N p) p) :=
  ~` universality_conditioned_fit_event (N p) p D.
pose T : set 'rV[RR]_(N p) := [set xi |
  delta < shifted_interpolation_size p L (gaussian_shift_target p 1 (a p) xi)].
have mF : measurable F by apply: measurableC; exact: measurable_conditioned_fit_event.
have mT : measurable T.
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
have PF : (gaussian_product_law (N p * p) F <= (eps / 8)%:E)%E.
  apply: gaussian_complement_probability; first exact: measurable_conditioned_fit_event.
  exact: h1 p pd1.
have PT : (gauss (N p) T <= (eps / 8)%:E)%E := h3 p pd3.
pose B : set (paper_main_sample (N p) (1 + p)) :=
  @gaussian_rest (N p) p @^-1` F `|` @gaussian_rest (N p) p @^-1` E `|`
    @gaussian_first (N p) p @^-1` T.
have mrF : measurable (@gaussian_rest (N p) p @^-1` F).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_rest.
have mrE : measurable (@gaussian_rest (N p) p @^-1` E).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_rest.
have mfT : measurable (@gaussian_first (N p) p @^-1` T).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_first.
have mB : measurable B by apply: measurableU => //; exact: measurableU.
have PFr : (gaussian_product_law (N p * (1 + p))
    (@gaussian_rest (N p) p @^-1` F) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_rest_law (N p) p F mF).
have PEr : (gaussian_product_law (N p * (1 + p))
    (@gaussian_rest (N p) p @^-1` E) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_rest_law (N p) p E mE).
have PTf : (gaussian_product_law (N p * (1 + p))
    (@gaussian_first (N p) p @^-1` T) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_first_law (N p) p T mT).
have PB : (gaussian_product_law (N p * (1 + p)) B <= (eps / 2)%:E)%E.
  apply: le_trans (measureU2 (gaussian_product_law (N p * (1 + p)))
    (measurableU _ _ mrF mrE) mfT) _.
  apply: le_trans (leeD (measureU2 (gaussian_product_law (N p * (1 + p))) mrF mrE)
    (lexx (gaussian_product_law (N p * (1 + p))
      (@gaussian_first (N p) p @^-1` T)))) _.
  apply: le_trans (leeD (leeD PFr PEr) PTf) _.
  rewrite -!EFinD lee_fin; clear -eps0; lra.
pose A : set (paper_main_sample (N p) (1 + p)) := [set x |
  universality_conditioned_fit_event (N p) (1 + p) C
    (sample_translate (gaussian_axis_shift p (a p)) x)].
have mA : measurable A := @measurable_gaussian_axis_fit (N p) p (a p) C.
have AB : ~` A `<=` B.
  move=> x hx; apply: contrapT => hB; apply: hx.
  have hf : universality_conditioned_fit_event (N p) p D (gaussian_rest x).
    apply: contrapT => hf; apply: hB; by left; left.
  have hi : mixture_interpolation (N p) p L (gaussian_rest x).
    apply: hE => hi; apply: hB; by left; right.
  have hs : shifted_interpolation_size p L
      (gaussian_shift_target p 1 (a p) (gaussian_first x)) <= delta.
    rewrite leNgt; apply/negP => ht; apply: hB; by right.
  exact: gaussian_axis_small_fit n0 p0 (ltW D1) (ltW de0) deD
    (ltW L0) margin hf hi hs.
have h := prob_close_one _ _ (gaussian_product_law (N p * (1 + p)))
  A B (eps / 2) mA mB AB PB.
apply: le_lt_trans h _.
rewrite lte_fin; clear -eps0; lra.
Qed.

Lemma gaussian_axis_weighted_fit n p (x : paper_main_sample n (1 + p))
    (a C D s L : R) :
  (0 < n)%N -> (0 < p)%N -> 1 <= D -> 0 < s -> s <= 1 -> 0 <= L ->
  4%:R * D ^+ 2 / s <= C ->
  universality_conditioned_fit_event n p D (gaussian_rest x) ->
  mixture_interpolation n p L (gaussian_rest x) ->
  shifted_interpolation_size p L (gaussian_shift_target p s a (gaussian_first x))
    <= (2 * D)^-1 ->
  universality_conditioned_fit_event n (1 + p) C
    (sample_translate (gaussian_axis_shift p a) x).
Proof.
move=> n0 p0 D1 s0 s1 L0 DC hfit hI hsize.
have [A [q [hA hq]]] := gaussian_fit_common_level p0 hfit.
apply: (conditioned_fit_mono n (1 + p) (4%:R * D ^+ 2 / s) C _ DC).
apply: (@shifted_weighted_block_interpolation n p (gaussian_rest x)
  (sample_translate (gaussian_axis_shift p a) x)
  (fun i => gaussian_first x 0 i + a) A D s L (1 + a ^+ 2) q
  p0 D1 s0 s1 L0 hA hI).
- exact: gaussian_axis_shift_point.
- exact: hq.
- exists (Ordinal n0); exact: gaussian_axis_point_nonzero hfit.
- exact: hsize.
Qed.

(* This weight equals min(1,e sqrt(p)/|a|) when a is nonzero, and
   equals 1 when a=0 and p>0. The quotient form avoids a separate
   zero-shift branch. The parameter e is fixed before probability tolerances. *)
Definition gaussian_axis_weight p (e a : R) :=
  (e * Num.sqrt p%:R) / Num.max (e * Num.sqrt p%:R) `|a|.

Lemma gaussian_axis_weight_bounds p (e a : R) :
  (0 < p)%N -> 0 < e ->
  [/\ 0 < gaussian_axis_weight p e a,
      gaussian_axis_weight p e a <= 1 &
      `|gaussian_axis_weight p e a * a| <= e * Num.sqrt p%:R].
Proof.
move=> p0 e0.
have r0 : (0 : RR) < Num.sqrt p%:R by rewrite sqrtr_gt0 ltr0n.
pose b := e * Num.sqrt p%:R.
have b0 : 0 < b by rewrite /b mulr_gt0.
have bm : b <= Num.max b `|a| by rewrite le_max lexx.
have am : `|a| <= Num.max b `|a| by rewrite le_max lexx orbT.
have m0 : 0 < Num.max b `|a| := lt_le_trans b0 bm.
have mn : Num.max b `|a| != 0 by rewrite gt_eqF.
have s0 : 0 < gaussian_axis_weight p e a by rewrite /gaussian_axis_weight divr_gt0.
split => //.
- by rewrite /gaussian_axis_weight -/b ler_pdivrMr // mul1r.
- rewrite normrM ger0_norm ?(ltW s0) // /gaussian_axis_weight -/b.
  apply: le_trans (ler_wpM2l (ltW (divr_gt0 b0 m0)) am) _.
  by rewrite divfK.
Qed.

Lemma gaussian_axis_weight_condition p (e a c : R) :
  (0 < p)%N -> 0 < e -> e <= 1 -> 0 <= c ->
  c / gaussian_axis_weight p e a <=
    (c / e) * (1 + `|a| / Num.sqrt p%:R).
Proof.
move=> p0 e0 e1 c0.
have r0 : (0 : RR) < Num.sqrt p%:R by rewrite sqrtr_gt0 ltr0n.
have rn : Num.sqrt p%:R != 0 :> RR by rewrite gt_eqF.
have en : e != 0 by rewrite gt_eqF.
have b0 : 0 < e * Num.sqrt p%:R by rewrite mulr_gt0.
have hmax : Num.max (e * Num.sqrt p%:R) `|a| <= Num.sqrt p%:R + `|a|.
  rewrite ge_max; apply/andP; split.
  - apply: le_trans (ler_wpM2r (ltW r0) e1) _.
    by rewrite mul1r lerDl normr_ge0.
  - by rewrite lerDr sqrtr_ge0.
rewrite /gaussian_axis_weight invf_div.
have he : c * (Num.max (e * Num.sqrt p%:R) `|a| / (e * Num.sqrt p%:R)) =
    (c / (e * Num.sqrt p%:R)) * Num.max (e * Num.sqrt p%:R) `|a| by ring.
rewrite he.
apply: le_trans (ler_wpM2l (divr_ge0 c0 (ltW b0)) hmax) _.
have -> : c / (e * Num.sqrt p%:R) * (Num.sqrt p%:R + `|a|) =
    (c / e) * (1 + `|a| / Num.sqrt p%:R) by field.
exact: lexx.
Qed.

Lemma gaussian_axis_weighted_probability (N : nat -> nat) (a s C : nat -> R)
    (alpha D L : R) :
  0 < alpha -> 1 < D -> alpha < condition_alpha D ->
  universality_density_tends_to N alpha -> 0 <= L ->
  (forall z : R, 0 < z -> exists d0 : nat, forall p, (d0 <= p)%N ->
    exists E : set (paper_main_sample (N p) p), [/\ measurable E,
      (gaussian_product_law (N p * p) E <= z%:E)%E &
      forall x, ~ E x -> mixture_interpolation (N p) p L x]) ->
  (forall z : R, 0 < z -> exists d0 : nat, forall p, (d0 <= p)%N ->
    (gauss (N p) [set xi : 'rV[RR]_(N p) |
      ((2 * D)^-1 < shifted_interpolation_size p L
        (gaussian_shift_target p (s p) (a p) xi))%R] <= z%:E)%E) ->
  (exists d0 : nat, forall p, (d0 <= p)%N ->
    [/\ 0 < s p, s p <= 1 & 4%:R * D ^+ 2 / s p <= C p]) ->
  paper_main_tends_to (fun p => gaussian_product_law (N p * (1 + p))
    [set x : paper_main_sample (N p) (1 + p) |
      universality_conditioned_fit_event (N p) (1 + p) (C p)
        (sample_translate (gaussian_axis_shift p (a p)) x)]) 1%R.
Proof.
move=> a0 D1 aD hN L0 hI hT [Ds hs].
have [_ hC] := gaussian_condition_threshold_holds D alpha D1 a0.
have [hfit _] := hC N hN.
have fit_limit := hfit aD.
have [Dn hn] := gaussian_density_positive a0 hN.
move=> eps eps0.
have z0 : 0 < eps / 8 by rewrite divr_gt0.
have [D1' h1] := fit_limit (eps / 8) z0.
have [D2 h2] := hI (eps / 8) z0.
have [D3 h3] := hT (eps / 8) z0.
exists (maxn 1 (maxn Ds (maxn Dn (maxn D1' (maxn D2 D3))))) => p.
rewrite !geq_max => /andP[p1 /andP[pds /andP[pn /andP[pd1 /andP[pd2 pd3]]]]].
have p0 : (0 < p)%N := p1.
have n0 := hn p pn.
have [s0 s1 sC] := hs p pds.
have [E [mE PE hE]] := h2 p pd2.
pose F : set (paper_main_sample (N p) p) :=
  ~` universality_conditioned_fit_event (N p) p D.
pose T : set 'rV[RR]_(N p) := [set xi |
  (2 * D)^-1 < shifted_interpolation_size p L
    (gaussian_shift_target p (s p) (a p) xi)].
have mF : measurable F by apply: measurableC; exact: measurable_conditioned_fit_event.
have mT : measurable T.
  rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
  exact: measurable_gaussian_target_size.
have PF : (gaussian_product_law (N p * p) F <= (eps / 8)%:E)%E.
  apply: gaussian_complement_probability; first exact: measurable_conditioned_fit_event.
  exact: h1 p pd1.
have PT : (gauss (N p) T <= (eps / 8)%:E)%E := h3 p pd3.
pose B : set (paper_main_sample (N p) (1 + p)) :=
  @gaussian_rest (N p) p @^-1` F `|` @gaussian_rest (N p) p @^-1` E `|`
    @gaussian_first (N p) p @^-1` T.
have mrF : measurable (@gaussian_rest (N p) p @^-1` F).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_rest.
have mrE : measurable (@gaussian_rest (N p) p @^-1` E).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_rest.
have mfT : measurable (@gaussian_first (N p) p @^-1` T).
  by rewrite -[X in measurable X]setTI; exact: measurable_gaussian_first.
have mB : measurable B by apply: measurableU => //; exact: measurableU.
have PFr : (gaussian_product_law (N p * (1 + p))
    (@gaussian_rest (N p) p @^-1` F) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_rest_law (N p) p F mF).
have PEr : (gaussian_product_law (N p * (1 + p))
    (@gaussian_rest (N p) p @^-1` E) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_rest_law (N p) p E mE).
have PTf : (gaussian_product_law (N p * (1 + p))
    (@gaussian_first (N p) p @^-1` T) <= (eps / 8)%:E)%E.
  by rewrite (@gaussian_first_law (N p) p T mT).
have PB : (gaussian_product_law (N p * (1 + p)) B <= (eps / 2)%:E)%E.
  apply: le_trans (measureU2 (gaussian_product_law (N p * (1 + p)))
    (measurableU _ _ mrF mrE) mfT) _.
  apply: le_trans (leeD (measureU2 (gaussian_product_law (N p * (1 + p))) mrF mrE)
    (lexx (gaussian_product_law (N p * (1 + p))
      (@gaussian_first (N p) p @^-1` T)))) _.
  apply: le_trans (leeD (leeD PFr PEr) PTf) _.
  rewrite -!EFinD lee_fin; clear -eps0; lra.
pose A : set (paper_main_sample (N p) (1 + p)) := [set x |
  universality_conditioned_fit_event (N p) (1 + p) (C p)
    (sample_translate (gaussian_axis_shift p (a p)) x)].
have mA : measurable A := @measurable_gaussian_axis_fit (N p) p (a p) (C p).
have AB : ~` A `<=` B.
  move=> x hx; apply: contrapT => hB; apply: hx.
  have hf : universality_conditioned_fit_event (N p) p D (gaussian_rest x).
    apply: contrapT => hf; apply: hB; by left; left.
  have hi : mixture_interpolation (N p) p L (gaussian_rest x).
    apply: hE => hi; apply: hB; by left; right.
  have ht : shifted_interpolation_size p L
      (gaussian_shift_target p (s p) (a p) (gaussian_first x)) <= (2 * D)^-1.
    rewrite leNgt; apply/negP => ht; apply: hB; by right.
  exact: gaussian_axis_weighted_fit n0 p0 (ltW D1) s0 s1 L0 sC hf hi ht.
have h := prob_close_one _ _ (gaussian_product_law (N p * (1 + p)))
  A B (eps / 2) mA mB AB PB.
apply: le_lt_trans h _.
rewrite lte_fin; clear -eps0; lra.
Qed.

Lemma gaussian_fixed_weight_parameter (D L alpha : R) :
  1 < D -> 0 <= L ->
  exists e : R, [/\ 0 < e, e <= 1 &
    2 * L * e * Num.sqrt alpha + (2 * D)^-1 / 4%:R < (2 * D)^-1].
Proof.
move=> D1 L0.
have D0 : 0 < D := lt_trans ltr01 D1.
have t0 : 0 < (2 * D)^-1 by rewrite invr_gt0 mulr_gt0.
have t1 : (2 * D)^-1 <= 1.
  by rewrite invf_le1 ?mulr_gt0 //; lra.
pose b := 4%:R * (L * Num.sqrt alpha + 1).
have b4 : 4%:R <= b.
  have h : 0 <= L * Num.sqrt alpha by rewrite mulr_ge0 // sqrtr_ge0.
  rewrite /b; clear -h; nra.
have b0 : 0 < b := lt_le_trans (ltr0n RR 4) b4.
have bn : b != 0 by rewrite gt_eqF.
pose e := (2 * D)^-1 / b.
have e0 : 0 < e by rewrite /e divr_gt0.
have e1 : e <= 1 by rewrite /e ler_pdivrMr // mul1r; lra.
have eb : e * b = (2 * D)^-1 by rewrite /e divfK.
exists e; split => //.
move: eb; rewrite /b => eb.
clearbody e; clear -e0 eb t0; nra.
Qed.

(* K is chosen before the sample-size sequence, the shift sequence and
   every probability tolerance. The constant is uniform over deterministic
   shift sequences, including those which are not o(sqrt(p)); a single
   success event for all shifts is not asserted. *)
Theorem gaussian_axis_arbitrary_shift_exists (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists K : R, 0 < K /\
  forall (N : nat -> nat) (a : nat -> R),
  universality_density_tends_to N alpha ->
  paper_main_tends_to (fun p => gaussian_product_law (N p * (1 + p))
    [set x : paper_main_sample (N p) (1 + p) |
      universality_conditioned_fit_event (N p) (1 + p)
        (K * (1 + `|a p| / Num.sqrt p%:R))
        (sample_translate (gaussian_axis_shift p (a p)) x)]) 1%R.
Proof.
move=> a0 a4.
have [st1 _ _ above] := condition_starP alpha a0 a4.
pose D := condition_star alpha + 1.
have D1 : 1 < D by rewrite /D; lra.
have aD : alpha < condition_alpha D.
  apply: above; by rewrite /D ltrDl.
have a2 : alpha < 2%:R^-1.
  apply: lt_le_trans a4 _; by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
have [L [L0 hI]] := gaussian_interpolation_holds alpha a0 a2.
have [e [e0 e1 margin]] := gaussian_fixed_weight_parameter alpha D1 (ltW L0).
pose K := 4%:R * D ^+ 2 / e.
have D0 : 0 < D := lt_trans ltr01 D1.
have K0 : 0 < K by rewrite /K divr_gt0 // mulr_gt0 // exprn_gt0.
exists K; split => // N a hN.
pose s p := gaussian_axis_weight p e (a p).
apply: (@gaussian_axis_weighted_probability N a s
  (fun p => K * (1 + `|a p| / Num.sqrt p%:R)) alpha D L
  a0 D1 aD hN (ltW L0)).
- exact: hI N hN.
- move=> z z0.
  have t0 : 0 < (2 * D)^-1 / 4%:R by rewrite divr_gt0 // invr_gt0 mulr_gt0.
  have weights : exists d0 : nat, forall p, (d0 <= p)%N ->
      `|s p| <= 1 /\ `|s p * a p| <= e * Num.sqrt p%:R.
    exists 1%N => p p1.
    have [s0 s1 sa] := gaussian_axis_weight_bounds (a p) p1 e0.
    split => //; by rewrite /s ger0_norm // ltW.
  have [d0 hd0] := @gaussian_shift_target_size_upper N alpha s a L e
    hN (ltW L0) (ltW e0) weights ((2 * D)^-1 / 4%:R) z t0 z0.
  exists d0 => p pd0.
  have mA : measurable [set xi : 'rV[RR]_(N p) |
      (2 * D)^-1 < shifted_interpolation_size p L
        (gaussian_shift_target p (s p) (a p) xi)].
    rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
    exact: measurable_gaussian_target_size.
  have mB : measurable [set xi : 'rV[RR]_(N p) |
      2 * L * e * Num.sqrt alpha + (2 * D)^-1 / 4%:R <
        shifted_interpolation_size p L (gaussian_shift_target p (s p) (a p) xi)].
    rewrite -[X in measurable X]setTI; apply: measurable_fun_ltr => //.
    exact: measurable_gaussian_target_size.
  apply: le_trans _ (hd0 p pd0).
  apply: le_measure; rewrite ?inE //.
  by move=> xi /= hx; exact: lt_trans margin hx.
- exists 1%N => p p1.
  have [s0 s1 _] := gaussian_axis_weight_bounds (a p) p1 e0.
  split => //.
  exact: (@gaussian_axis_weight_condition p e (a p) (4%:R * D ^+ 2)
    p1 e0 e1 (mulr_ge0 (ler0n RR 4) (sqr_ge0 D))).
Qed.

Lemma gaussian_quadratic_rotation d (U S : 'M[R]_d) (v : 'cV[R]_d) :
  paper_main_quadratic_form (U^T *m S *m U) v =
  paper_main_quadratic_form S (U *m v).
Proof.
by rewrite !pm_qf_col -!mulmxA -mxdot_mulmxl.
Qed.

Lemma conditioned_fit_rotation_points n d (U : 'M[R]_d)
    (x y : paper_main_sample n d) (C : R) :
  U \is orthogonalmx ->
  (forall i : 'I_n, paper_main_point y i = U *m paper_main_point x i) ->
  universality_conditioned_fit_event n d C y ->
  universality_conditioned_fit_event n d C x.
Proof.
move=> Uo hxy [S [lm [lm0 [hlo [hhi hfit]]]]].
have [Ss Slo] := (uni_loewner_geP d lm S).1 hlo.
have [_ Shi] := (uni_loewner_leP d (C * lm) S).1 hhi.
have ST : S^T = S by apply/matrixP => i j; rewrite mxE Ss.
have QS : paper_main_symmetric (U^T *m S *m U).
  have ht : (U^T *m S *m U)^T = U^T *m S *m U.
    by rewrite !trmx_mul trmxK ST mulmxA.
  move=> i j; have h := congr1 (fun A : 'M[R]_d => A j i) ht.
  by rewrite mxE in h.
have nv (v : 'cV[R]_d) : mxdot (U *m v) (U *m v) = mxdot v v.
  exact: mxdot_orthogonalmxl Uo.
exists (U^T *m S *m U), lm; split => //; split; first last.
  split; last by move=> i; rewrite gaussian_quadratic_rotation -hxy; exact: hfit.
  apply/(uni_loewner_leP d (C * lm) _); split => // v.
  have h := Shi (U *m v); rewrite pm_sqnorm_col nv in h.
  by rewrite gaussian_quadratic_rotation pm_sqnorm_col.
apply/(uni_loewner_geP d lm _); split => // v.
have h := Slo (U *m v); rewrite pm_sqnorm_col nv in h.
by rewrite gaussian_quadratic_rotation pm_sqnorm_col.
Qed.

Lemma conditioned_fit_rotation_equiv n d (U : 'M[R]_d)
    (x y : paper_main_sample n d) (C : R) :
  U \is orthogonalmx ->
  (forall i : 'I_n, paper_main_point y i = U *m paper_main_point x i) ->
  (universality_conditioned_fit_event n d C x <->
   universality_conditioned_fit_event n d C y).
Proof.
move=> Uo hxy; split; last exact: conditioned_fit_rotation_points Uo hxy.
apply: (conditioned_fit_rotation_points (U := U^T)).
- by rewrite trmx_orthogonal.
- by move=> i; rewrite hxy mulmxA orthogonalmxT // mul1mx.
Qed.

Lemma sample_right_rotation_point n d (U : 'M[R]_d)
    (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point (sample_right_isometry U^T x) i = U *m paper_main_point x i.
Proof.
have h := congr1 trmx (sample_right_isometry_point U^T x i).
by rewrite trmxK trmx_mul !trmxK in h.
Qed.

Lemma gaussian_translation_rotation_probability n d (U : 'M[R]_d)
    (m v : 'cV[R]_d) (C : R) :
  U \is orthogonalmx -> U *m m = v ->
  gaussian_product_law (n * d)
    [set x : paper_main_sample n d |
      universality_conditioned_fit_event n d C (sample_translate m x)] =
  gaussian_product_law (n * d)
    [set x : paper_main_sample n d |
      universality_conditioned_fit_event n d C (sample_translate v x)].
Proof.
move=> Uo Um.
pose A : set (paper_main_sample n d) := [set x |
  universality_conditioned_fit_event n d C (sample_translate v x)].
have mA : measurable A.
  rewrite -[X in measurable X]setTI.
  exact: measurable_sample_translate (measurable_conditioned_fit_event _ _ _).
have UUT : (U^T)^T *m U^T = 1%:M.
  by rewrite trmxK; apply/orthogonalmxP.
rewrite -(@gaussian_flat_right_isometry_law n d d U^T A UUT mA).
congr (gaussian_product_law _ _); apply/funext => x; apply/propext.
apply: (@conditioned_fit_rotation_equiv n d U (sample_translate m x)
  (sample_translate v (sample_right_isometry U^T x)) C Uo) => i.
by rewrite !sample_translate_point sample_right_rotation_point mulmxDr Um.
Qed.

Lemma gaussian_axis_shift_dot p (a : R) :
  mxdot (gaussian_axis_shift p a) (gaussian_axis_shift p a) = a ^+ 2.
Proof.
rewrite /gaussian_axis_shift mxdot_col_mx mxdot0l addr0.
by rewrite /mxdot !big_ord1 !mxE expr2.
Qed.

Lemma gaussian_translation_axis_probability n p (m : 'cV[R]_(1 + p)) (C : R) :
  gaussian_product_law (n * (1 + p))
    [set x : paper_main_sample n (1 + p) |
      universality_conditioned_fit_event n (1 + p) C (sample_translate m x)] =
  gaussian_product_law (n * (1 + p))
    [set x : paper_main_sample n (1 + p) |
      universality_conditioned_fit_event n (1 + p) C
        (sample_translate (gaussian_axis_shift p (frobenius m)) x)].
Proof.
pose v := gaussian_axis_shift p (frobenius m).
apply: (@gaussian_translation_rotation_probability n (1 + p)
  (householder (m - v)) m v C); first exact: householder_orthogonal.
apply: householder_swap.
by rewrite /v gaussian_axis_shift_dot frobenius_sqr.
Qed.

Theorem gaussian_small_shift_exists_succ (N : nat -> nat)
    (m : forall p, 'cV[R]_(1 + p)) (alpha C : R) :
  0 < alpha -> 1 < C -> alpha < condition_alpha C ->
  universality_density_tends_to N alpha ->
  (forall e : R, 0 < e -> exists D : nat, forall p, (D <= p)%N ->
    frobenius (m p) <= e * Num.sqrt p%:R) ->
  paper_main_tends_to (fun p => gaussian_product_law (N p * (1 + p))
    [set x : paper_main_sample (N p) (1 + p) |
      universality_conditioned_fit_event (N p) (1 + p) C
        (sample_translate (m p) x)]) 1%R.
Proof.
move=> a0 C1 aC hN hm.
have ha : forall e : R, 0 < e -> exists D : nat, forall p, (D <= p)%N ->
    `|frobenius (m p)| <= e * Num.sqrt p%:R.
  move=> e e0; have [D hD] := hm e e0; exists D => p pD.
  by rewrite ger0_norm ?frobenius_ge0 //; exact: hD.
have h := gaussian_axis_small_shift_exists a0 C1 aC hN ha.
move=> eps eps0; have [D hD] := h eps eps0.
exists D => p pD.
by rewrite gaussian_translation_axis_probability; exact: hD.
Qed.

Theorem gaussian_arbitrary_shift_exists_succ (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists K : R, 0 < K /\
  forall (N : nat -> nat) (m : forall p, 'cV[R]_(1 + p)),
  universality_density_tends_to N alpha ->
  paper_main_tends_to (fun p => gaussian_product_law (N p * (1 + p))
    [set x : paper_main_sample (N p) (1 + p) |
      universality_conditioned_fit_event (N p) (1 + p)
        (K * (1 + frobenius (m p) / Num.sqrt p%:R))
        (sample_translate (m p) x)]) 1%R.
Proof.
move=> a0 a4; have [K [K0 hK]] := gaussian_axis_arbitrary_shift_exists a0 a4.
exists K; split => // N m hN.
have h := hK N (fun p => frobenius (m p)) hN.
move=> eps eps0; have [D hD] := h eps eps0.
exists D => p pD.
have hp := hD p pD; rewrite ger0_norm ?frobenius_ge0 // in hp.
by rewrite gaussian_translation_axis_probability.
Qed.

Lemma gaussian_successor_density_arithmetic (q p alpha : R) :
  1 <= p ->
  `|q / p ^+ 2 - alpha| <=
    4%:R * `|q / (p + 1) ^+ 2 - alpha| + 3%:R * `|alpha| / p.
Proof.
move=> p1.
have p0 : 0 < p := lt_le_trans ltr01 p1.
have pn : p != 0 by rewrite gt_eqF.
have pp0 : 0 < p + 1 by lra.
have ppn : p + 1 != 0 by rewrite gt_eqF.
have i0 : 0 <= p^-1 by rewrite invr_ge0 ltW.
have i1 : p^-1 <= 1 by rewrite invf_le1.
have f0 : 0 <= (1 + p^-1) ^+ 2 := sqr_ge0 _.
have f4 : (1 + p^-1) ^+ 2 <= 4%:R by clear -i0 i1; nra.
have g0 : 0 <= 2 * p^-1 + p^-1 ^+ 2 by clear -i0; nra.
have g3 : 2 * p^-1 + p^-1 ^+ 2 <= 3%:R * p^-1 by clear -i0 i1; nra.
have he : q / p ^+ 2 - alpha =
    (1 + p^-1) ^+ 2 * (q / (p + 1) ^+ 2 - alpha) +
      alpha * (2 * p^-1 + p^-1 ^+ 2) by field.
rewrite he; apply: le_trans (ler_normD _ _) _.
rewrite (normrM ((1 + p^-1) ^+ 2) _) (normrM alpha _)
  (ger0_norm f0) (ger0_norm g0).
apply: le_trans (lerD (ler_wpM2r (normr_ge0 _) f4)
  (ler_wpM2l (normr_ge0 _) g3)) _.
by rewrite mulrCA mulrA.
Qed.

Lemma gaussian_density_successor (N : nat -> nat) (alpha : R) :
  universality_density_tends_to N alpha ->
  universality_density_tends_to (fun p => N (1 + p)%N) alpha.
Proof.
move=> hN eps eps0.
have e80 : 0 < eps / 8%:R by rewrite divr_gt0.
have [D hD] := hN (eps / 8%:R) e80.
pose b := 6%:R * `|alpha| / eps.
exists (maxn 1 (maxn D (archimedean.Num.truncn b).+1)) => p.
rewrite !geq_max => /andP[p1 /andP[pD pb]].
have pR : (1 : RR) <= p%:R by rewrite -[1]/(1%:R) ler_nat.
have p0 : (0 : RR) < p%:R by rewrite ltr0n.
have bp : b < p%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have h := hD (1 + p)%N (leq_trans pD (leq_addl 1 p)).
change (is_true (`|(N (1 + p))%:R / (1 + p)%:R ^+ 2 - alpha| < eps / 8%:R)) in h.
rewrite natrD /= (addrC (1 : RR) p%:R) in h.
have ha : 3%:R * `|alpha| / p%:R <= eps / 2.
  rewrite ler_pdivrMr //.
  move: bp; rewrite /b ltr_pdivrMr // => bp.
  clear -bp; nra.
apply: le_lt_trans (gaussian_successor_density_arithmetic _ _ pR) _.
clear -h ha; nra.
Qed.

Lemma gaussian_successor_sqrt p : (0 < p)%N ->
  Num.sqrt (1 + p)%:R <= 2 * Num.sqrt p%:R :> RR.
Proof.
move=> p0.
have p1 : (1 : RR) <= p%:R by rewrite -[1]/(1%:R) ler_nat.
have pr0 : (0 : RR) <= p%:R := ler0n _ _.
have sr0 : (0 : RR) <= Num.sqrt p%:R := sqrtr_ge0 _.
have sr2 : Num.sqrt p%:R ^+ 2 = p%:R :> RR by rewrite sqr_sqrtr.
have sp0 : (0 : RR) <= Num.sqrt (1 + p)%:R := sqrtr_ge0 _.
have sp2 : Num.sqrt (1 + p)%:R ^+ 2 = 1 + p%:R :> RR.
  by rewrite sqr_sqrtr ?ler0n // natrD.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?sqrtr_ge0 // exprMn sr2 sp2.
clear -p1; move: p1.
set t := (p%:R : RR); clearbody t; clear p; move=> t1; nra.
Qed.

Lemma gaussian_small_shift_successor (m : forall d, 'cV[R]_d) :
  (forall e : R, 0 < e -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= e * Num.sqrt d%:R) ->
  forall e : R, 0 < e -> exists D : nat, forall p, (D <= p)%N ->
    frobenius (m (1 + p)%N) <= e * Num.sqrt p%:R.
Proof.
move=> hm e e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have [D hD] := hm (e / 2) e20.
exists (maxn 1 D) => p; rewrite geq_max => /andP[p0 pD].
apply: le_trans (hD (1 + p)%N (leq_trans pD (leq_addl 1 p))) _.
apply: le_trans (ler_wpM2l (ltW e20) (gaussian_successor_sqrt p0)) _.
have -> : e / 2 * (2 * Num.sqrt p%:R) = e * Num.sqrt p%:R by field.
exact: lexx.
Qed.

Theorem gaussian_small_shift_exists (N : nat -> nat)
    (m : forall d, 'cV[R]_d) (alpha C : R) :
  0 < alpha -> 1 < C -> alpha < condition_alpha C ->
  universality_density_tends_to N alpha ->
  (forall e : R, 0 < e -> exists D : nat, forall d, (D <= d)%N ->
    frobenius (m d) <= e * Num.sqrt d%:R) ->
  paper_main_tends_to (fun d => gaussian_product_law (N d * d)
    [set x : paper_main_sample (N d) d |
      universality_conditioned_fit_event (N d) d C
        (sample_translate (m d) x)]) 1%R.
Proof.
move=> a0 C1 aC hN hm.
have hs := gaussian_small_shift_exists_succ a0 C1 aC
  (gaussian_density_successor hN) (gaussian_small_shift_successor hm).
move=> eps eps0; have [D hD] := hs eps eps0.
exists D.+1 => d; case: d => [|p] //= pD.
exact: hD p pD.
Qed.

Lemma gaussian_probability_superset_close dT (T : measurableType dT)
    (P : probability T RR) (A B : set T) (z : R) :
  measurable A -> measurable B -> A `<=` B ->
  (`|P A - 1%:E| < z%:E)%E -> (`|P B - 1%:E| <= z%:E)%E.
Proof.
move=> mA mB AB hA.
apply: (prob_close_one _ _ P B (~` A) z mB (measurableC mA)).
- by move=> x hx ha; apply: hx; exact: AB.
- exact: gaussian_complement_probability mA hA.
Qed.

Lemma gaussian_successor_condition_bound p (K q : R) :
  (0 < p)%N -> 0 <= K -> 0 <= q ->
  K * (1 + q / Num.sqrt p%:R) <=
    (2 * K) * (1 + q / Num.sqrt (1 + p)%:R).
Proof.
move=> p0 K0 q0.
have r0 : (0 : RR) < Num.sqrt p%:R by rewrite sqrtr_gt0 ltr0n.
have t0 : (0 : RR) < Num.sqrt (1 + p)%:R by rewrite sqrtr_gt0 ltr0n add1n.
have tr := gaussian_successor_sqrt p0.
have hr : q / Num.sqrt p%:R <= 2 * (q / Num.sqrt (1 + p)%:R).
  rewrite ler_pdivrMr //.
  have -> : 2 * (q / Num.sqrt (1 + p)%:R) * Num.sqrt p%:R =
      (2 * q * Num.sqrt p%:R) / Num.sqrt (1 + p)%:R by ring.
  rewrite ler_pdivlMr //.
  move: tr; set r := Num.sqrt p%:R; set t := Num.sqrt (1 + p)%:R.
  clearbody r t; clear -q0; move=> tr; nra.
have he : (2 * K) * (1 + q / Num.sqrt (1 + p)%:R) =
    K * (2 * (1 + q / Num.sqrt (1 + p)%:R)) by ring.
rewrite he.
have hh : 1 + q / Num.sqrt p%:R <=
    2 * (1 + q / Num.sqrt (1 + p)%:R).
  clear -hr; lra.
exact: (@ler_wpM2l RR K K0 _ _ hh).
Qed.

Theorem gaussian_arbitrary_shift_exists (alpha : R) :
  0 < alpha -> alpha < 4%:R^-1 ->
  exists K : R, 0 < K /\
  forall (N : nat -> nat) (m : forall d, 'cV[R]_d),
  universality_density_tends_to N alpha ->
  paper_main_tends_to (fun d => gaussian_product_law (N d * d)
    [set x : paper_main_sample (N d) d |
      universality_conditioned_fit_event (N d) d
        (K * (1 + frobenius (m d) / Num.sqrt d%:R))
        (sample_translate (m d) x)]) 1%R.
Proof.
move=> a0 a4.
have [K [K0 hK]] := gaussian_arbitrary_shift_exists_succ a0 a4.
exists (2 * K); split; first by rewrite mulr_gt0.
move=> N m hN.
have hs := hK (fun p => N (1 + p)%N) (fun p => m (1 + p)%N)
  (gaussian_density_successor hN).
move=> eps eps0.
have e20 : 0 < eps / 2 by rewrite divr_gt0.
have [D hD] := hs (eps / 2) e20.
exists (maxn 1 D).+1 => d; case: d => [|p] //.
rewrite ltnS geq_max => /andP[p0 pD].
pose A : set (paper_main_sample (N p.+1) p.+1) := [set x |
  universality_conditioned_fit_event (N p.+1) p.+1
    (K * (1 + frobenius (m p.+1) / Num.sqrt p%:R))
    (sample_translate (m p.+1) x)].
pose B : set (paper_main_sample (N p.+1) p.+1) := [set x |
  universality_conditioned_fit_event (N p.+1) p.+1
    ((2 * K) * (1 + frobenius (m p.+1) / Num.sqrt p.+1%:R))
    (sample_translate (m p.+1) x)].
have mA : measurable A.
  rewrite -[X in measurable X]setTI.
  exact: measurable_sample_translate (measurable_conditioned_fit_event _ _ _).
have mB : measurable B.
  rewrite -[X in measurable X]setTI.
  exact: measurable_sample_translate (measurable_conditioned_fit_event _ _ _).
have AB : A `<=` B.
  move=> x hx.
  apply: (conditioned_fit_mono _ _ _ _ _ _ hx).
  exact: gaussian_successor_condition_bound p0 (ltW K0) (frobenius_ge0 _).
have h := @gaussian_probability_superset_close _ _
  (gaussian_product_law (N p.+1 * p.+1)) A B (eps / 2) mA mB AB (hD p pD).
apply: le_lt_trans h _.
rewrite lte_fin; clear -eps0.
change (is_true (eps / (2 : RR) < eps)); lra.
Qed.
