(* The continuous latent mixture (18), at Stdlib's R: item R3 of phase 9
   (notes/phase6-three-extensions.md, section 3.3;
   notes/optional-items-plan.md, item R3; lane A). The module is not named
   ContinuousLatent, so that the short name of the frozen statement file
   stays unambiguous; it is required as
   From EllipsoidUniversality.Countable Require Import Continuous.

   Proved here: continuous_latent_holds : continuous_latent_statement.
   1. cl_component: for a in [1, 2] the two-point component has mass 1, mean
      0, variance 1 and fourth moment a^2 - 1 + a^-2, by field on the
      explicit sums cl_moment, and its values a and -1/a are at most 2 in
      absolute value.
   2. cl_fourth_integral, over a generic real type: the integral of
      a^2 - 1 + a^-2 over [1, 2] is 11/6, by continuous_FTC2 with the
      antiderivative a^3 / 3 - a - 1/a.
   3. For d >= 2 (written d'.+2): cl_point_law has mass 1
      (cl_point_law_setT) and total variation distance 1 from the point law
      of every countable mixture of product laws (cl_tv). The integrand of
      cl_point_law is rewritten on [1, 2] with the coordinate values of
      max a 1 (cl_val, cl_int, cl_point_lawE), which are continuous in a,
      hence measurable (measurable_cl_int); it lies in [0, 1], so
      cl_point_law is in [0, 1] on measurable sets (cl_point_law_bounds).
      The first two coordinates x, y of a point of (18) satisfy
      cl_pair x y: y = x or y x = -1, a relation with at most two points in
      every section (cl_pair_countable, cl_pair_countable_inv). By
      sections_charge_countable of library/probability/atoms.v, the first
      coordinates x above which some component mu s 1 charges the section
      form a countable set cl_null. The singular set cl_set (first
      coordinate off cl_null, first two coordinates related) is measurable
      (measurable_cl_set); every product law gives it mass 0, by Fubini on
      the first two coordinates (cl_set_component, with
      ge0_integral_tuple_prodS twice), hence so does the countable mixture
      (cl_set_family); and cl_point_law gives it mass 1, since the values a
      and -1/a of the first coordinate avoid cl_null for all a off a
      countable, Lebesgue-null set (cl_set_point_law, by ae_eq_integral and
      countable_lebesgue_measure0). With both laws in [0, 1], the total
      variation distance is 1. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finmap.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import Rstruct interval topology Rstruct_topology.
From mathcomp Require Import normedtype sequences esum ereal measure.
From mathcomp Require Import lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability derive realfun ftc.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import mixture tuple_rows atoms.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions ContinuousLatent.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).
Local Notation RT := (measurableTypeR R).

(* 1. The component law of a. *)

Lemma cl_weight_sum (a : R) : cl_weight a true + cl_weight a false = 1.
Proof.
have h : 1 + a ^+ 2 != 0 by rewrite gt_eqF // ltr_pwDl // sqr_ge0.
by rewrite /cl_weight /=; field.
Qed.

Lemma cl_weight_ge0 (a : R) (b : bool) : 0 <= cl_weight a b.
Proof.
have h : 0 < 1 + a ^+ 2 by rewrite ltr_pwDl // sqr_ge0.
by rewrite /cl_weight; case: b; rewrite ?invr_ge0 ?divr_ge0 ?sqr_ge0 // ltW.
Qed.

Lemma cl_component (a : R) : 1 <= a <= 2%:R ->
  [/\ cl_moment a 0 = 1, cl_moment a 1 = 0, cl_moment a 2 = 1,
      cl_moment a 4 = a ^+ 2 - 1 + a ^- 2 &
      forall b : bool, `|cl_value a b| <= 2%:R].
Proof.
move=> /andP[a1 a2].
have a0 : a != 0 by rewrite gt_eqF // (lt_le_trans ltr01 a1).
have h : 1 + a ^+ 2 != 0 by rewrite gt_eqF // ltr_pwDl // sqr_ge0.
rewrite /cl_moment !big_bool /cl_weight /cl_value /=.
split; [by field | by field | by field | by field |].
case => /=; first by rewrite ger0_norm // (le_trans ler01 a1).
rewrite normrN normfV ger0_norm ?(le_trans ler01 a1) //.
apply: le_trans (_ : 1 <= _); last by rewrite ler1n.
by rewrite invr_le1 // (lt_le_trans ltr01 a1).
Qed.

(* 2. The average fourth moment, over a generic real type. *)
Section cl_fourth.
Context {R' : realType}.
Local Notation mu := (@lebesgue_measure R').

Lemma cl_fourth_integral :
  \int[mu]_(a in `[1, 2%:R]) (a ^+ 2 - 1 + a ^- 2) = 11%:R / 6%:R :> R'.
Proof.
pose F (y : R') := 3%:R^-1 * y ^+ 3 - y - y^-1.
pose f (y : R') := y ^+ 2 - 1 + y ^- 2.
have dF (y : R') : y != 0 -> is_derive y (1 : R') F (f y).
  move=> y0.
  have h3 : is_derive y (1 : R') (fun z : R' => z ^+ 3) (3%:R * y ^+ 2).
    have h := is_deriveX 3 (is_derive_id y (1 : R')).
    apply: (is_derive_eq h).
    by rewrite /GRing.scale /= mulr1.
  have hZ := is_deriveZ (3%:R^-1) h3.
  have hB := is_deriveB hZ (is_derive_id y (1 : R')).
  have hV := is_deriveV y0 (is_derive_id y (1 : R')).
  apply: (is_derive_eq (is_deriveB hB hV)).
  by rewrite /f /GRing.scale /= mulr1; field.
have cF (y : R') : y != 0 -> {for y, continuous F}.
  move=> y0; apply: differentiable_continuous.
  by apply/derivable1_diffP; case: (dF y y0) => h _; exact: h.
have cf (y : R') : y != 0 -> {for y, continuous f}.
  move=> y0; apply: differentiable_continuous; apply/derivable1_diffP.
  apply: derivableD; first exact: derivableB.
  by apply: derivableV; rewrite ?expf_neq0.
have pos (y : R') : y \in `]1, 2%:R[%R -> y != 0.
  by rewrite in_itv /= => /andP[y1 _]; rewrite gt_eqF // (lt_trans ltr01 y1).
have n1 : (1 : R') != 0 by rewrite oner_eq0.
have n2 : (2%:R : R') != 0 by rewrite pnatr_eq0.
rewrite /Rintegral (@continuous_FTC2 _ _ F).
- by rewrite ltr1n.
- apply: continuous_in_subspaceT => y; rewrite inE /= in_itv /= => /andP[y1 _].
  by apply: cf; rewrite gt_eqF // (lt_le_trans ltr01 y1).
- split.
  + by move=> y y12; case: (dF y (pos y y12)) => h _; exact: h.
  + by apply: cvg_at_right_filter; exact: cF.
  + by apply: cvg_at_left_filter; exact: cF.
- move=> y y12.
  by rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF y (pos y y12))).
- by rewrite /= /F; field.
Qed.

(* The weights and the coordinate values of max a 1 are continuous in a. *)
Lemma cl_weight_continuous (b : bool) :
  continuous (fun a : R' => if b then (1 + a ^+ 2)^-1 else a ^+ 2 / (1 + a ^+ 2)).
Proof.
move=> x; have hx : 1 + x ^+ 2 != 0 by rewrite gt_eqF // ltr_pwDl // sqr_ge0.
apply: differentiable_continuous; apply/derivable1_diffP.
have h1 : derivable (fun a : R' => 1 + a ^+ 2) x 1.
  by apply: derivableD; [exact: derivable_cst | exact: exprn_derivable].
case: b.
- exact: derivableV.
- by apply: derivableM; [exact: exprn_derivable | exact: derivableV].
Qed.

Lemma cl_val_continuous (b : bool) :
  continuous (fun a : R' => if b then Num.max a 1 else - (Num.max a 1)^-1).
Proof.
move=> x.
have cm : {for x, continuous (fun a : R' => Num.max a 1)}.
  by apply: continuous_max; [exact: cvg_id | exact: cvg_cst].
case: b => //.
apply: (@continuousN _ _ _ (fun a : R' => (maxr a 1)^-1)).
apply: continuousV => //.
by rewrite gt_eqF // (lt_le_trans ltr01) // le_max lexx orbT.
Qed.

End cl_fourth.

(* 3. The point law of (18), read with the coordinate values of
   max a 1, which agree with those of a on [1, 2] and are continuous in a. *)

Definition cl_val (a : R) (b : bool) : R := cl_value (Num.max a 1) b.

Definition cl_pt (d : nat) (a : R) (v : d.-tuple bool) : d.-tuple RT :=
  [tuple (cl_val a (tnth v j) : RT) | j < d].

Definition cl_int (d : nat) (A : set (d.-tuple RT)) (a : RT) : \bar R :=
  (\sum_(v : d.-tuple bool)
     (\prod_(j < d) cl_weight a (tnth v j))%:E * (\1_A (cl_pt d a v))%:E)%E.

Lemma cl_point_lawE d (A : set (d.-tuple RT)) :
  cl_point_law d A =
  (\int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R]) cl_int d A a)%E.
Proof.
rewrite /cl_point_law; apply: eq_integral => a.
rewrite inE /= in_itv /= => /andP[a1 _].
apply: eq_bigr => v _; congr (_ * (\1_A _)%:E)%E.
by apply: eq_from_tnth => j; rewrite !tnth_mktuple /cl_val max_l.
Qed.

Lemma cl_weight_prod_sum d (a : R) :
  \sum_(v : d.-tuple bool) \prod_(j < d) cl_weight a (tnth v j) = 1.
Proof.
rewrite (big_tuple_distr (fun (j : 'I_d) b => cl_weight a b)).
by rewrite big1 // => j _; rewrite big_bool /= cl_weight_sum.
Qed.

Lemma measurable_cl_int d (A : set (d.-tuple RT)) : measurable A ->
  measurable_fun [set: RT] (cl_int d A).
Proof.
move=> mA.
have mw (b : bool) : measurable_fun [set: RT] (fun a : RT => cl_weight a b : RR).
  exact: continuous_measurable_fun (@cl_weight_continuous RR b).
have mv (b : bool) : measurable_fun [set: RT] (fun a : RT => (cl_val a b : RT)).
  exact: continuous_measurable_fun (@cl_val_continuous RR b).
rewrite /cl_int; apply: emeasurable_sum => v.
apply: emeasurable_funM.
  apply/measurable_EFinP.
  by apply: measurable_prod => j _; exact: mw.
apply/measurable_EFinP.
apply: measurableT_comp (measurable_indic mA) _.
apply/measurable_fun_tnthP => j.
apply: (eq_measurable_fun (fun a : RT => (cl_val a (tnth v j) : RT))).
  by move=> a _; rewrite /= /cl_pt tnth_mktuple.
exact: mv.
Qed.

Lemma cl_int_ge0 d (A : set (d.-tuple RT)) a : (0 <= cl_int d A a)%E.
Proof.
apply: sume_ge0 => v _; apply: mule_ge0; rewrite lee_fin.
  by apply: prodr_ge0 => j _; exact: cl_weight_ge0.
by rewrite indicE ler0n.
Qed.

Lemma cl_int_le1 d (A : set (d.-tuple RT)) a : (cl_int d A a <= 1)%E.
Proof.
rewrite -(cl_weight_prod_sum d a) -sumEFin; apply: lee_sum => v _.
rewrite -[X in (_ <= X)%E]mule1; apply: lee_wpmul2l.
  by rewrite lee_fin; apply: prodr_ge0 => j _; exact: cl_weight_ge0.
by rewrite lee_fin indicE; case: (_ \in _).
Qed.

(* If every point of a lies in A, the integrand is 1. *)
Lemma cl_int1 d (A : set (d.-tuple RT)) a :
  (forall v, A (cl_pt d a v)) -> cl_int d A a = 1%E.
Proof.
move=> hA.
transitivity ((\sum_(v : d.-tuple bool) \prod_(j < d) cl_weight a (tnth v j))%:E);
  last by rewrite cl_weight_prod_sum.
rewrite /cl_int -sumEFin; apply: eq_bigr => v _.
by rewrite indicE mem_set ?mule1.
Qed.

Lemma cl_int_cst1 :
  (\int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R]) (1 : \bar R))%E = 1%E.
Proof.
rewrite (@integral_cst _ _ _ (@lebesgue_measure R) `[1%R, 2%:R%R]
  (measurable_itv _) 1%E) mul1e.
have := @lebesgue_measure_itv RR (Interval (BLeft 1%R) (BRight 2%:R)).
rewrite /= lte_fin ltr1n => ->.
by rewrite -EFinD (natrD _ 1 1) addrK.
Qed.

Lemma cl_point_law_setT d : cl_point_law d setT = 1%E.
Proof.
rewrite cl_point_lawE -cl_int_cst1; apply: eq_integral => a _.
exact: cl_int1.
Qed.

Lemma cl_point_law_bounds d (A : set (d.-tuple RT)) : measurable A ->
  (0 <= cl_point_law d A <= 1)%E.
Proof.
move=> mA; rewrite cl_point_lawE; apply/andP; split.
  by apply: integral_ge0 => a _; exact: cl_int_ge0.
rewrite -cl_int_cst1; apply: ge0_le_integral => //.
- by move=> a _; exact: cl_int_ge0.
- by apply: measurable_funTS; exact: measurable_cl_int.
- by move=> a _; exact: cl_int_le1.
Qed.

(* 4. The singular set. Two coordinates x, y of a point of (18) satisfy
   y = x or y x = -1; the sections of this relation have at most two points
   in each direction. *)

Definition cl_pair (x y : R) : Prop := y = x \/ y * x = -1.

Lemma cl_pair_countable (x : R) : countable [set y : RT | cl_pair x y].
Proof.
apply: (sub_countable (B := [set x] `|` [set - x^-1])).
  apply: subset_card_le => y [->|h]; [by left | right].
  have x0 : x != 0.
    apply/eqP => x0; move: h; rewrite x0 mulr0 => /eqP.
    by rewrite eq_sym oppr_eq0 oner_eq0.
  by rewrite /= -[y](mulfK x0) h mulN1r.
by apply: finite_set_countable; rewrite finite_setU; split; exact: finite_set1.
Qed.

Lemma cl_pair_countable_inv (y : R) : countable [set x : RT | cl_pair x y].
Proof.
apply: (sub_countable (B := [set y] `|` [set - y^-1])).
  apply: subset_card_le => x [h|h]; [by left | right].
  have y0 : y != 0.
    apply/eqP => y0; move: h; rewrite y0 mul0r => /eqP.
    by rewrite eq_sym oppr_eq0 oner_eq0.
  by rewrite /= -[x](mulKf y0) h mulrN1.
by apply: finite_set_countable; rewrite finite_setU; split; exact: finite_set1.
Qed.

Lemma measurable_cl_pair (x : R) : measurable [set y : RT | cl_pair x y].
Proof.
by apply: countable_measurable; [exact: measurable_set1 | exact: cl_pair_countable].
Qed.

Section singular.
Variables (d' : nat) (w : nat -> R).
Variable mu : nat -> nat -> probability RT R.
Hypotheses (w0 : forall s, 0 <= w s) (w1 : (\sum_(s <oo) (w s)%:E = 1%:E)%E).

(* The first coordinates above which some component charges the
   relation: a countable set. *)
Definition cl_null : set RT :=
  \bigcup_(s in [set: nat]) [set x : RT | mu s 1 [set y : RT | cl_pair x y] != 0%E].

Lemma cl_null_countable : countable cl_null.
Proof.
have m1 : forall x : RT, measurable [set x] := @measurable_set1 R.
apply: bigcup_countable => [|s _]; first exact: countableP.
apply: (sections_charge_countable m1 (mu s 1)).
- exact: cl_pair_countable.
- exact: cl_pair_countable_inv.
Qed.

(* The singular set of points: the first coordinate is off cl_null and the
   first two coordinates are related. *)
Definition cl_set : set (d'.+2.-tuple RT) :=
  [set p | ~ cl_null (tnth p ord0) /\ cl_pair (tnth p ord0) (tnth p (lift ord0 ord0))].

Lemma measurable_cl_set : measurable cl_set.
Proof.
have m1 : forall x : RT, measurable [set x] := @measurable_set1 R.
have mN : measurable cl_null := countable_measurable m1 cl_null_countable.
have mt (i : 'I_d'.+2) :
    measurable_fun setT (fun p : d'.+2.-tuple RT => (tnth p i : RR)) :=
  measurable_tnth i.
pose x0 (p : d'.+2.-tuple RT) := tnth p ord0.
pose x1 (p : d'.+2.-tuple RT) := tnth p (lift ord0 ord0).
have -> : cl_set = x0 @^-1` (~` cl_null) `&`
    ((fun p => (x1 p : RR) - x0 p) @^-1` [set 0] `|`
     (fun p => (x1 p : RR) * x0 p) @^-1` [set -1]).
  apply/seteqP; split => p /= [h1 h2]; split => //.
  - by rewrite /x0 /x1; case: h2 => [->|h]; [left; rewrite subrr | right].
  - move: h2; rewrite /x0 /x1 => -[/eqP|h]; last by right.
    by rewrite subr_eq0 => /eqP; left.
have mB : measurable_fun setT (fun p : d'.+2.-tuple RT => (x1 p : RR) - x0 p) :=
  measurable_funB (mt _) (mt _).
have mM : measurable_fun setT (fun p : d'.+2.-tuple RT => (x1 p : RR) * x0 p) :=
  measurable_funM (mt _) (mt _).
apply: measurableI.
  rewrite -[X in measurable X]setTI; apply: (measurable_tnth ord0) => //.
  exact: measurableC.
apply: measurableU; rewrite -[X in measurable X]setTI.
  exact: mB measurableT _ (measurable_set1 _).
exact: mM measurableT _ (measurable_set1 _).
Qed.

Lemma cl_set_component s : tuple_prod (mu s) d'.+2 cl_set = 0%E.
Proof.
have mB := measurable_cl_set.
transitivity (\int[tuple_prod (mu s) d'.+2]_x (\1_cl_set x)%:E)%E.
  rewrite integral_indic; [exact: measurableT | exact: mB |].
  by rewrite setIT.
rewrite ge0_integral_tuple_prodS.
- by apply/measurable_EFinP; exact: measurable_indic.
- by move=> x; rewrite lee_fin indicE ler0n.
apply: integral0_eq => t _.
have [Nt|Nt] := pselect (cl_null t).
  apply: integral0_eq => ts _; rewrite indicE memNset //.
  by move=> [h _]; apply: h.
have h0 : mu s 1 [set y : RT | cl_pair t y] = 0%E.
  apply/eqP; apply: contrapT => h; apply: Nt; exists s => //; exact/negP.
have mS : measurable [set y : RT | cl_pair t y] := measurable_cl_pair t.
transitivity (\int[tuple_prod (fun i => mu s i.+1) d'.+1]_ts
    (\1_[set y : RT | cl_pair t y] (tnth ts ord0))%:E)%E.
  apply: eq_integral => ts _; rewrite !indicE.
  have -> : (tuple_cons (t, ts) \in cl_set) =
      (tnth ts ord0 \in [set y : RT | cl_pair t y]).
    apply/idP/idP => /set_mem h; apply/mem_set.
      by case: h => _; rewrite /tuple_cons tnthS.
    by split => //; rewrite /tuple_cons tnthS.
  by [].
rewrite ge0_integral_tuple_prodS.
- apply/measurable_EFinP.
  exact: measurableT_comp (measurable_indic mS) (measurable_tnth ord0).
- by move=> x; rewrite lee_fin indicE ler0n.
transitivity (\int[mu s 1]_u (\1_[set y : RT | cl_pair t y] u)%:E)%E.
  apply: eq_integral => u _ /=.
  rewrite (@integral_cst _ _ _ (tuple_prod (fun i => mu s i.+2) d') setT
    measurableT ((\1_[set y : RT | cl_pair t y] u)%:E)).
  by rewrite -[X in _ = X]mule1; congr (_ * _)%E; exact: probability_setT.
by rewrite integral_indic //; first by rewrite setIT.
Qed.

Lemma cl_set_family : robust_point_law w mu d'.+2 cl_set = 0%E.
Proof.
rewrite /robust_point_law; apply: esum1 => s _.
by rewrite cl_set_component mule0.
Qed.

Lemma cl_set_point_law : cl_point_law d'.+2 cl_set = 1%E.
Proof.
have m1 : forall x : RT, measurable [set x] := @measurable_set1 R.
pose Z : set RT := cl_null `|` [set a : RT | cl_null (- a^-1)].
have cZ : countable Z.
  have cN := cl_null_countable.
  have cI : countable [set a : RT | cl_null (- a^-1)].
    apply: sub_countable cN.
    apply: (card_le_trans _ (card_image_le (fun x : RT => - x^-1) cl_null)).
    apply: subset_card_le => a /= Na; exists (- a^-1) => //.
    by rewrite invrN invrK opprK.
  have -> : Z = \bigcup_(b in [set: bool])
      (if b then cl_null else [set a : RT | cl_null (- a^-1)]).
    apply/seteqP; split => a.
    - by case => h; [exists true | exists false].
    - by case => -[] _ h; [left | right].
  by apply: bigcup_countable => [|[] _] //; exact: countableP.
rewrite cl_point_lawE -cl_int_cst1.
apply: ae_eq_integral.
- exact: measurable_itv.
- by apply: measurable_funTS; exact: measurable_cl_int measurable_cl_set.
- exact: measurable_cst.
exists Z; split.
- exact: countable_measurable m1 cZ.
- exact: countable_lebesgue_measure0.
move=> a /= h; apply: contrapT => hZ; apply: h => a12.
have a1 : 1 <= a by move: a12; rewrite /= in_itv /= => /andP[].
have a0 : a != 0 by rewrite gt_eqF // (lt_le_trans ltr01 a1).
have [Na Nia] : ~ cl_null a /\ ~ cl_null (- a^-1).
  by split => h; apply: hZ; [left | right].
apply: cl_int1 => v.
rewrite /cl_set /cl_pt /= !tnth_mktuple /cl_val max_l //.
rewrite /cl_pair /cl_value.
case: (tnth v ord0); case: (tnth v (lift ord0 ord0)); split => //.
- by left.
- by right; rewrite mulNr mulVf.
- by right; rewrite mulrN mulfV.
- by left.
Qed.

Lemma robust_point_law_bounds (A : set (d'.+2.-tuple RT)) : measurable A ->
  (0 <= robust_point_law w mu d'.+2 A <= 1)%E.
Proof.
move=> mA; rewrite /robust_point_law; apply/andP; split.
  by apply: esum_ge0 => s _; rewrite mule_ge0 // lee_fin.
apply: le_trans (_ : \esum_(s in [set: nat]) (w s)%:E <= _)%E.
  apply: le_esum => s _.
  rewrite -[X in (_ <= X)%E]mule1; apply: lee_wpmul2l; first by rewrite lee_fin.
  exact: probability_le1.
have -> : [set: nat] = [set x | xpredT x] by apply/seteqP; split.
by rewrite -nneseries_esum ?w1 // => s _; rewrite lee_fin.
Qed.

Lemma cl_tv :
  robust_tv d'.+2 (cl_point_law d'.+2) (robust_point_law w mu d'.+2) = 1%E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => _ [A mA <-].
  have /andP[p0 p1] := cl_point_law_bounds _ _ mA.
  have /andP[q0 q1] := robust_point_law_bounds _ mA.
  have fp : cl_point_law d'.+2 A \is a fin_num.
    by rewrite ge0_fin_numE // (le_lt_trans p1) ?ltry.
  have fq : robust_point_law w mu d'.+2 A \is a fin_num.
    by rewrite ge0_fin_numE // (le_lt_trans q1) ?ltry.
  move: p0 p1 q0 q1; rewrite -(fineK fp) -(fineK fq) -EFinB abse_EFin !lee_fin.
  move: (fine _) (fine _) => x y x0 x1 y0 y1.
  by rewrite ler_norml; apply/andP; split; lra.
apply: ereal_sup_ubound; exists cl_set; first exact: measurable_cl_set.
by rewrite cl_set_point_law cl_set_family sube0 abse1.
Qed.

End singular.

(* 5. The statement. *)
Theorem continuous_latent_holds : continuous_latent_statement.
Proof.
split.
- exact: cl_component.
- exact: cl_fourth_integral.
- case=> [|[|d']] // _; split; first exact: cl_point_law_setT.
  by move=> w mu w0 w1; exact: cl_tv.
Qed.
