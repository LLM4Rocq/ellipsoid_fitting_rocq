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
      variation distance is 1.
   6. The law (18) as a probability (phase 10, item I2). cl_law d is a copy
      of cl_point_law d with the structure of a probability on
      d.-tuple (measurableTypeR R), equal to it on every set (cl_lawE). Its
      sigma-additivity comes from that of the integrand, a finite sum of
      weighted Dirac masses at the points of (18), through
      integral_nneseries. integral_cl_law: the integral of a nonnegative
      measurable f against cl_law d is the integral over a in [1, 2] of the
      sum over the sign patterns v of the weights times f at the point (by
      simple functions and monotone convergence, as integral_kcomp of
      kernel.v). integral_cl_law_coord: for a function of the coordinate j
      the sum over v reduces to the two values of that coordinate.
      cl_law_mean, cl_law_second_moment, cl_law_fourth_moment: every
      coordinate has mean 0, second moment 1 and fourth moment 11/6. *)

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
Import HBNNSimple.

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

Lemma cl_fourth_integralE :
  (\int[mu]_(a in `[1%R, 2%:R%R]) ((a : R') ^+ 2 - 1 + (a : R') ^- 2)%:E)%E =
  (11%:R / 6%:R : R')%:E.
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
rewrite (@continuous_FTC2 _ _ F).
- by rewrite ltr1n.
- apply: continuous_in_subspaceT => y; rewrite inE /= in_itv /= => /andP[y1 _].
  by apply: cf; rewrite gt_eqF // (lt_le_trans ltr01 y1).
- split.
  + by move=> y y12; case: (dF y (pos y y12)) => h _; exact: h.
  + by apply: cvg_at_right_filter; exact: cF.
  + by apply: cvg_at_left_filter; exact: cF.
- move=> y y12.
  by rewrite derive1E (@derive_val _ _ _ _ _ _ _ (dF y (pos y y12))).
- by rewrite -EFinB /F; congr EFin; field.
Qed.

Lemma cl_fourth_integral :
  \int[mu]_(a in `[1, 2%:R]) (a ^+ 2 - 1 + a ^- 2) = 11%:R / 6%:R :> R'.
Proof. by rewrite /Rintegral cl_fourth_integralE. Qed.

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

(* 6. The law (18) as a probability, with the moments of its coordinates
   (phase 10, item I2). *)

Lemma measurable_cl_pt d (v : d.-tuple bool) :
  measurable_fun [set: RT] (fun a : RT => cl_pt d a v).
Proof.
apply/measurable_fun_tnthP => j.
apply: (eq_measurable_fun (fun a : RT => (cl_val a (tnth v j) : RT))).
  by move=> a _; rewrite /= /cl_pt tnth_mktuple.
exact: continuous_measurable_fun (@cl_val_continuous RR (tnth v j)).
Qed.

Section cl_law.
Variable d : nat.

(* A copy of cl_point_law d that carries the structure of a probability. *)
Definition cl_law : set (d.-tuple RT) -> \bar R := cl_point_law d.

Lemma cl_lawE (A : set (d.-tuple RT)) : cl_law A = cl_point_law d A.
Proof. by []. Qed.

Lemma cl_law0 : cl_law set0 = 0%E.
Proof.
rewrite cl_lawE cl_point_lawE; apply: integral0_eq => a _.
by rewrite /cl_int big1 // => v _; rewrite indicE in_set0 mule0.
Qed.

Lemma cl_law_ge0 (A : set (d.-tuple RT)) : (0 <= cl_law A)%E.
Proof.
by rewrite cl_lawE cl_point_lawE; apply: integral_ge0 => a _; exact: cl_int_ge0.
Qed.

Lemma cl_law_sigma_additive : semi_sigma_additive cl_law.
Proof.
move=> F mF tF mUF.
have hI (x : d.-tuple RT) :
    (((\1_(\bigcup_k F k) x : R))%:E = \sum_(k <oo) ((\1_(F k) x : R))%:E)%E.
  transitivity (\d_x (\bigcup_k F k) : \bar R); first by rewrite diracE indicE.
  rewrite (@measure_bigcup _ _ _ (@dirac _ _ x R) [set: nat] F
    (fun i _ => mF i) tF).
  rewrite (eq_eseriesl (P := fun i => i \in [set: nat]) (Q := xpredT)).
    by move=> i; rewrite in_setT.
  by apply: eq_eseriesr => k _; rewrite indicE; exact: diracE.
have hU : cl_law (\bigcup_k F k) = (\sum_(k <oo) cl_law (F k))%E.
  rewrite cl_lawE cl_point_lawE.
  transitivity (\sum_(k <oo) \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
      cl_int d (F k) a)%E; last first.
    by apply: eq_eseriesr => k _; rewrite cl_lawE cl_point_lawE.
  rewrite -integral_nneseries //.
  - by move=> k; apply: measurable_funTS; exact: measurable_cl_int.
  - by move=> k a _; exact: cl_int_ge0.
  - apply: eq_integral => a _.
    rewrite /cl_int nneseries_sum.
      move=> v k _; apply: mule_ge0; rewrite lee_fin ?indicE ?ler0n //.
      by apply: prodr_ge0 => j _; exact: cl_weight_ge0.
    apply: eq_bigr => v _.
    rewrite nneseriesZl; first by move=> k _; rewrite lee_fin indicE ler0n.
    by rewrite hI.
rewrite [X in _ --> X]hU.
apply/cvg_closeP; split; last by rewrite closeE.
by apply: is_cvg_nneseries => k _; rewrite cl_law_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ cl_law
  cl_law0 cl_law_ge0 cl_law_sigma_additive.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R cl_law (cl_point_law_setT d).

End cl_law.

(* The integral of a nonnegative measurable function of a point of (18). *)
Lemma integral_cl_law d (f : d.-tuple RT -> \bar R) :
  (forall x, 0 <= f x)%E -> measurable_fun [set: d.-tuple RT] f ->
  (\int[cl_law d]_x f x =
   \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
     \sum_(v : d.-tuple bool)
       (\prod_(j < d) cl_weight a (tnth v j))%:E * f (cl_pt d a v))%E.
Proof.
move=> f0 mf.
pose W (a : R) (v : d.-tuple bool) : R := \prod_(j < d) cl_weight a (tnth v j).
have W0 a v : (0 <= W a v)%R by apply: prodr_ge0 => j _; exact: cl_weight_ge0.
have mW v : measurable_fun [set: RT] (fun a : RT => (W a v : RR)).
  apply: measurable_prod => j _.
  exact: continuous_measurable_fun (@cl_weight_continuous RR (tnth v j)).
have mG (g : d.-tuple RT -> \bar R) : measurable_fun [set: d.-tuple RT] g ->
    measurable_fun [set: RT]
      (fun a : RT => (\sum_(v : d.-tuple bool) (W a v)%:E * g (cl_pt d a v))%E).
  move=> mg; apply: emeasurable_sum => v; apply: emeasurable_funM.
    exact/measurable_EFinP.
  exact: measurableT_comp mg (measurable_cl_pt d v).
(* Nonnegative simple functions: linearity from the indicators. *)
have hS (h : {nnsfun (d.-tuple RT) >-> R}) :
    (\int[cl_law d]_x (h x)%:E =
     \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
       \sum_(v : d.-tuple bool) (W a v)%:E * (h (cl_pt d a v))%:E)%E.
  have fh := @fimfunP _ _ h.
  have h0 r : r \in range h -> (0 <= r)%R.
    by move=> /set_mem [x _ <-]; exact: fun_ge0.
  rewrite integralT_nnsfun sintegralE fsbigop.fsbig_finite //.
  set S := fset_set (range h).
  have hS0 r : r \in S -> (0 <= r)%R by rewrite in_fset_set // => /h0.
  transitivity (\int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
      \sum_(r <- S) r%:E * cl_int d (h @^-1` [set r]) a)%E.
    rewrite ge0_integral_sum.
    - exact: measurable_itv.
    - move=> r; apply: measurable_funeM; apply: measurable_funTS.
      by apply: measurable_cl_int; exact: measurable_funPTI.
    - move=> r a _; have [r0|r0] := leP 0%R r.
        by rewrite mule_ge0 // ?lee_fin // cl_int_ge0.
      rewrite preimage_nnfun0 //.
      by rewrite /cl_int big1 ?mule0 // => v _; rewrite indicE in_set0 mule0.
    - rewrite big_seq [RHS]big_seq; apply: eq_bigr => r hr.
      have mhr : measurable (h @^-1` [set r]) by exact: measurable_funPTI.
      rewrite ge0_integralZl //.
      + by apply: measurable_funTS; exact: measurable_cl_int.
      + by move=> a _; exact: cl_int_ge0.
      + by rewrite lee_fin hS0.
      + by congr (_ * _)%E; exact: (cl_point_lawE d (h @^-1` [set r])).
  apply: eq_integral => a _.
  have hc r : cl_int d (h @^-1` [set r]) a =
      (\sum_v W a v * \1_(h @^-1` [set r]) (cl_pt d a v))%:E.
    by rewrite /cl_int -sumEFin; apply: eq_bigr => v _; rewrite EFinM.
  under eq_bigr do rewrite hc -EFinM.
  rewrite sumEFin.
  transitivity ((\sum_v W a v * h (cl_pt d a v))%:E); last first.
    by rewrite -sumEFin; apply: eq_bigr => v _; rewrite EFinM.
  congr EFin.
  under eq_bigr do rewrite mulr_sumr.
  rewrite exchange_big /=; apply: eq_bigr => v _.
  rewrite [in RHS]fimfunE fsbigop.fsbig_finite // mulr_sumr.
  by apply: eq_bigr => r _; rewrite mulrCA.
(* Monotone limits of simple functions. *)
pose f_ := nnsfun_approx measurableT mf.
have cf x : ((f_ n x)%:E @[n --> \oo] --> f x)%E.
  by apply: cvg_nnsfun_approx => // y _; exact: f0.
transitivity (limn (fun n => \int[cl_law d]_x (f_ n x)%:E))%E.
  rewrite -monotone_convergence //.
  - by move=> n; exact/measurable_EFinP.
  - by move=> n x _; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
  - by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: cf.
have hlim : (fun n => \int[cl_law d]_x (f_ n x)%:E)%E =
    (fun n => \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
      \sum_(v : d.-tuple bool) (W a v)%:E * (f_ n (cl_pt d a v))%:E)%E.
  by apply/funext => n; rewrite hS.
rewrite hlim -monotone_convergence //.
- move=> n; apply: measurable_funTS.
  by apply: (mG (fun y => (f_ n y)%:E)); exact/measurable_EFinP.
- by move=> n a _; apply: sume_ge0 => v _; rewrite mule_ge0 // lee_fin.
- move=> a _ m n mn; apply: lee_sum => v _.
  apply: lee_wpmul2l; first by rewrite lee_fin.
  by rewrite lee_fin; exact/lefP/nd_nnsfun_approx.
- apply: eq_integral => a _; apply/cvg_lim => //.
  apply: cvg_nnesum => [v _|v _].
    by apply: nearW => n; rewrite mule_ge0 // lee_fin.
  by apply: cvgeZl => //; exact: cf.
Qed.

(* The integral of a nonnegative function of the coordinate j. *)
Lemma integral_cl_law_coord d (j : 'I_d) (g : R -> R) :
  (forall t, 0 <= g t) -> measurable_fun [set: RT] (g : RT -> RR) ->
  (\int[cl_law d]_x (g (tnth x j))%:E =
   \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
     (\sum_(b : bool) cl_weight a b * g (cl_value a b))%:E)%E.
Proof.
move=> g0 mg.
rewrite integral_cl_law.
- by move=> x; rewrite lee_fin.
- by apply/measurable_EFinP; exact: measurableT_comp mg (measurable_tnth j).
apply: eq_integral => a; rewrite inE /= in_itv /= => /andP[a1 _].
have hv (v : d.-tuple bool) :
    ((\prod_(i < d) cl_weight a (tnth v i))%:E * (g (tnth (cl_pt d a v) j))%:E)%E =
    (\prod_(i < d) (if i == j then cl_weight a (tnth v i) * g (cl_value a (tnth v i))
                    else cl_weight a (tnth v i)))%:E.
  rewrite -EFinM /cl_pt tnth_mktuple /cl_val max_l //; congr EFin.
  rewrite [X in X * _](bigD1 j) //= [RHS](bigD1 j) //= eqxx mulrAC.
  by congr (_ * _); apply: eq_bigr => i ij; rewrite (negbTE ij).
rewrite (eq_bigr _ (fun v _ => hv v)) sumEFin; congr EFin.
rewrite (big_tuple_distr (fun i b => if i == j then cl_weight a b * g (cl_value a b)
                                      else cl_weight a b)).
rewrite (bigD1 j) //= eqxx [X in _ * X]big1 ?mulr1 // => i ij.
by rewrite (negbTE ij) big_bool /= cl_weight_sum.
Qed.

(* The coordinates have mean 0, second moment 1 and fourth moment 11/6. *)
Lemma cl_law_mean d (j : 'I_d) :
  ('E_(cl_law d)[fun x => (tnth x j : R)] = 0)%E.
Proof.
rewrite unlock integralE.
have mP : measurable_fun [set: RT] ((fun t : R => maxr t 0) : RT -> RR).
  exact: measurable_maxr.
have mN : measurable_fun [set: RT] ((fun t : R => maxr (- t) 0) : RT -> RR).
  by apply: measurable_maxr => //; exact: measurableT_comp.
(* Both parts of the coordinate integrate a / (1 + a^2) over [1, 2]. *)
have hpos : (\int[cl_law d]_x (fun x0 => (tnth x0 j : R)%:E)^\+ x =
    \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
      ((a : R) / (1 + (a : R) ^+ 2))%:E)%E.
  transitivity (\int[cl_law d]_x (maxr (tnth x j : R) 0)%:E)%E.
    by apply: eq_integral => x _; rewrite funeposE EFin_max.
  rewrite (integral_cl_law_coord _ j (fun t => maxr t 0)) //; last first.
    apply: eq_integral => a; rewrite inE /= in_itv /= => /andP[a1 _].
    have a0 : (0 < (a : R))%R by apply: lt_le_trans a1.
    congr EFin; rewrite big_bool /= /cl_weight /cl_value /=.
    have -> : maxr (a : R) 0 = a by apply/max_idPl; exact: ltW.
    have -> : maxr (- (a : R)^-1) 0 = 0.
      by apply/max_idPr; rewrite oppr_le0 invr_ge0 ltW.
    by rewrite mulr0 addr0 mulrC.
  by move=> t; rewrite le_max lexx orbT.
have hneg : (\int[cl_law d]_x (fun x0 => (tnth x0 j : R)%:E)^\- x =
    \int[@lebesgue_measure R]_(a in `[1%R, 2%:R%R])
      ((a : R) / (1 + (a : R) ^+ 2))%:E)%E.
  transitivity (\int[cl_law d]_x (maxr (- (tnth x j : R)) 0)%:E)%E.
    by apply: eq_integral => x _; rewrite funenegE -EFinN EFin_max.
  rewrite (integral_cl_law_coord _ j (fun t => maxr (- t) 0)) //; last first.
    apply: eq_integral => a; rewrite inE /= in_itv /= => /andP[a1 _].
    have a0 : (0 < (a : R))%R by apply: lt_le_trans a1.
    congr EFin; rewrite big_bool /= /cl_weight /cl_value /=.
    have -> : maxr (- (a : R)) 0 = 0 by apply/max_idPr; rewrite oppr_le0 ltW.
    have -> : maxr (- - (a : R)^-1) 0 = (a : R)^-1.
      by rewrite opprK; apply/max_idPl; rewrite invr_ge0 ltW.
    have an : (a : R) != 0 by rewrite gt_eqF.
    have hn : 1 + (a : R) ^+ 2 != 0 by rewrite gt_eqF // ltr_pwDl // sqr_ge0.
    by rewrite mulr0 add0r; field.
  by move=> t; rewrite le_max lexx orbT.
rewrite hpos hneg subee //.
(* That integral is finite: its integrand lies in [0, 1]. *)
have mw : measurable_fun [set: RT]
    (fun a : RT => ((a : R) / (1 + (a : R) ^+ 2)) : RR).
  apply: measurable_funM => //.
  exact: continuous_measurable_fun (@cl_weight_continuous RR true).
have h01 (a : R) : 1 <= a -> (0 <= a / (1 + a ^+ 2) <= 1)%R.
  move=> a1; have a0 : (0 <= a)%R by apply: le_trans a1.
  have hp : (0 < 1 + a ^+ 2)%R by rewrite ltr_pwDl // sqr_ge0.
  rewrite divr_ge0 ?(ltW hp) //= ler_pdivrMr // mul1r.
  apply: le_trans (_ : a <= a ^+ 2) _; first by rewrite expr2 ler_peMl.
  by rewrite lerDr.
rewrite ge0_fin_numE; last first.
  apply: (@le_lt_trans _ _ 1%E); last exact: ltry.
  rewrite -cl_int_cst1; apply: ge0_le_integral => //.
  - move=> a ha; have /andP[a1 _] : (1 <= (a : R) <= 2%:R)%R.
      by move: ha => /=; rewrite in_itv.
    by rewrite lee_fin; case/andP: (h01 a a1).
  - by apply/measurable_EFinP; exact: measurable_funTS.
  - move=> a ha; have /andP[a1 _] : (1 <= (a : R) <= 2%:R)%R.
      by move: ha => /=; rewrite in_itv.
    by rewrite lee_fin; case/andP: (h01 a a1).
apply: integral_ge0 => a ha.
have /andP[a1 _] : (1 <= (a : R) <= 2%:R)%R by move: ha => /=; rewrite in_itv.
by rewrite lee_fin; case/andP: (h01 a a1).
Qed.

Lemma cl_law_second_moment d (j : 'I_d) :
  ('E_(cl_law d)[fun x => ((tnth x j : R) ^+ 2)%R] = 1)%E.
Proof.
have mX k : measurable_fun [set: RT] ((fun t : R => t ^+ k) : RT -> RR).
  exact: continuous_measurable_fun (@exprn_continuous RR k).
rewrite unlock (integral_cl_law_coord _ j (fun t => t ^+ 2)) //; last first.
  rewrite -cl_int_cst1; apply: eq_integral => a; rewrite inE /= in_itv /= => ha.
  by have [_ _ h2 _ _] := cl_component a ha; rewrite -h2.
by move=> t; exact: sqr_ge0.
Qed.

Lemma cl_law_fourth_moment d (j : 'I_d) :
  ('E_(cl_law d)[fun x => ((tnth x j : R) ^+ 4)%R] =
   ((11%:R / 6%:R)%R)%:E)%E.
Proof.
have mX k : measurable_fun [set: RT] ((fun t : R => t ^+ k) : RT -> RR).
  exact: continuous_measurable_fun (@exprn_continuous RR k).
rewrite unlock (integral_cl_law_coord _ j (fun t => t ^+ 4)) //; last first.
  rewrite -(@cl_fourth_integralE RR); apply: eq_integral => a.
  rewrite inE /= in_itv /= => ha.
  by have [_ _ _ h4 _] := cl_component a ha; rewrite -h4.
by move=> t; rewrite exprn_even_ge0.
Qed.
