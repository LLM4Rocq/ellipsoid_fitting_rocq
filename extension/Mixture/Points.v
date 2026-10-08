(* Some point of the sample is not zero, with probability tending to one:
   item X7a of phase 6, at Stdlib's R, for flat families of component laws
   and for finite mixtures of product laws. The assembly of Theorem 1.2 (i)
   needs a point x_i != 0 (sample_points_zero of Sat/Universality does it
   for the coordinate laws of the paper, with the fourth moment).

   Definitions:
     coord_zero n d j0 == the samples of n points of R^d in which
                          coordinate j0 of every point is 0

   Results.
   - measurable_coord_zero, coord_zero_point: coord_zero n d j0 is
     measurable, and outside it some point is not zero.
   - component_law_zero: a component law with constant K gives {0} the
     mass at most 1 - 1 / (4 K^4) (component_law_nonzero of
     Mixture/Component).
   - flat_coord_zero, flat_points_zero: for a flat family tuple_prod lam
     (n d) of component laws with constant K, coord_zero n d j0 has
     probability at most (1 - 1 / (4 K^4))^n, since the coordinates j0 of
     the points are independent (flat_map_law of Mixture/Flat); hence, for
     d > 0, a measurable event of that probability outside which some
     point is not zero.
   - mixture_points_zero: the same for mixture_probability, with the same
     event for every tuple of labels, since the label weights have sum one
     (mixture_weights_prod of library/probability/mixture.v). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology arithmetic_tactic.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import conditioning mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Mixture Require Import Component Flat.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation RR := (R : realType).

(* The samples in which coordinate j0 of every point is 0. *)
Definition coord_zero (n d : nat) (j0 : 'I_d) : set (paper_main_sample n d) :=
  [set x | forall i : 'I_n, tnth (tnth (tuple_rows n d x) i) j0 = 0].

Section coord_zero.
Variables (n d : nat) (j0 : 'I_d).

Let g (r : d.-tuple (measurableTypeR R)) : measurableTypeR R := tnth r j0.

Let A : set (n.-tuple (measurableTypeR R)) :=
  tuple_box (fun _ : 'I_n => [set (0%R : measurableTypeR R)]).

Let coord_zeroE : coord_zero n d j0 =
  (fun x => tuple_map (fun=> g) (tuple_rows n d x)) @^-1` A.
Proof.
apply/seteqP; split => x /= h i.
  by rewrite /g tnth_map tnth_ord_tuple; exact: h.
by have := h i; rewrite /g tnth_map tnth_ord_tuple.
Qed.

Lemma measurable_coord_zero : measurable (coord_zero n d j0).
Proof.
rewrite coord_zeroE.
have mT : measurable_fun setT (fun x : paper_main_sample n d =>
    tuple_map (fun=> g) (tuple_rows n d x)).
  apply: measurableT_comp; last exact: measurable_tuple_rows.
  by apply: measurable_tuple_map => i; exact: measurable_tnth.
rewrite -[X in measurable X]setTI; apply: mT => //.
by apply: measurable_tuple_box => i.
Qed.

Lemma coord_zero_point (x : paper_main_sample n d) :
  ~ coord_zero n d j0 x -> exists i : 'I_n, paper_main_point x i != 0.
Proof.
move=> hx; apply: contrapT => hno; apply: hx => i.
have : paper_main_point x i = 0.
  by apply: contrapT => h; apply: hno; exists i; apply/eqP.
move=> /(congr1 (fun v : 'cV[R]_d => v j0 0)).
by rewrite paper_main_point_row !mxE.
Qed.

End coord_zero.

(* A component law with constant K gives {0} the mass at most
   1 - 1 / (4 K^4). *)
Lemma component_law_zero (K : R) (mu : probability (measurableTypeR R) R) :
  mixture_component_law K mu ->
  (mu [set (0%R : measurableTypeR R)] <= (1 - (4%:R * K ^+ 4)^-1)%:E)%E.
Proof.
move=> hmu; have h := component_law_nonzero K mu hmu.
pose B := [set x : measurableTypeR R | ((x : R) != 0)%R].
have mB : measurable B.
  have -> : B = ~` [set (0%R : measurableTypeR R)].
    by apply/seteqP; split => x /=; [move=> /eqP|move=> hx; apply/eqP].
  exact: measurableC.
have -> : [set (0%R : measurableTypeR R)] = ~` B.
  apply/seteqP; split => x /=; first by move=> ->; rewrite /B /= eqxx.
  by move=> hx; apply/eqP/negPn/negP.
rewrite probability_setC //.
move: h (probability_le1 mu mB); rewrite -/B.
case: (mu B) => [b| |] //= hb hb1.
by rewrite -EFinB lee_fin; move: hb; rewrite lee_fin => hb; lra.
Qed.

(* For a flat family of component laws with constant K, coordinate j0 of
   every point is 0 with probability at most (1 - 1 / (4 K^4))^n. *)
Lemma flat_coord_zero (K : R) (lam : nat -> probability (measurableTypeR R) R)
    n d (j0 : 'I_d) :
  (forall k, (k < n * d)%N -> mixture_component_law K (lam k)) ->
  (tuple_prod lam (n * d) (coord_zero n d j0) <=
   ((1 - (4%:R * K ^+ 4)^-1) ^+ n)%:E)%E.
Proof.
move=> hlam.
pose g (r : d.-tuple (measurableTypeR R)) : measurableTypeR R := tnth r j0.
have mg : measurable_fun setT g := measurable_tnth j0.
pose A : set (n.-tuple (measurableTypeR R)) :=
  tuple_box (fun _ : 'I_n => [set (0%R : measurableTypeR R)]).
have mA : measurable A by apply: measurable_tuple_box => i.
pose mu i := flat_row lam d i j0.
have hg i B : measurable B ->
    mu i B = tuple_prod (flat_row lam d i) d (g @^-1` B).
  move=> mB; rewrite /mu.
  by rewrite -(@tuple_prod_tnth _ _ (flat_row lam d i) d j0 B mB).
have -> : coord_zero n d j0 =
    (fun x => tuple_map (fun=> g) (tuple_rows n d x)) @^-1` A.
  apply/seteqP; split => x /= h i.
    by rewrite /g tnth_map tnth_ord_tuple; exact: h.
  by have := h i; rewrite /g tnth_map tnth_ord_tuple.
rewrite (flat_map_law lam n d _ _ mu g A mg hg mA) tuple_prod_box.
  by move=> i.
set q := (1 - (4%:R * K ^+ 4)^-1)%R.
have hb (i : 'I_n) : (mu i [set (0%R : measurableTypeR R)] <= q%:E)%E.
  apply: component_law_zero; rewrite /mu /flat_row; apply: hlam.
  exact: flat_index_lt.
have hb' (i : 'I_n) :
    (0 <= fine (mu i [set (0%R : measurableTypeR R)]) <= q)%R.
  have f0 : mu i [set (0%R : measurableTypeR R)] \is a fin_num.
    exact: fin_num_measure.
  apply/andP; split; first by apply: fine_ge0; exact: measure_ge0.
  by move: (hb i); rewrite -(fineK f0) lee_fin.
have -> : (\prod_(i < n) mu i [set (0%R : measurableTypeR R)] =
    (\prod_(i < n) fine (mu i [set (0%R : measurableTypeR R)]))%:E)%E.
  rewrite -prodEFin; apply: eq_bigr => i _.
  by rewrite fineK //; exact: fin_num_measure.
have -> : (q ^+ n = \prod_(i < n) q)%R by rewrite prodr_const card_ord.
by rewrite lee_fin; apply: ler_prod => i _; exact: hb'.
Qed.

(* For d > 0, some point of a sample of a flat family of component laws is
   not zero, outside a measurable event of probability at most
   (1 - 1 / (4 K^4))^n. *)
Lemma flat_points_zero (K : R) (lam : nat -> probability (measurableTypeR R) R)
    n d : (0 < d)%N ->
  (forall k, (k < n * d)%N -> mixture_component_law K (lam k)) ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (tuple_prod lam (n * d) G <= ((1 - (4%:R * K ^+ 4)^-1) ^+ n)%:E)%E &
    forall x, ~ G x -> exists i : 'I_n, paper_main_point x i != 0].
Proof.
move=> d0 hlam; pose j0 : 'I_d := Ordinal d0.
exists (coord_zero n d j0); split.
- exact: measurable_coord_zero.
- exact: flat_coord_zero.
- exact: coord_zero_point.
Qed.

(* The same for a finite mixture of product laws, whose components have
   coordinate laws of class K: the event does not depend on the labels. *)
Lemma mixture_points_zero (K : R) (N : nat) (w : nat -> R)
    (mu : nat -> nat -> probability (measurableTypeR R) R) n d :
  (0 < d)%N -> (forall s, (s < N)%N -> 0 <= w s) -> \sum_(s < N) w s = 1 ->
  (forall s j, (s < N)%N -> (j < d)%N -> mixture_component_law K (mu s j)) ->
  exists G : set (paper_main_sample n d), [/\ measurable G,
    (mixture_probability N w mu n d G <=
     ((1 - (4%:R * K ^+ 4)^-1) ^+ n)%:E)%E &
    forall x, ~ G x -> exists i : 'I_n, paper_main_point x i != 0].
Proof.
move=> d0 w0 w1 hmu; pose j0 : 'I_d := Ordinal d0.
exists (coord_zero n d j0); split.
- exact: measurable_coord_zero.
- set q := ((1 - (4%:R * K ^+ 4)^-1) ^+ n)%R.
  have hw : mixture_weights (fun t : 'I_N => w t).
    by split => [t|]; [exact: w0 (ltn_ord t)|exact: w1].
  have hp := mixture_weights_sum (mixture_weights_prod n hw).
  rewrite /mixture_probability.
  apply: (@le_trans _ _ (\sum_(s : n.-tuple 'I_N)
      (\prod_(i < n) w (tnth s i))%:E * q%:E)%E).
    apply: lee_sum => s _; apply: lee_wpmul2l.
      by rewrite lee_fin; apply: prodr_ge0 => i _; exact: w0 (ltn_ord _).
    exact: flat_coord_zero (labelled_component K N mu n d s hmu).
  under eq_bigr do rewrite -EFinM.
  by rewrite sumEFin -mulr_suml hp mul1r.
- exact: coord_zero_point.
Qed.
