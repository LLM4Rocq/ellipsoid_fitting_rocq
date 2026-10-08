(* Samples whose coordinate laws vary with the point and the coordinate, at
   Stdlib's R. A flat family is a sample law tuple_prod lam (n * d) on
   paper_main_sample n d: coordinate k, which is coordinate k mod d of point
   k / d (paper_main_point), has law lam k, and the n * d coordinates are
   independent. Given the labels of its points, a sample of a finite
   mixture of product laws has such a law (mixture_labelled_law of
   MixtureDefinitions), and universality_sample_law nu n d is the case
   lam k = nu (k mod d). The proofs of the interpolation estimate are
   stated for flat families (item X2 of phase 6 and the following).

   Definitions:
     flat_row lam d i == the coordinate laws of point i:
                         j |-> lam (i * d + j)

   Results.
   - tuple_prod_tnth: coordinate i of tuple_prod mu n has law mu i.
   - flat_index_lt, flat_row_hyp: coordinate j < d of point i < n is
     coordinate i * d + j < n * d, so a hypothesis on every coordinate law
     holds for the coordinate laws of every point.
   - flat_rows_law, flat_row_law: under tuple_prod lam (n * d), the points
     are independent and point i has law tuple_prod (flat_row lam d i) d
     (tuple_prod_rows of library/probability/tuple_rows.v).
   - flat_map_law, flat_features_law: the images of the points by a
     measurable map are independent; in particular the features
     W(x_1), ..., W(x_n) of the points (unsat_features) are independent,
     the feature of point i with law data_feature_law (flat_row lam d i) d.
   - flat_row_mod, flat_row_mod_prod, flat_row_mod_feature: for
     lam k = nu (k mod d), flat_row lam d i j = nu j for j < d, so point i
     has law tuple_prod nu d and its feature the law data_feature_law nu d:
     the old statements about universality_sample_law are cases of the flat
     ones.
   - flat_row_label, flat_row_label_prod: for the labelled law of a
     mixture, flat_row lam d i j = mu (s_i) j for i < n and j < d, and
     point i has law tuple_prod (mu (s_i)) d.
   - mixture_label_lt, labelled_component: the labels are component
     indices, so the labelled law of a mixture of component laws is a flat
     family of component laws. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
From EllipsoidUniversality.Model Require Import Rows.
Import GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure. *)
Local Notation RR := (R : realType).

Section marginal.
Local Open Scope ereal_scope.
Context dT (T : measurableType dT).

Lemma tuple_prod_tnth (mu : nat -> probability T RR) n (i : 'I_n) (B : set T) :
  measurable B -> tuple_prod mu n [set y | B (tnth y i)] = mu i B.
Proof.
move=> mB.
pose f (j : nat) (t : T) : RR := if j == i then \1_B t else 1%R.
have mf j : measurable_fun [set: T] (f j).
  rewrite /f; case: (j == i); first exact: measurable_indic.
  exact: measurable_cst.
have f0 j t : (0 <= f j t)%R by rewrite /f; case: (j == i).
have h := ge0_integral_tuple_prod_prod mu n mf f0.
have -> : tuple_prod mu n [set y | B (tnth y i)] =
    \int[tuple_prod mu n]_x (\prod_(j < n) f j (tnth x j))%:E.
  have mS : measurable [set y : n.-tuple T | B (tnth y i)].
    rewrite -[X in measurable X]setTI.
    by apply: (measurable_tnth i) => //.
  transitivity (\int[tuple_prod mu n]_y (\1_[set y | B (tnth y i)] y)%:E).
    by rewrite integral_indic // setIT.
  apply: eq_integral => y _; congr (_%:E).
  rewrite (bigD1 i) //= big1 ?mulr1.
    by move=> j ji; rewrite /f val_eqE (negPf ji).
  by rewrite /f eqxx !indicE.
rewrite h (bigD1 i) //= big1 ?mule1.
  move=> j ji; rewrite /f val_eqE (negPf ji).
  by rewrite integral_cst //= probability_setT mul1e.
by rewrite /f eqxx integral_indic // setIT.
Qed.

End marginal.

(* The coordinate laws of point i. *)
Definition flat_row (lam : nat -> probability (measurableTypeR R) R) (d i : nat) :
    nat -> probability (measurableTypeR R) R :=
  fun j => lam (i * d + j)%N.

(* Coordinate j < d of point i < n is coordinate i * d + j < n * d. *)
Lemma flat_index_lt n d i j : (i < n)%N -> (j < d)%N -> (i * d + j < n * d)%N.
Proof.
move=> id jd; apply: (@leq_trans (i.+1 * d)); last by rewrite leq_mul2r id orbT.
by rewrite mulSn addnC ltn_add2r.
Qed.

(* A property of every coordinate law is a property of the coordinate laws
   of every point. *)
Lemma flat_row_hyp (P : probability (measurableTypeR R) R -> Prop)
    (lam : nat -> probability (measurableTypeR R) R) n d :
  (forall k, (k < n * d)%N -> P (lam k)) ->
  forall i j, (i < n)%N -> (j < d)%N -> P (flat_row lam d i j).
Proof. by move=> h i j id jd; rewrite /flat_row; apply: h; exact: flat_index_lt. Qed.

Section flat.
Local Open Scope ereal_scope.
Variables (lam : nat -> probability (measurableTypeR R) R) (n d : nat).

Lemma flat_rows_law (A : set (n.-tuple (d.-tuple (measurableTypeR R)))) :
  measurable A ->
  tuple_prod lam (n * d) (tuple_rows n d @^-1` A) =
  tuple_prod (fun i => tuple_prod (flat_row lam d i) d) n A.
Proof. by move=> mA; rewrite tuple_prod_rows. Qed.

Lemma flat_row_law (B : set (d.-tuple (measurableTypeR R))) (i : 'I_n) :
  measurable B ->
  tuple_prod lam (n * d) [set x | B (tnth (tuple_rows n d x) i)] =
  tuple_prod (flat_row lam d i) d B.
Proof.
move=> mB.
have mA : measurable
    [set y : n.-tuple (d.-tuple (measurableTypeR R)) | B (tnth y i)].
  rewrite -[X in measurable X]setTI.
  by apply: (measurable_tnth i) => //.
rewrite -(@tuple_prod_tnth _ _ (fun i => tuple_prod (flat_row lam d i) d) n i
  B mB).
by rewrite -(flat_rows_law _ mA).
Qed.

(* The images of the points by a measurable map g are independent, the
   image of point i with the law mu i of g under its law. *)
Lemma flat_map_law d' (U : measurableType d') (mu : nat -> probability U RR)
    (g : d.-tuple (measurableTypeR R) -> U) (A : set (n.-tuple U)) :
  measurable_fun setT g ->
  (forall i B, measurable B ->
     mu i B = tuple_prod (flat_row lam d i) d (g @^-1` B)) ->
  measurable A ->
  tuple_prod lam (n * d)
    ((fun x => tuple_map (fun=> g) (tuple_rows n d x)) @^-1` A) =
  tuple_prod mu n A.
Proof.
move=> mg mug mA.
have mg' : forall i : nat, measurable_fun setT ((fun=> g) i) by [].
rewrite (@tuple_prod_map _ _ _ _ RR (fun i => tuple_prod (flat_row lam d i) d)
  mu (fun=> g) n A mg' mug mA).
have mgA : measurable (tuple_map (fun=> g) @^-1` A).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_tuple_map mg') measurableT A mA.
by rewrite -(flat_rows_law _ mgA).
Qed.

Lemma flat_features_law (A : set (n.-tuple 'rV[RR]_(d * d))) : measurable A ->
  tuple_prod lam (n * d) (unsat_features n d @^-1` A) =
  tuple_prod (fun i => data_feature_law (flat_row lam d i) d) n A.
Proof.
move=> mA.
have mg : forall i : nat, measurable_fun setT
    ((fun=> data_feature_map d) i : d.-tuple (measurableTypeR R) -> 'rV[RR]_(d * d)).
  by move=> i; exact: measurable_data_feature_map.
rewrite (@tuple_prod_map _ _ _ _ RR (fun i => tuple_prod (flat_row lam d i) d)
  (fun i => data_feature_law (flat_row lam d i) d) (fun=> data_feature_map d)
  n A mg) //.
have mgA : measurable (tuple_map (fun=> data_feature_map d) @^-1` A).
  rewrite -[X in measurable X]setTI.
  exact: (measurable_tuple_map mg) measurableT A mA.
rewrite -(flat_rows_law _ mgA).
congr (tuple_prod lam (n * d) _); apply/seteqP; split => x /=;
  by rewrite unsat_features_rows.
Qed.

End flat.

(* universality_sample_law nu n d is the flat family k |-> nu (k mod d). *)
Lemma flat_row_mod (nu : nat -> probability (measurableTypeR R) R) d i j :
  (j < d)%N -> flat_row (fun k => nu (k %% d)%N) d i j = nu j.
Proof. by move=> jd; rewrite /flat_row modnMDl modn_small. Qed.

Lemma flat_row_mod_prod (nu : nat -> probability (measurableTypeR R) R) d i :
  tuple_prod (flat_row (fun k => nu (k %% d)%N) d i) d = tuple_prod nu d.
Proof. by apply: eq_tuple_prod => j jd; exact: flat_row_mod. Qed.

Lemma flat_row_mod_feature (nu : nat -> probability (measurableTypeR R) R) d i :
  data_feature_law (flat_row (fun k => nu (k %% d)%N) d i) d =
  data_feature_law nu d.
Proof. by rewrite /data_feature_law flat_row_mod_prod. Qed.

(* The labelled law of a mixture is the flat family
   k |-> mu (s_(k / d)) (k mod d), and point i has the coordinate laws of
   component s_i. *)
Lemma flat_row_label (N : nat) (mu : nat -> nat -> probability (measurableTypeR R) R)
    n d (s : n.-tuple 'I_N) (i : 'I_n) j : (j < d)%N ->
  flat_row (fun k => mu (mixture_label s (k %/ d)) (k %% d)) d i j =
  mu (tnth s i) j.
Proof.
move=> jd; have d0 : (0 < d)%N by apply: leq_ltn_trans jd.
rewrite /flat_row modnMDl modn_small // divnMDl // divn_small // addn0.
by rewrite /mixture_label (nth_map (tnth s i)) ?size_tuple // -tnth_nth.
Qed.

(* The label of a point is a component index. *)
Lemma mixture_label_lt (N n : nat) (s : n.-tuple 'I_N) i :
  (i < n)%N -> (mixture_label s i < N)%N.
Proof.
move=> i_lt.
rewrite /mixture_label (nth_map (tnth s (Ordinal i_lt))) ?size_tuple //.
exact: ltn_ord.
Qed.

(* The labelled law of a mixture of component laws is a flat family of
   component laws. *)
Lemma labelled_component (K : R) (N : nat)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    n d (s : n.-tuple 'I_N) :
  (forall t j, (t < N)%N -> (j < d)%N -> mixture_component_law K (mu t j)) ->
  forall k, (k < n * d)%N ->
    mixture_component_law K (mu (mixture_label s (k %/ d)) (k %% d)).
Proof.
move=> hmu k kn.
have d0 : (0 < d)%N.
  by rewrite lt0n; apply/eqP => d0; move: kn; rewrite d0 muln0 ltn0.
apply: hmu; last exact: ltn_pmod.
by apply: mixture_label_lt; rewrite ltn_divLR.
Qed.

Lemma flat_row_label_prod (N : nat)
    (mu : nat -> nat -> probability (measurableTypeR R) R)
    n d (s : n.-tuple 'I_N) (i : 'I_n) :
  tuple_prod (flat_row (fun k => mu (mixture_label s (k %/ d)) (k %% d)) d i) d =
  tuple_prod (mu (tnth s i)) d.
Proof. by apply: eq_tuple_prod => j jd; exact: flat_row_label. Qed.
