(* The sample as rows, at Stdlib's R: the law of the n * d coordinates of a
   sample of Koehler and Sohn's theorem (arXiv 2608.27372, lines 166-171 of
   arxiv_v1.tex) as the law of n independent points.

   A sample of paper_main_sample n d is a tuple of n * d coordinates, and
   paper_main_point x i is the column of the coordinates i * d + j, j < d.
   Under universality_sample_law nu n d, coordinate k has law nu (k mod d).

   Main results:
   - paper_main_point_row: paper_main_point x i is the tuple_point of row i
     of tuple_rows n d x (probability/tuple_rows.v, Features/Definitions);
     sample_points_rows and unsat_features_rows write the tuple of the
     values of a function at the n points, and unsat_features n d x, as
     tuple_map of the rows.
   - integral_sample_rows: the image of universality_sample_law nu n d
     under tuple_rows n d is tuple_prod (fun=> tuple_prod nu d) n: the
     points are independent, and each has independent coordinates of laws
     nu 0, ..., nu (d - 1).
   - integral_sample_map: for g measurable on the d-tuples of coordinates
     and mu the law of g under tuple_prod nu d, the values of g at the n
     rows have the law tuple_prod (fun=> mu) n.
   - integral_sample_features, sample_features_law: the features
     unsat_features n d x of the points are independent with the common
     law data_feature_law nu d; measurable_unsat_features.

   Planned (phase 5, stage 1): the same for the frozen
   gaussian_product_law (n * d), whose rows are independent with law
   gaussian_product_law d (for Unsat/GoeBridge). *)
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
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Features Require Import Definitions.
Import GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure, which carries the
   measurable structure of MathComp-Analysis on matrices. *)
Local Notation RR := (R : realType).

Lemma List_nthE (A : Type) (s : seq A) (x0 : A) k :
  List.nth k s x0 = nth x0 s k.
Proof. by elim: s k => [|a s IH] [|k] //=. Qed.

(* The point i of a sample is the point of its row i. *)
Lemma paper_main_point_row n d (x : paper_main_sample n d) (i : 'I_n) :
  paper_main_point x i = tuple_point (tnth (tuple_rows n d x) i).
Proof.
apply/matrixP => j k; rewrite ord1 !mxE !tnth_mktuple (tnth_nth 0).
by rewrite List_nthE.
Qed.

Section sample_rows.
Local Open Scope ereal_scope.

(* The rows of a sample are independent, with independent coordinates of
   laws nu 0, ..., nu (d - 1). *)
Lemma integral_sample_rows (nu : nat -> probability (measurableTypeR R) R)
    n d (G : n.-tuple (d.-tuple (measurableTypeR R)) -> \bar R) :
  measurable_fun setT G ->
  \int[universality_sample_law nu n d]_x G (tuple_rows n d x) =
  \int[tuple_prod (fun=> tuple_prod nu d) n]_y G y.
Proof.
move=> mG; rewrite /universality_sample_law /universality_product_law.
rewrite integral_tuple_rows //.
have -> : tuple_prod
    (fun i => tuple_prod (fun j => nu ((i * d + j) %% d)%N) d) n =
    tuple_prod (fun=> tuple_prod nu d) n.
  apply: eq_tuple_prod => i _; apply: eq_tuple_prod => j jd.
  by rewrite modnMDl modn_small.
by [].
Qed.

Lemma sample_points_rows n d d' (U : measurableType d') (f : 'cV[R]_d -> U)
    (x : paper_main_sample n d) :
  [tuple f (paper_main_point x i) | i < n] =
  tuple_map (fun=> f \o tuple_point) (tuple_rows n d x).
Proof.
apply: eq_from_tnth => i; rewrite [LHS]tnth_mktuple paper_main_point_row.
by rewrite [RHS]tnth_mktuple.
Qed.

(* For a measurable g of the coordinates of one point, the values of g at
   the n points of a sample are independent with the law of g under
   tuple_prod nu d. *)
Lemma integral_sample_map (nu : nat -> probability (measurableTypeR R) R)
    n d d' (U : measurableType d') (mu : probability U R)
    (g : d.-tuple (measurableTypeR R) -> U) (H : n.-tuple U -> \bar R) :
  measurable_fun setT g ->
  (forall A, measurable A -> mu A = tuple_prod nu d (g @^-1` A)) ->
  measurable_fun setT H ->
  \int[universality_sample_law nu n d]_x
    H (tuple_map (fun=> g) (tuple_rows n d x)) =
  \int[tuple_prod (fun=> mu) n]_y H y.
Proof.
move=> mg mug mH.
have mHm : measurable_fun setT
    (fun y : n.-tuple (d.-tuple (measurableTypeR R)) =>
      H (tuple_map (fun=> g) y)).
  by apply: measurableT_comp mH _; exact: measurable_tuple_map.
rewrite (integral_sample_rows nu n d _ mHm).
by symmetry; apply: integral_tuple_map.
Qed.

Lemma unsat_features_rows n d (x : paper_main_sample n d) :
  unsat_features n d x =
  tuple_map (fun=> data_feature_map d) (tuple_rows n d x).
Proof.
apply: eq_from_tnth => i; rewrite [LHS]tnth_mktuple paper_main_point_row.
by rewrite [RHS]tnth_mktuple.
Qed.

(* The features of the points of a sample are independent with the common
   law data_feature_law nu d. *)
Lemma integral_sample_features (nu : nat -> probability (measurableTypeR R) R)
    n d (H : n.-tuple 'rV[RR]_(d * d) -> \bar R) :
  measurable_fun setT H ->
  \int[universality_sample_law nu n d]_x H (unsat_features n d x) =
  \int[tuple_prod (fun=> data_feature_law nu d) n]_Z H Z.
Proof.
move=> mH; under eq_integral do rewrite unsat_features_rows.
have mHm : measurable_fun setT
    (fun y : n.-tuple (d.-tuple (measurableTypeR R)) =>
      H (tuple_map (fun=> data_feature_map d) y)).
  apply: measurableT_comp mH _; apply: measurable_tuple_map => i.
  exact: measurable_data_feature_map.
rewrite (integral_sample_rows nu n d _ mHm).
by symmetry; apply: integral_tuple_map.
Qed.

Lemma measurable_unsat_features n d :
  measurable_fun [set: paper_main_sample n d]
    (fun x => unsat_features n d x : n.-tuple 'rV[RR]_(d * d)).
Proof.
apply: (eq_measurable_fun (fun x : paper_main_sample n d =>
    tuple_map (fun=> data_feature_map d) (tuple_rows n d x))).
  by move=> x _; rewrite unsat_features_rows.
apply: measurableT_comp; last exact: measurable_tuple_rows.
by apply: measurable_tuple_map => i; exact: measurable_data_feature_map.
Qed.

Lemma sample_features_law (nu : nat -> probability (measurableTypeR R) R)
    n d (A : set (n.-tuple 'rV[RR]_(d * d))) : measurable A ->
  universality_sample_law nu n d (unsat_features n d @^-1` A) =
  tuple_prod (fun=> data_feature_law nu d) n A.
Proof.
move=> mA; have mUA : measurable (unsat_features n d @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_unsat_features.
transitivity (\int[universality_sample_law nu n d]_x
    (\1_(unsat_features n d @^-1` A) x)%:E).
  by rewrite integral_indic // setIT.
transitivity (\int[tuple_prod (fun=> data_feature_law nu d) n]_Z (\1_A Z)%:E);
  last by rewrite integral_indic // setIT.
rewrite -integral_sample_features.
  by apply/measurable_EFinP; exact: measurable_indic.
by apply: eq_integral => x _; rewrite !indicE.
Qed.

End sample_rows.
