(* Coordinate selections of product-mixture samples. An injective selection
   gives the exact marginal law, with the original component weights and
   selected coordinate laws. Permutations and head/tail restrictions are
   special cases. Neither statement asserts independence of the selected
   coordinates after mixing, or of complementary blocks.
   Source: doc/shifted-gaussian.tex, sparse-shift reduction. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import sequences esum ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows conditioning.
From GaussianAnalysis.probability Require Import mixture countable_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting.Gaussian.Law Require Import LibraryBridge.
From EllipsoidUniversality Require Import MixtureDefinitions CountableMixtureDefinitions.
From EllipsoidUniversality.Model Require Import Rows.
From EllipsoidUniversality.Sat Require Import AprioriSparse.
From EllipsoidUniversality.Shifted Require Import GaussianRows MixtureRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sparse_flat_index n d p (f : 'I_p -> 'I_d) (a : 'I_(n * p)) : 'I_(n * d) :=
  row_index (sample_flat_row a) (f (sample_flat_col a)).

Lemma sparse_flat_indexK n d p (f : 'I_p -> 'I_d) (i : 'I_n) (j : 'I_p) :
  sparse_flat_index f (row_index i j) = row_index i (f j).
Proof. by rewrite /sparse_flat_index sample_flat_rowK sample_flat_colK. Qed.

Lemma sparse_flat_index_inj n d p (f : 'I_p -> 'I_d) :
  injective f -> injective (@sparse_flat_index n d p f).
Proof.
move=> fi a b eqab.
have er := congr1 (@sample_flat_row n d) eqab.
have ec := congr1 (@sample_flat_col n d) eqab.
rewrite /sparse_flat_index !sample_flat_rowK in er.
rewrite /sparse_flat_index !sample_flat_colK in ec.
rewrite -[a]sample_flat_indicesK -[b]sample_flat_indicesK er (fi _ _ ec).
by [].
Qed.

Definition sparse_sample_pick n d p (f : 'I_p -> 'I_d)
    (x : paper_main_sample n d) : paper_main_sample n p :=
  tuple_pick (@sparse_flat_index n d p f) x.

Definition sparse_sample_head n h p :
    paper_main_sample n (h+p) -> paper_main_sample n h :=
  @sparse_sample_pick n (h+p) h (lshift p).
Definition sparse_sample_tail n h p :
    paper_main_sample n (h+p) -> paper_main_sample n p :=
  @sparse_sample_pick n (h+p) p (@rshift h p).

Lemma measurable_sparse_sample_pick n d p (f : 'I_p -> 'I_d) :
  measurable_fun [set: paper_main_sample n d] (@sparse_sample_pick n d p f).
Proof. exact: measurable_tuple_pick. Qed.

Lemma sparse_point_entry n d (x : paper_main_sample n d) (i : 'I_n) (j : 'I_d) :
  paper_main_point x i j 0 = tnth x (row_index i j).
Proof.
by rewrite -sample_row_tuple_entry /sample_row_tuple tnth_mktuple !mxE.
Qed.

Lemma sparse_sample_pick_point n d p (f : 'I_p -> 'I_d)
    (x : paper_main_sample n d) (i : 'I_n) (j : 'I_p) :
  paper_main_point (sparse_sample_pick f x) i j 0 = paper_main_point x i (f j) 0.
Proof.
by rewrite !sparse_point_entry /sparse_sample_pick /tuple_pick tnth_mktuple
  sparse_flat_indexK.
Qed.

Lemma sparse_flat_coordinate_law n d p (f : 'I_p -> 'I_d)
    (mu nu : nat -> nat -> probability (measurableTypeR R) R)
    (labels : nat -> nat) (A : set (paper_main_sample n p)) :
  injective f -> (forall s (j : 'I_p), nu s j = mu s (f j)) -> measurable A ->
  tuple_prod (fun a => mu (labels (a %/ d)) (a %% d)%N) (n * d)
    ((@sparse_sample_pick n d p f) @^-1` A) =
  tuple_prod (fun a => nu (labels (a %/ p)) (a %% p)%N) (n * p) A.
Proof.
move=> fi hn mA.
apply: tuple_prod_pick (sparse_flat_index_inj fi) _ mA => a.
have er := sample_flat_rowK (sample_flat_row a) (f (sample_flat_col a)).
have ec := sample_flat_colK (sample_flat_row a) (f (sample_flat_col a)).
have erV := congr1 val er; have ecV := congr1 val ec.
change ((sparse_flat_index f a %/ d)%N = (a %/ p)%N) in erV.
change ((sparse_flat_index f a %% d)%N = (f (sample_flat_col a) : nat)) in ecV.
rewrite erV ecV.
exact: (hn _ (sample_flat_col a)).
Qed.

Theorem finite_sparse_sample_law n d p (f : 'I_p -> 'I_d)
    (N : nat) (w : nat -> R)
    (mu nu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set (paper_main_sample n p)) :
  injective f -> (forall s (j : 'I_p), nu s j = mu s (f j)) -> measurable A ->
  mixture_probability N w mu n d ((@sparse_sample_pick n d p f) @^-1` A) =
  mixture_probability N w nu n p A.
Proof.
move=> fi hn mA; rewrite /mixture_probability.
apply: eq_bigr => s _; congr (_ * _)%E.
exact: sparse_flat_coordinate_law fi hn mA.
Qed.

Theorem countable_sparse_sample_law n d p (f : 'I_p -> 'I_d)
    (w : nat -> R)
    (mu nu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set (paper_main_sample n p)) :
  injective f -> (forall s (j : 'I_p), nu s j = mu s (f j)) -> measurable A ->
  countable_mixture_probability w mu n d ((@sparse_sample_pick n d p f) @^-1` A) =
  countable_mixture_probability w nu n p A.
Proof.
move=> fi hn mA; rewrite /countable_mixture_probability.
apply: eq_esum => s _; congr (_ * _)%E.
exact: sparse_flat_coordinate_law fi hn mA.
Qed.

Definition sparse_row_pick d p (f : 'I_p -> 'I_d) (x : 'rV[RR]_d) : 'rV[RR]_p :=
  \row_j x 0 (f j).

Lemma measurable_sparse_row_pick d p (f : 'I_p -> 'I_d) :
  measurable_fun [set: 'rV[RR]_d] (@sparse_row_pick d p f).
Proof.
apply/measurable_fun_mxP=>i j; under eq_fun do rewrite /sparse_row_pick mxE.
exact: measurable_mxentry.
Qed.

Lemma sparse_row_pick_tuple d p (f : 'I_p -> 'I_d)
    (x : d.-tuple (measurableTypeR R)) :
  sparse_row_pick f (row_of_tuple d x) = row_of_tuple p (tuple_pick f x).
Proof.
apply/rowP=>j.
by rewrite /sparse_row_pick mxE !row_of_tupleE /tuple_pick tnth_mktuple.
Qed.

Lemma sparse_point_law d p (f : 'I_p -> 'I_d)
    (mu nu : nat -> probability (measurableTypeR R) R) (A : set 'rV[RR]_p) :
  injective f -> (forall j : 'I_p, nu j = mu (f j)) -> measurable A ->
  point_law d mu (sparse_row_pick f @^-1` A) = point_law p nu A.
Proof.
move=> fi hn mA.
have mB : measurable ((row_of_tuple p) @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_row_of_tuple.
rewrite /point_law /distribution /pushforward /=.
change (tuple_prod mu d (row_of_tuple d @^-1` (sparse_row_pick f @^-1` A)) =
  tuple_prod nu p (row_of_tuple p @^-1` A)).
have -> : row_of_tuple d @^-1` (sparse_row_pick f @^-1` A) =
    tuple_pick f @^-1` ((row_of_tuple p) @^-1` A).
  by apply/funext=>x; rewrite /= sparse_row_pick_tuple.
exact: tuple_prod_pick fi hn mB.
Qed.

Theorem finite_sparse_row_law d p (f : 'I_p -> 'I_d)
    (N : nat) (w : 'I_N -> R) (hw : mixture_weights w)
    (mu nu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set 'rV[RR]_p) :
  injective f -> (forall s (j : 'I_p), nu s j = mu s (f j)) -> measurable A ->
  mixture (fun s : 'I_N => point_law d (mu s)) hw (sparse_row_pick f @^-1` A) =
  mixture (fun s : 'I_N => point_law p (nu s)) hw A.
Proof.
move=> fi hn mA; rewrite !mixtureE; apply: eq_bigr=>s _.
by rewrite (sparse_point_law fi (hn s) mA).
Qed.

Theorem countable_sparse_row_law d p (f : 'I_p -> 'I_d)
    (w : nat -> R) (hw : cmixture_weights w)
    (mu nu : nat -> nat -> probability (measurableTypeR R) R)
    (A : set 'rV[RR]_p) :
  injective f -> (forall s (j : 'I_p), nu s j = mu s (f j)) -> measurable A ->
  cmixture (fun s => point_law d (mu s)) hw (sparse_row_pick f @^-1` A) =
  cmixture (fun s => point_law p (nu s)) hw A.
Proof.
move=> fi hn mA; rewrite !cmixtureE.
by under eq_eseriesr do rewrite (sparse_point_law fi (hn _) mA).
Qed.

Lemma sparse_row_head h p (x : 'rV[RR]_(h+p)) :
  sparse_row_pick (lshift p) x = lsubmx x.
Proof. by apply/rowP=>j; rewrite /sparse_row_pick !mxE. Qed.

Lemma sparse_row_tail h p (x : 'rV[RR]_(h+p)) :
  sparse_row_pick (@rshift h p) x = rsubmx x.
Proof. by apply/rowP=>j; rewrite /sparse_row_pick !mxE. Qed.

Section selected_families.
Variable D : nat -> nat.
Variable f : forall p, 'I_p -> 'I_(D p).
Variables (K kappa : R) (N : nat -> nat) (w : nat -> nat -> R).
Variables mu nu : nat -> nat -> nat -> probability (measurableTypeR R) R.
Hypothesis selected_laws : forall p s (j : 'I_p), nu p s j = mu (D p) s (@f p j).

Lemma sparse_finite_family : mixture_family K N w mu ->
  mixture_family K (fun p=>N (D p)) (fun p=>w (D p)) nu.
Proof.
move=> hf p; have [w0 [w1 hm]] := hf (D p); split=> //; split=> //.
move=> s j sN jp; rewrite (@selected_laws p s (Ordinal jp)).
exact: hm sN (ltn_ord _).
Qed.

Lemma sparse_finite_fourth_moment : mixture_fourth_moment kappa N w mu ->
  mixture_fourth_moment kappa (fun p=>N (D p)) (fun p=>w (D p)) nu.
Proof.
move=> hf p j jp.
have eqj s := @selected_laws p s (Ordinal jp).
under eq_bigr do rewrite eqj.
exact: hf (ltn_ord (@f p (Ordinal jp))).
Qed.

Lemma sparse_countable_family : countable_mixture_family K w mu ->
  countable_mixture_family K (fun p=>w (D p)) nu.
Proof.
move=> hf p; have [w0 [w1 hm]] := hf (D p); split=> //; split=> //.
move=> s j jp; rewrite (@selected_laws p s (Ordinal jp)).
exact: hm (ltn_ord _).
Qed.

Lemma sparse_countable_fourth_moment : countable_fourth_moment kappa w mu ->
  countable_fourth_moment kappa (fun p=>w (D p)) nu.
Proof.
move=> hf p j jp.
have eqj s := @selected_laws p s (Ordinal jp).
under eq_eseriesr do rewrite eqj.
exact: hf (ltn_ord (@f p (Ordinal jp))).
Qed.

End selected_families.
