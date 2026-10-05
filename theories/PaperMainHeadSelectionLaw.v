(* The exact law of a fixed head of rows of the Gaussian data sample. A
   sample x : paper_main_sample N d has N rows of d coordinates, row t at
   positions t d + j, j < d.
   - Row permutations. For pi : 'S_N, the coordinate map
     t d + j |-> pi(t) d + j is a permutation of 'I_(N d)
     (paper_main_row_perm pi), and paper_main_permute_rows pi x is the sample
     whose row t is row pi(t) of x. By PaperMainGaussianPermutationLaw it
     preserves gaussian_product_law (N d) on every measurable event.
   - Head and tail blocks. For N = k + n, paper_main_head_selection k n d pi x
     splits the row-permuted sample into its first k rows and last n rows.
     It is measurable, and for every measurable joint event E
       P[(head, tail) in E] = (P_(k d) \x P_(n d)) E.
     Head row t is row pi(t) of x, tail row u is row pi(k + u) of x, and the
     same holds for the head features W_i.
   - Fixed heads. For a fixed list J of distinct rows below k + n with
     size J = k, there is pi whose first k images are J, in order, and whose
     last n images are the other rows in increasing order.
   J is fixed, not chosen from the data; no law is claimed for a
   data-dependent selection. No independence or regularity premise is used. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure PaperMainDefinitions PaperMainGeometryHeadFeature
  PaperMainSampling PaperMainHeadLaw PaperMainDataSampleTail
  PaperMainGaussianPermutationLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* Row and column of a coordinate. *)

Lemma paper_main_row_div_lt N d c : (c < N * d)%N -> (c %/ d < N)%N.
Proof. by case: d => [|d]; [rewrite muln0 | move=> H; rewrite ltn_divLR]. Qed.

Lemma paper_main_row_mod_lt N d c : (c < N * d)%N -> (c %% d < d)%N.
Proof. by case: d => [|d]; [rewrite muln0 | move=> _; rewrite ltn_mod]. Qed.

Lemma paper_main_row_target_lt N d a b : (a < N)%N -> (b < d)%N -> (a * d + b < N * d)%N.
Proof.
move=> Ha Hb; apply: (@leq_trans (a * d + d)); first by rewrite ltn_add2l.
by rewrite -mulSnr leq_mul2r Ha orbT.
Qed.

Definition paper_main_row_index {N d : nat} (c : 'I_(N * d)) : 'I_N :=
  Ordinal (paper_main_row_div_lt N d c (ltn_ord c)).

Definition paper_main_col_index {N d : nat} (c : 'I_(N * d)) : 'I_d :=
  Ordinal (paper_main_row_mod_lt N d c (ltn_ord c)).

Definition paper_main_coord_index {N d : nat} (t : 'I_N) (j : 'I_d) : 'I_(N * d) :=
  Ordinal (paper_main_row_target_lt N d t j (ltn_ord t) (ltn_ord j)).

Lemma paper_main_coord_index_row N d (t : 'I_N) (j : 'I_d) :
  paper_main_row_index (paper_main_coord_index t j) = t.
Proof.
apply/val_inj => /=; have Hd : (0 < d)%N by case: d j => [[]|].
by rewrite divnMDl // divn_small // addn0.
Qed.

Lemma paper_main_coord_index_col N d (t : 'I_N) (j : 'I_d) :
  paper_main_col_index (paper_main_coord_index t j) = j.
Proof. by apply/val_inj => /=; rewrite modnMDl modn_small. Qed.

Lemma paper_main_coord_indexK N d (c : 'I_(N * d)) :
  paper_main_coord_index (paper_main_row_index c) (paper_main_col_index c) = c.
Proof. by apply/val_inj => /=; rewrite -divn_eq. Qed.

(* The row permutation of the coordinates. *)

Definition paper_main_row_coord {N d : nat} (pi : 'S_N) (c : 'I_(N * d)) : 'I_(N * d) :=
  paper_main_coord_index (pi (paper_main_row_index c)) (paper_main_col_index c).

Lemma paper_main_row_coord_inj N d (pi : 'S_N) : injective (@paper_main_row_coord N d pi).
Proof.
move=> c1 c2 H.
have Hr := congr1 paper_main_row_index H.
have Hc := congr1 paper_main_col_index H.
rewrite /paper_main_row_coord !paper_main_coord_index_row in Hr.
rewrite /paper_main_row_coord !paper_main_coord_index_col in Hc.
rewrite -(paper_main_coord_indexK _ _ c1) -(paper_main_coord_indexK _ _ c2).
by rewrite (perm_inj Hr) Hc.
Qed.

Definition paper_main_row_perm {N d : nat} (pi : 'S_N) : 'S_(N * d) :=
  perm (paper_main_row_coord_inj N d pi).

Definition paper_main_permute_rows {N d : nat} (pi : 'S_N) (x : paper_main_sample N d) :
    paper_main_sample N d :=
  paper_main_permute_tuple (paper_main_row_perm pi) x.

Lemma paper_main_permute_rows_measurable N d (pi : 'S_N) :
  measurable_fun [set: paper_main_sample N d] (paper_main_permute_rows pi).
Proof. exact: paper_main_permute_tuple_measurable. Qed.

Theorem paper_main_permute_rows_law N d (pi : 'S_N) (E : set (paper_main_sample N d)) :
  measurable E ->
  paper_main_probability N d (paper_main_permute_rows pi @^-1` E) =
  paper_main_probability N d E.
Proof. exact: paper_main_permute_tuple_law. Qed.

Lemma paper_main_permute_rows_point N d (pi : 'S_N) (x : paper_main_sample N d) (t : 'I_N) :
  paper_main_point (paper_main_permute_rows pi x) t = paper_main_point x (pi t).
Proof.
apply/matrixP => j c; rewrite [c]ord1 !mxE.
have E1 : List.nth (t * d + j) (tval (paper_main_permute_rows pi x)) 0 =
    tnth (paper_main_permute_rows pi x) (paper_main_coord_index t j).
  by rewrite gpp_nthE (tnth_nth 0).
have E2 : List.nth (pi t * d + j) (tval x) 0 = tnth x (paper_main_coord_index (pi t) j).
  by rewrite gpp_nthE (tnth_nth 0).
rewrite E1 E2 /paper_main_permute_rows paper_main_permute_tuple_tnth permE.
by rewrite /paper_main_row_coord paper_main_coord_index_row paper_main_coord_index_col.
Qed.

(* The head and tail blocks. *)

Definition paper_main_head_selection k n d (pi : 'S_(k + n))
    (x : paper_main_sample (k + n) d) : paper_main_sample k d * paper_main_sample n d :=
  paper_main_split_points k n d (paper_main_permute_rows pi x).

Lemma paper_main_head_selection_measurable k n d (pi : 'S_(k + n)) :
  measurable_fun [set: paper_main_sample (k + n) d] (paper_main_head_selection k n d pi).
Proof.
exact: (measurableT_comp (paper_main_split_points_measurable k n d)
  (paper_main_permute_rows_measurable (k + n) d pi)).
Qed.

Theorem paper_main_head_selection_law k n d (pi : 'S_(k + n))
    (E : set (paper_main_sample k d * paper_main_sample n d)) :
  measurable E ->
  paper_main_probability (k + n) d (paper_main_head_selection k n d pi @^-1` E) =
  (gaussian_product_law (k * d)%N \x gaussian_product_law (n * d)%N)%E E.
Proof.
move=> mE.
have mS : measurable (paper_main_split_points k n d @^-1` E).
  have H := paper_main_split_points_measurable k n d measurableT _ mE.
  by rewrite setTI in H.
change (paper_main_probability (k + n) d
  (paper_main_permute_rows pi @^-1` (paper_main_split_points k n d @^-1` E)) =
  (gaussian_product_law (k * d)%N \x gaussian_product_law (n * d)%N)%E E).
rewrite (paper_main_permute_rows_law (k + n) d pi _ mS).
exact: paper_main_split_points_law.
Qed.

Lemma paper_main_head_selection_head_point k n d (pi : 'S_(k + n))
    (x : paper_main_sample (k + n) d) (t : 'I_k) :
  paper_main_point (paper_main_head_selection k n d pi x).1 t =
  paper_main_point x (pi (lshift n t)).
Proof.
rewrite /paper_main_head_selection paper_main_split_pointsE /=.
rewrite (pmds_take_point k n d _ t (ltn_ord t)).
by rewrite -(paper_main_permute_rows_point (k + n) d pi x (lshift n t)).
Qed.

Lemma paper_main_head_selection_tail_point k n d (pi : 'S_(k + n))
    (x : paper_main_sample (k + n) d) (u : 'I_n) :
  paper_main_point (paper_main_head_selection k n d pi x).2 u =
  paper_main_point x (pi (rshift k u)).
Proof.
rewrite /paper_main_head_selection paper_main_split_pointsE /=.
rewrite paper_main_drop_points_point.
by rewrite -(paper_main_permute_rows_point (k + n) d pi x (rshift k u)).
Qed.

Lemma paper_main_head_selection_head_feature k n d (pi : 'S_(k + n))
    (x : paper_main_sample (k + n) d) (t : 'I_k) :
  paper_main_head_feature (paper_main_head_selection k n d pi x).1 t =
  paper_main_head_feature x (pi (lshift n t)).
Proof. by rewrite /paper_main_head_feature paper_main_head_selection_head_point. Qed.

Lemma paper_main_head_selection_tail_feature k n d (pi : 'S_(k + n))
    (x : paper_main_sample (k + n) d) (u : 'I_n) :
  paper_main_head_feature (paper_main_head_selection k n d pi x).2 u =
  paper_main_head_feature x (pi (rshift k u)).
Proof. by rewrite /paper_main_head_feature paper_main_head_selection_tail_point. Qed.

(* A fixed ordered head gives a row permutation. *)

Definition paper_main_head_complement (N : nat) (J : seq nat) : seq nat :=
  [seq i <- iota 0 N | i \notin J].

Theorem paper_main_head_selection_perm_exists k n (J : seq nat) :
  uniq J -> size J = k -> all (fun i => i < k + n)%N J ->
  exists pi : 'S_(k + n),
    (forall t : 'I_k, nat_of_ord (pi (lshift n t)) = nth 0 J t) /\
    (forall u : 'I_n,
      nat_of_ord (pi (rshift k u)) = nth 0 (paper_main_head_complement (k + n) J) u).
Proof.
move=> HJu HJs HJa.
set C := paper_main_head_complement (k + n) J.
set L := J ++ C.
have HJsub : {subset J <= iota 0 (k + n)}.
  by move=> i Hi; rewrite mem_iota /= add0n; exact: (allP HJa).
have HL : perm_eq L (iota 0 (k + n)).
  rewrite /L /C /paper_main_head_complement.
  apply: (@perm_trans _ ([seq i <- iota 0 (k + n) | i \in J] ++
      [seq i <- iota 0 (k + n) | i \notin J])).
    rewrite perm_cat2r; apply: uniq_perm => //.
    - by apply: filter_uniq; exact: iota_uniq.
    - move=> i; rewrite mem_filter /=; apply/idP/andP => [Hi | [] //].
      by split=> //; exact: HJsub.
  by apply/permPl; exact: (perm_filterC (mem J) (iota 0 (k + n))).
have HLs : size L = (k + n)%N by rewrite (perm_size HL) size_iota.
have HLu : uniq L by rewrite (perm_uniq HL) iota_uniq.
have HLb : forall t : 'I_(k + n), (nth 0 L t < k + n)%N.
  move=> t; have Ht : (t < size L)%N by rewrite HLs ltn_ord.
  by have := mem_nth 0 Ht; rewrite (perm_mem HL) mem_iota add0n.
pose f := fun t : 'I_(k + n) => Ordinal (HLb t).
have Hf : injective f.
  move=> t1 t2 /(congr1 val) /= H; apply/val_inj.
  by apply/eqP; rewrite -(nth_uniq 0 _ _ HLu) ?HLs ?ltn_ord // H.
exists (perm Hf); split.
- by move=> t; rewrite permE /= /L nth_cat HJs ltn_ord.
- by move=> u; rewrite permE /= /L nth_cat HJs ltnNge leq_addr /= addKn.
Qed.

(* Everything for a fixed ordered head J. *)
