(* The fixed-cutoff spectral head in the first-r-rows orientation convention.

   For PSD S with ||S||_F = 1 and eps > 0, the checked M119 decomposition
   S = O^T diag(a) O (O^T O = 1, a >= 0, #{eps < a_i} <= 1/eps^2) is
   reordered so that the large coefficients come first.
   1. For a predicate p on 'I_d, the list (indices with p) ++ (indices
      without p) is a permutation of enum 'I_d. Reading it position by
      position gives a permutation sigma of 'I_d with (t < r) = p (sigma t),
      where r is the number of indices with p. It is a fixed finite
      construction on 'I_d: no cast of dimensions and no measurable choice.
   2. Permuting the rows of O and the entries of a by the same permutation
      keeps O^T O = 1 and O^T diag(a) O.
   3. Ordered diagonalization: S = O^T diag(a) O with (i < r) = (eps < a_i),
      r <= d, r <= 1/eps^2, and the spectral mask projector of this
      diagonalization is the orientation projector P_r(O) of
      PaperMainOrientationNet (head directions are the first r rows of O).
   4. The M121 decomposition in this orientation: S = H + B, H and B PSD,
      ||B||_op <= eps, ||H||_F <= 1, P H P = H, P S = S P, P^T = P, P P = P
      with P = P_r(O). If d > 1/eps^2 then r < d. r = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainConeConditionOperator PaperMainSymmetricDiagonalization
  PaperMainSpectralCutoff PaperMainOrthogonalMatrixBounds PaperMainSpectralSplit
  PaperMainOrientationNet.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The ordering permutation. *)

Definition paper_main_orientation_order_list {d : nat} (p : pred 'I_d) : seq 'I_d :=
  [seq i <- enum 'I_d | p i] ++ [seq i <- enum 'I_d | ~~ p i].

Definition paper_main_orientation_order_rank {d : nat} (p : pred 'I_d) : nat :=
  size [seq i <- enum 'I_d | p i].

Lemma paper_main_orientation_order_list_perm {d : nat} (p : pred 'I_d) :
  perm_eq (paper_main_orientation_order_list p) (enum 'I_d).
Proof. by apply/permPl; exact: perm_filterC. Qed.

Lemma paper_main_orientation_order_list_size {d : nat} (p : pred 'I_d) :
  size (paper_main_orientation_order_list p) = d.
Proof. by rewrite (perm_size (paper_main_orientation_order_list_perm p)) size_enum_ord. Qed.

Lemma paper_main_orientation_order_list_uniq {d : nat} (p : pred 'I_d) : uniq (paper_main_orientation_order_list p).
Proof. by rewrite (perm_uniq (paper_main_orientation_order_list_perm p)) enum_uniq. Qed.

Definition paper_main_orientation_order_fun {d : nat} (p : pred 'I_d) (t : 'I_d) : 'I_d :=
  nth t (paper_main_orientation_order_list p) t.

Lemma paper_main_orientation_order_inj {d : nat} (p : pred 'I_d) : injective (paper_main_orientation_order_fun p).
Proof.
move=> t1 t2; rewrite /paper_main_orientation_order_fun.
have Hs := paper_main_orientation_order_list_size p.
have Hu := paper_main_orientation_order_list_uniq p.
have Ht2 : (t2 < size (paper_main_orientation_order_list p))%N by rewrite Hs ltn_ord.
have Ht1 : (t1 < size (paper_main_orientation_order_list p))%N by rewrite Hs ltn_ord.
rewrite [nth t2 _ _](set_nth_default t1 t2 Ht2) => E.
apply/val_inj/eqP; rewrite -(nth_uniq t1 Ht1 Ht2 Hu).
by apply/eqP.
Qed.

Definition paper_main_orientation_order_perm {d : nat} (p : pred 'I_d) : 'S_d :=
  perm (paper_main_orientation_order_inj p).

Lemma paper_main_orientation_order_head {d : nat} (p : pred 'I_d) (t : 'I_d) :
  (t < paper_main_orientation_order_rank p)%N = p (paper_main_orientation_order_perm p t).
Proof.
rewrite permE /paper_main_orientation_order_fun /paper_main_orientation_order_list
  /paper_main_orientation_order_rank nth_cat.
set L1 := [seq i <- enum 'I_d | p i]; set L2 := [seq i <- enum 'I_d | ~~ p i].
case: ifP => Ht.
  have := mem_nth t Ht; rewrite mem_filter => /andP [Hp _].
  by rewrite Hp.
have Hsz := paper_main_orientation_order_list_size p.
rewrite /paper_main_orientation_order_list size_cat -/L1 -/L2 in Hsz.
have Hlt : (t - size L1 < size L2)%N.
  have := ltn_ord t; move: Ht => /negbT; rewrite -leqNgt => /ssrnat.leP Ht /ssrnat.ltP Htd.
  move: Hsz; rewrite -?plusE => Hsz.
  apply/ssrnat.ltP; rewrite -?minusE; lia.
have := mem_nth t Hlt; rewrite mem_filter => /andP [Hnp _].
by rewrite (negbTE Hnp).
Qed.

Lemma paper_main_orientation_order_rank_card {d : nat} (p : pred 'I_d) :
  paper_main_orientation_order_rank p = #|p|.
Proof.
rewrite /paper_main_orientation_order_rank cardE /enum_mem.
rewrite -filter_predI; congr size; apply: eq_filter => x /=.
by rewrite andbT.
Qed.

Lemma paper_main_orientation_order_rank_le {d : nat} (p : pred 'I_d) : (paper_main_orientation_order_rank p <= d)%N.
Proof. by rewrite paper_main_orientation_order_rank_card -[X in (_ <= X)%N](card_ord d) max_card. Qed.


(* 2. Permuting the rows of O and the entries of a. *)

Definition paper_main_orientation_rows {d : nat} (s : 'S_d) (O : 'M[R]_d) : 'M[R]_d :=
  \matrix_(i, j) O (s i) j.

Definition paper_main_orientation_coeffs {d : nat} (s : 'S_d) (a : 'rV[R]_d) : 'rV[R]_d :=
  \row_i a 0 (s i).

Lemma paper_main_orientation_congruence_entry {d : nat} (O : 'M[R]_d) (a : 'rV[R]_d) (j k : 'I_d) :
  (O^T *m diag_mx a *m O) j k = \sum_i O i j * a 0 i * O i k.
Proof.
rewrite mxE; apply: eq_bigr => i _.
by rewrite mul_mx_diag !mxE.
Qed.

Lemma paper_main_orientation_rows_orthogonal {d : nat} (s : 'S_d) (O : 'M[R]_d) :
  O^T *m O = 1%:M ->
  (paper_main_orientation_rows s O)^T *m paper_main_orientation_rows s O = 1%:M.
Proof.
move=> HO; rewrite -HO; apply/matrixP => j k; rewrite !mxE.
rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma paper_main_orientation_rows_congruence {d : nat} (s : 'S_d) (O : 'M[R]_d) (a : 'rV[R]_d) :
  (paper_main_orientation_rows s O)^T *m diag_mx (paper_main_orientation_coeffs s a) *m
    paper_main_orientation_rows s O =
  O^T *m diag_mx a *m O.
Proof.
apply/matrixP => j k; rewrite !paper_main_orientation_congruence_entry.
rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

(* 3. The ordered diagonalization. *)

Theorem paper_main_orientation_spectral_order d (S : 'M[R]_d) (eps : R) :
  paper_main_psd S -> paper_main_frobenius S = 1 -> 0 < eps ->
  exists (r : nat) (O : 'M[R]_d) (a : 'rV[R]_d),
    (r <= d)%N /\ O^T *m O = 1%:M /\ S = O^T *m diag_mx a *m O /\
    (forall i : 'I_d, 0 <= a 0 i) /\
    (forall i : 'I_d, (i < r)%N = (eps < a 0 i)) /\
    r%:R <= 1 / eps ^+ 2 /\
    paper_main_spectral_projection O a eps = paper_main_orientation_projector r O.
Proof.
move=> HS HN He.
have [O [a [HO [HE [Ha Hcard]]]]] := paper_main_unit_spectral_head_cardinality d S eps HS HN He.
set p := fun i : 'I_d => eps < a 0 i.
set s := paper_main_orientation_order_perm p.
set r := paper_main_orientation_order_rank p.
exists r, (paper_main_orientation_rows s O), (paper_main_orientation_coeffs s a).
split; first exact: paper_main_orientation_order_rank_le.
split; first exact: paper_main_orientation_rows_orthogonal.
split; first by rewrite paper_main_orientation_rows_congruence.
split; first by move=> i; rewrite mxE.
have Hhead : forall i : 'I_d, (i < r)%N = (eps < paper_main_orientation_coeffs s a 0 i).
  by move=> i; rewrite mxE (paper_main_orientation_order_head p i).
split; first exact: Hhead.
split.
  rewrite /r paper_main_orientation_order_rank_card.
  have -> : #|p| = #|paper_main_spectral_large a eps|.
    by apply: eq_card => i; rewrite /paper_main_spectral_large inE.
  exact: Hcard.
rewrite /paper_main_spectral_projection /paper_main_spectral_matrix
  /paper_main_orientation_projector.
congr (_ *m diag_mx _ *m _).
have Hhead' : forall i : 'I_d, (i < r)%N = (eps < a 0 (s i)).
  by move=> i; rewrite Hhead mxE.
apply/matrixP => i j; rewrite /paper_main_spectral_mask /paper_main_orientation_mask !mxE.
by rewrite -Hhead'.
Qed.

(* 4. The decomposition in this orientation. *)

Theorem paper_main_orientation_spectral_decomposition d (S : 'M[R]_d) (eps : R) :
  paper_main_psd S -> paper_main_frobenius S = 1 -> 0 < eps ->
  exists (r : nat) (O : 'M[R]_d) (a : 'rV[R]_d),
    (r <= d)%N /\ O^T *m O = 1%:M /\ S = O^T *m diag_mx a *m O /\
    (forall i : 'I_d, (i < r)%N = (eps < a 0 i)) /\ r%:R <= 1 / eps ^+ 2 /\
    S = paper_main_spectral_head O a eps + paper_main_spectral_bulk O a eps /\
    paper_main_psd (paper_main_spectral_head O a eps) /\
    paper_main_psd (paper_main_spectral_bulk O a eps) /\
    paper_main_cone_opnorm_le (paper_main_spectral_bulk O a eps) eps /\
    paper_main_frobenius (paper_main_spectral_head O a eps) <= 1 /\
    paper_main_orientation_projector r O *m paper_main_spectral_head O a eps *m
      paper_main_orientation_projector r O = paper_main_spectral_head O a eps /\
    paper_main_orientation_projector r O *m S = S *m paper_main_orientation_projector r O /\
    (paper_main_orientation_projector r O)^T = paper_main_orientation_projector r O /\
    paper_main_orientation_projector r O *m paper_main_orientation_projector r O =
      paper_main_orientation_projector r O.
Proof.
move=> HS HN He.
have [r [O [a [Hrd [HO [HE [Ha [Hhead [Hr HP]]]]]]]]] :=
  paper_main_orientation_spectral_order d S eps HS HN He.
exists r, O, a.
have [HH [HB HBo]] := paper_main_spectral_positive_bounds d O a eps HO Ha (ltW He).
have HSm : paper_main_spectral_matrix O a = S by rewrite /paper_main_spectral_matrix HE.
do 5 (split => //).
split; first by rewrite paper_main_spectral_split HSm.
do 3 (split => //).
split.
  by have := paper_main_spectral_head_frobenius d O a eps HO; rewrite HSm HN.
rewrite -HP.
split; first exact: paper_main_spectral_head_supported.
split; first by have := paper_main_spectral_projection_commutes d O a eps HO; rewrite HSm.
split; first exact: paper_main_spectral_matrix_symmetric.
exact: paper_main_spectral_projection_square.
Qed.

(* A dimension above 1/eps^2 leaves a positive bulk dimension. *)

Corollary paper_main_orientation_spectral_rank_lt (d r : nat) (eps : R) :
  r%:R <= 1 / eps ^+ 2 -> 1 / eps ^+ 2 < d%:R -> (r < d)%N.
Proof.
move=> Hr Hd.
have H : r%:R < d%:R :> R by apply: le_lt_trans Hr Hd.
by rewrite ltr_nat in H.
Qed.
