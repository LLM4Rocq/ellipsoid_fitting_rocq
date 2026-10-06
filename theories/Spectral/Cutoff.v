(* A positive spectral decomposition and the cardinality of a fixed-cutoff head. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Spectral.SymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Theorem paper_main_positive_diagonalization d (S : 'M[R]_d) : paper_main_psd S ->
  exists (O : 'M[R]_d) (a : 'rV[R]_d), O^T *m O = 1%:M /\
    S = O^T *m diag_mx a *m O /\ (forall i : 'I_d, 0<=a 0 i) /\
    (\sum_(i<d) a 0 i ^+ 2) = paper_main_frobenius S ^+ 2.
Proof.
move=> [HS HP].
have [O [a [HO HE]]] := paper_main_symmetric_diagonalization d S HS.
exists O, a; split=> //; split=> //; split.
  apply/(spectral_psd (paper_main_symmetric_orthogonalmx _ HO) HE) => x.
  by rewrite -paper_main_quadratic_form_mxdot.
by rewrite pmh_frobenius_sqr (paper_main_symmetric_frobenius_diagonal d S O a HO HE).
Qed.

Definition paper_main_spectral_large {d} (a : 'rV[R]_d) eps : {set 'I_d} :=
  [set i | eps<a 0 i].
Definition paper_main_spectral_head_coeff {d} (a : 'rV[R]_d) eps : 'rV[R]_d :=
  \row_i if eps<a 0 i then a 0 i else 0.
Definition paper_main_spectral_bulk_coeff {d} (a : 'rV[R]_d) eps : 'rV[R]_d :=
  \row_i if eps<a 0 i then 0 else a 0 i.
Definition paper_main_spectral_mask {d} (a : 'rV[R]_d) eps : 'rV[R]_d :=
  \row_i if eps<a 0 i then 1 else 0.

Lemma paper_main_spectral_coeff_split d (a : 'rV[R]_d) eps :
  paper_main_spectral_head_coeff a eps+paper_main_spectral_bulk_coeff a eps = a.
Proof.
apply/matrixP=> i j; have -> : i = 0 by apply: ord1.
by rewrite !mxE; case: ifP=>_; rewrite ?addr0 ?add0r.
Qed.

Lemma paper_main_spectral_bulk_bounds d (a : 'rV[R]_d) eps :
  (forall i, 0<=a 0 i) -> 0<=eps ->
  forall i, 0<=paper_main_spectral_head_coeff a eps 0 i /\
    0<=paper_main_spectral_bulk_coeff a eps 0 i<=eps.
Proof.
move=> Ha He i; rewrite /paper_main_spectral_head_coeff /paper_main_spectral_bulk_coeff !mxE.
case: ifP=>H.
- split; first exact: Ha.
  by apply/andP; split.
- split; first exact: lexx.
  apply/andP; split; first exact: Ha.
  by rewrite leNgt H.
Qed.

Theorem paper_main_spectral_head_cardinality d (a : 'rV[R]_d) eps : 0<=eps ->
  (#|paper_main_spectral_large a eps|)%:R*eps^+2<=\sum_(i<d) a 0 i^+2.
Proof.
move=> He.
have E : (#|paper_main_spectral_large a eps|)%:R*eps^+2 =
  \sum_(i in paper_main_spectral_large a eps) eps^+2.
  by rewrite sumr_const mulr_natl.
rewrite E big_mkcond; apply: ler_sum=>i _.
case: ifP=>Hi; last exact: sqr_ge0.
have HH : eps<a 0 i by move: Hi; rewrite inE.
nra.
Qed.

Corollary paper_main_unit_spectral_head_cardinality d (S : 'M[R]_d) eps :
  paper_main_psd S -> paper_main_frobenius S = 1 -> 0<eps ->
  exists (O : 'M[R]_d) (a : 'rV[R]_d), O^T *m O = 1%:M /\
    S = O^T *m diag_mx a *m O /\ (forall i : 'I_d, 0<=a 0 i) /\
    (#|paper_main_spectral_large a eps|)%:R<=1/(eps^+2).
Proof.
move=> HS HN He; have [O [a [HO [HE [Ha Hsum]]]]] := paper_main_positive_diagonalization d S HS.
exists O,a; split=> //; split=> //; split=> //.
have H := paper_main_spectral_head_cardinality d a eps (ltW He).
rewrite Hsum HN expr1n in H.
by rewrite ler_pdivlMr ?exprn_gt0.
Qed.
