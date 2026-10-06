(* Entrywise transport between the calculus matrices and the public matrices.
   matrix n and 'M[R]_(S n) have the same positive true dimension. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct normedtype.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Tensor.Definitions Matrix.FrobeniusNorm
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_matrix_to_public n (A : Matrix.Definitions.matrix n) : 'M[R]_(S n) :=
  \matrix_(i,j) matrix_entry n A i j.

Definition paper_main_matrix_from_public n (A : 'M[R]_(S n)) : Matrix.Definitions.matrix n :=
  matrix_build n (fun i j => A (inord i) (inord j)).

Lemma paper_main_matrix_to_public_entry n A (i j : 'I_(S n)) :
  paper_main_matrix_to_public n A i j = matrix_entry n A i j.
Proof.
by rewrite /paper_main_matrix_to_public mxE.
Qed.

Lemma paper_main_matrix_from_public_entry n (A : 'M[R]_(S n)) (i j : 'I_(S n)) :
  matrix_entry n (paper_main_matrix_from_public n A) i j = A i j.
Proof.
unfold paper_main_matrix_from_public.
rewrite matrix_entry_build.
- have H := elimT ssrnat.ltP (ltn_ord i); lia.
- have H := elimT ssrnat.ltP (ltn_ord j); lia.
- by rewrite !inord_val.
Qed.

Lemma paper_main_matrix_public_roundtrip n (A : 'M[R]_(S n)) :
  paper_main_matrix_to_public n (paper_main_matrix_from_public n A) = A.
Proof.
apply/matrixP => i j.
by rewrite paper_main_matrix_to_public_entry paper_main_matrix_from_public_entry.
Qed.

Lemma paper_main_matrix_public_symmetric n (A : Matrix.Definitions.matrix n) :
  symmetric_matrix n A -> paper_main_symmetric (paper_main_matrix_to_public n A).
Proof.
intros H i j.
rewrite !paper_main_matrix_to_public_entry.
apply H; have Hi := elimT ssrnat.ltP (ltn_ord i); have Hj := elimT ssrnat.ltP (ltn_ord j); lia.
Qed.

Lemma paper_main_matrix_internal_symmetric n (A : 'M[R]_(S n)) :
  paper_main_symmetric A -> symmetric_matrix n (paper_main_matrix_from_public n A).
Proof.
intros H i j Hi Hj.
unfold paper_main_matrix_from_public.
rewrite !matrix_entry_build; try assumption.
apply H.
Qed.

Lemma paper_main_matrix_coordinate_sum n f :
  coordinate_sum n f = (\sum_(i < S n) f i)%R.
Proof.
elim: n f => [|n IH] f.
- by rewrite big_ord1.
- rewrite big_ord_recl /=.
  change (f 0%nat + coordinate_sum n (fun i => f (S i)) = f 0%nat + (\sum_(i < S n) f (S i))%R).
  by rewrite IH.
Qed.

Lemma paper_main_matrix_public_pairing n (A B : Matrix.Definitions.matrix n) :
  symmetric_matrix n B ->
  trace_pair n A B = paper_main_pairing (paper_main_matrix_to_public n A) (paper_main_matrix_to_public n B).
Proof.
intro HB.
unfold trace_pair, paper_main_pairing.
rewrite paper_main_matrix_coordinate_sum.
apply: eq_bigr => i _; rewrite paper_main_matrix_coordinate_sum.
apply: eq_bigr => j _; rewrite !paper_main_matrix_to_public_entry.
have Hi : Nat.le i n by have H := elimT ssrnat.ltP (ltn_ord i); lia.
have Hj : Nat.le j n by have H := elimT ssrnat.ltP (ltn_ord j); lia.
by rewrite (HB j i Hj Hi).
Qed.

Lemma paper_main_matrix_public_frobenius n (A : Matrix.Definitions.matrix n) :
  (`|A|)%R = paper_main_frobenius (paper_main_matrix_to_public n A).
Proof.
have Hsquare : (`|A|)%R^2 = paper_main_pairing (paper_main_matrix_to_public n A) (paper_main_matrix_to_public n A).
{ rewrite matrix_frobenius_norm_squared /paper_main_pairing paper_main_matrix_coordinate_sum.
  apply: eq_bigr => i _; rewrite paper_main_matrix_coordinate_sum.
  apply: eq_bigr => j _; rewrite !paper_main_matrix_to_public_entry.
  change ((matrix_entry n A i j)^2 = matrix_entry n A i j*matrix_entry n A i j); ring. }
have HP := paper_main_pairing_self_ge0 (S n) (paper_main_matrix_to_public n A).
have HR := sqr_sqrtr HP.
rewrite expr2 in HR.
change (paper_main_frobenius (paper_main_matrix_to_public n A) * paper_main_frobenius (paper_main_matrix_to_public n A) = paper_main_pairing (paper_main_matrix_to_public n A) (paper_main_matrix_to_public n A)) in HR.
have HA : 0 <= (`|A|)%R by apply/RleP; apply normr_ge0.
have HB : 0 <= paper_main_frobenius (paper_main_matrix_to_public n A) by apply/RleP; apply sqrtr_ge0.
nra.
Qed.

Lemma paper_main_matrix_internal_frobenius n (A : 'M[R]_(S n)) :
  (`|paper_main_matrix_from_public n A|)%R = paper_main_frobenius A.
Proof.
by rewrite paper_main_matrix_public_frobenius paper_main_matrix_public_roundtrip.
Qed.
