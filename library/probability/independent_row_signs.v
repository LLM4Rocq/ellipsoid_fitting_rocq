From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import measurable_realfun numfun lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.comparison Require Import gauss_law gauss_matrix_law.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import symmetric_shift symmetrization.
From GaussianAnalysis.random_matrix Require Import restricted_isometry isotropic_rows.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.

(**md**************************************************************************)
(* # Independent signs of centrally symmetric rows                            *)
(*                                                                            *)
(* Independent row laws, each invariant under negation, give a matrix law     *)
(* invariant under every choice of row signs. The rows may have different    *)
(* laws and dependent coordinates. There are no moment or density hypotheses *)
(* and both the number of rows and the number of columns may be zero.        *)
(*                                                                            *)
(* row_tuple_matrix == the measurable matrix map with the given tuple rows  *)
(* independent_row_matrix_law P k == matrix law of k independent rows P i     *)
(* tuple_row_sign s == multiply the ith tuple row by the ith sign            *)
(* independent_row_sign_invariant == central symmetry of the first k row    *)
(*                                  laws implies reserve_sign_invariant    *)
(*                                                                            *)
(* Source: the row-sign averaging argument of doc/shifted-gaussian.tex.       *)
(* The product-law step is tuple_prod_map, with identity signs outside the   *)
(* finite sample. Gaussian symmetry follows from orthogonal invariance.     *)
(* The final example has two equal coordinates in each row.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section row_symmetry.
Context {R : realType} {d : nat}.

Lemma row_symmetric_sign (P : probability 'rV[R]_d R) (s : bool)
    (A : set 'rV[R]_d) :
  row_symmetric_law P -> measurable A ->
  P ((fun x => rademacher s *: x) @^-1` A) = P A.
Proof.
move=> symP mA; case: s; rewrite /rademacher.
  by under eq_fun do rewrite scale1r.
under eq_fun do rewrite scaleN1r.
exact: symP.
Qed.

Lemma row_symmetric_distribution (P : probability 'rV[R]_d R) e
    (f : {mfun 'rV[R]_d >-> 'rV[R]_e}) :
  row_symmetric_law P -> (forall x, f (- x) = - f x) ->
  row_symmetric_law (distribution P f).
Proof.
move=> symP oddf A mA.
have mfA : measurable (f @^-1` A) := measurable_funPTI f mA.
change (P [set x | A (- f x)] = P (f @^-1` A)).
rewrite -(symP _ mfA); congr (P _); apply/funext => x /=.
by rewrite oddf.
Qed.

Lemma gauss_row_symmetric : row_symmetric_law (@gauss R d).
Proof.
move=> A mA.
have orth : (- (1%:M : 'M[R]_d))^T *m (- (1%:M : 'M[R]_d)) = 1%:M.
  by rewrite mulmxN mulmx1 [(- _)^T]linearN /= trmx1 opprK.
have h := gauss_orthogonal_law orth mA.
rewrite -h; congr (gauss d _); apply/funext => x /=.
by rewrite mulmxN mulmx1.
Qed.

End row_symmetry.

Section independent_rows.
Context {R : realType} {d : nat}.

Definition row_tuple_matrix k :
    {mfun k.-tuple 'rV[R]_d >-> 'M[R]_(k,d)} :=
  HB.pack (fun x : k.-tuple 'rV[R]_d => restricted_isometry.tuple_mx x)
    (isMeasurableFun.Build _ _ _ _ _ measurable_rows_matrix).

Definition independent_row_matrix_law
    (P : nat -> probability 'rV[R]_d R) k : probability 'M[R]_(k,d) R :=
  distribution (tuple_prod P k) (row_tuple_matrix k).

Arguments independent_row_matrix_law P k : clear implicits.

Lemma independent_row_matrix_lawE (P : nat -> probability 'rV[R]_d R) k A :
  independent_row_matrix_law P k A =
  tuple_prod P k ((@restricted_isometry.tuple_mx R k d) @^-1` A).
Proof. by []. Qed.

Definition tuple_row_sign {k} (s : k.-tuple bool) (x : k.-tuple 'rV[R]_d) :=
  tuple_map (fun i (z : 'rV[R]_d) => rademacher (nth true s i) *: z) x.

Lemma measurable_tuple_row_sign k (s : k.-tuple bool) :
  measurable_fun [set: k.-tuple 'rV[R]_d] (tuple_row_sign s).
Proof.
by apply: measurable_tuple_map => i; apply: measurable_scalemx.
Qed.

Lemma tuple_row_sign_matrix k (s : k.-tuple bool) x :
  restricted_isometry.tuple_mx (tuple_row_sign s x) =
  reserve_row_sign s (restricted_isometry.tuple_mx x).
Proof.
apply/matrixP => i j.
by rewrite /tuple_row_sign /tuple_map /restricted_isometry.tuple_mx
  /reserve_row_sign !mxE tnth_mktuple mxE (tnth_nth true).
Qed.

Lemma independent_tuple_row_sign (P : nat -> probability 'rV[R]_d R)
    k (s : k.-tuple bool) A :
  (forall i, (i < k)%N -> row_symmetric_law (P i)) -> measurable A ->
  tuple_prod P k (tuple_row_sign s @^-1` A) = tuple_prod P k A.
Proof.
move=> symP mA; symmetry; apply: tuple_prod_map => //.
  by move=> i; apply: measurable_scalemx => //; exact: measurable_cst.
move=> i B mB; symmetry.
case: (ltnP i k) => ik.
  exact: row_symmetric_sign (symP i ik) mB.
have -> : nth true s i = true by apply: nth_default; rewrite size_tuple.
by under eq_fun do rewrite /rademacher scale1r.
Qed.

Theorem independent_row_sign_invariant
    (P : nat -> probability 'rV[R]_d R) k :
  (forall i, (i < k)%N -> row_symmetric_law (P i)) ->
  reserve_sign_invariant (independent_row_matrix_law P k).
Proof.
move=> symP s A mA; rewrite !independent_row_matrix_lawE.
have mB : measurable ((@restricted_isometry.tuple_mx R k d) @^-1` A) :=
  measurable_funPTI (row_tuple_matrix k) mA.
rewrite -(independent_tuple_row_sign s symP mB).
congr (tuple_prod P k _); apply/funext => x /=.
by rewrite tuple_row_sign_matrix.
Qed.

Theorem reserve_sign_invariant_of_independent_rows
    k (Q : probability 'M[R]_(k,d) R)
    (P : nat -> probability 'rV[R]_d R) :
  (forall A, measurable A ->
    Q A = tuple_prod P k ((@restricted_isometry.tuple_mx R k d) @^-1` A)) ->
  (forall i, (i < k)%N -> row_symmetric_law (P i)) ->
  reserve_sign_invariant Q.
Proof.
move=> lawQ symP s A mA.
have msA : measurable (reserve_row_sign s @^-1` A).
  have h := reserve_row_sign_measurable s measurableT mA.
  by rewrite setTI in h.
rewrite (lawQ _ msA) (lawQ _ mA) -!independent_row_matrix_lawE.
exact: (independent_row_sign_invariant symP s mA).
Qed.

Corollary gauss_independent_row_sign_invariant k :
  reserve_sign_invariant (independent_row_matrix_law (fun=> gauss d) k).
Proof. by apply: independent_row_sign_invariant => i ik; exact: gauss_row_symmetric. Qed.

Lemma gauss_independent_row_matrix_lawE k (A : set 'M[R]_(k,d)) :
  measurable A -> independent_row_matrix_law (fun=> gauss d) k A =
    gauss (k * d) [set a | A (vec_mx a)].
Proof. move=> mA; rewrite independent_row_matrix_lawE; exact: gauss_tuple_mx mA. Qed.

Corollary independent_row_sign_invariant_empty
    (P : nat -> probability 'rV[R]_d R) :
  reserve_sign_invariant (independent_row_matrix_law P 0).
Proof. by apply: independent_row_sign_invariant => i; rewrite ltn0. Qed.

End independent_rows.

Section duplicated_gaussian.
Context {R : realType}.

Lemma measurable_duplicate_row :
  measurable_fun [set: 'rV[R]_1]
    (fun z => const_mx (z 0 0) : 'rV[R]_2).
Proof.
apply/measurable_fun_mxP => i j.
apply: (eq_measurable_fun (fun z : 'rV[R]_1 => z 0 0)).
- by move=> z _; rewrite mxE.
- exact: measurable_mxentry.
Qed.

Definition duplicate_row : {mfun 'rV[R]_1 >-> 'rV[R]_2} :=
  HB.pack (fun z : 'rV[R]_1 => const_mx (z 0 0) : 'rV[R]_2)
    (isMeasurableFun.Build _ _ _ _ _ measurable_duplicate_row).

Lemma duplicate_rowE z (j : 'I_2) : duplicate_row z 0 j = z 0 0.
Proof. by rewrite /duplicate_row /= mxE. Qed.

Lemma duplicate_rowN z : duplicate_row (- z) = - duplicate_row z.
Proof. by apply/matrixP => i j; rewrite /duplicate_row /= !mxE. Qed.

Definition duplicated_gaussian_row : probability 'rV[R]_2 R :=
  distribution (gauss 1) duplicate_row.

Lemma duplicated_gaussian_row_symmetric : row_symmetric_law duplicated_gaussian_row.
Proof.
exact: row_symmetric_distribution (@gauss_row_symmetric R 1) duplicate_rowN.
Qed.

Lemma duplicated_gaussian_row_diagonal :
  duplicated_gaussian_row [set x | x 0 ord0 = x 0 ord_max] = 1%:E.
Proof.
change (gauss 1 [set z : 'rV[R]_1 |
  duplicate_row z 0 ord0 = duplicate_row z 0 ord_max] = 1%:E).
have -> : [set z : 'rV[R]_1 |
  duplicate_row z 0 ord0 = duplicate_row z 0 ord_max] = setT.
  apply/seteqP; split => z /= h.
  - exact: I.
  - by rewrite !duplicate_rowE.
exact: probability_setT.
Qed.

Lemma duplicated_gaussian_coordinate (j : 'I_2) (A : set R) : measurable A ->
  duplicated_gaussian_row [set x | A (x 0 j)] = normal_prob 0 1 A.
Proof.
move=> mA.
change (gauss 1 [set z : 'rV[R]_1 | A (duplicate_row z 0 j)] = normal_prob 0 1 A).
have -> : [set z : 'rV[R]_1 | A (duplicate_row z 0 j)] =
    [set z : 'rV[R]_1 | A (z 0 0)].
  by apply/funext => z; rewrite /= duplicate_rowE.
exact: gauss_coord mA.
Qed.
Corollary duplicated_gaussian_independent_row_signs k :
  reserve_sign_invariant
    (independent_row_matrix_law (fun=> duplicated_gaussian_row) k).
Proof.
by apply: independent_row_sign_invariant => i ik;
  exact: duplicated_gaussian_row_symmetric.
Qed.

End duplicated_gaussian.
