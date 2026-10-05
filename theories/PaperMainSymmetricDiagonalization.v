(* Real orthogonal diagonalization of real symmetric matrices. For every
   symmetric A : 'M[R]_n there are O : 'M[R]_n with O^T O = 1 and a real
   row a : 'rV[R]_n with
     A = O^T diag(a) O.
   Proof by induction on n. For n = k + 1, PaperMainSymmetricDiagonalizationEigen
   gives a unit vector v with A v = l v. The Householder reflection
     H = 1 - 2 / |v - e|^2 (v - e)(v - e)^T,   e = col_mx 1 0,
   is symmetric, H H = 1, H v = e and H e = v (if v = e, then H = 1). So
   M = H A H is symmetric with M e = l e, hence M = block_mx l 0 0 A' with A'
   symmetric of size k. The induction hypothesis for A' and the block matrix
   P = block_mx 1 0 0 O' give O = P H. Consequences, for every column x:
     x^T A x = sum_i a_i ((O x)_i)^2,   trace A = sum_i a_i,
     sum_(i,j) A_ij^2 = sum_i a_i^2,   O O^T = 1,
   and |a_i| <= b when (u^T A w)^2 <= b^2 |u|^2 |w|^2 for all u, w
   (paper_main_cone_opnorm_le A b) and 0 <= b. No spectral theorem,
   complex number, eigenvalue existence or orthogonality is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ring_tactic field_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainConeConditionOperator PaperMainSymmetricDiagonalizationEigen.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* Dot products of columns. *)

Lemma paper_main_symmetric_dotC {N : nat} (u v : 'cV[R]_N) :
  (u^T *m v) 0 0 = (v^T *m u) 0 0.
Proof.
have -> : v^T *m u = (u^T *m v)^T by rewrite trmx_mul trmxK.
by rewrite [in RHS]mxE.
Qed.

Lemma paper_main_symmetric_entryB {m n : nat} (A B : 'M[R]_(m, n)) i j :
  (A - B) i j = A i j - B i j.
Proof. by rewrite [in LHS]mxE [X in _ + X]mxE. Qed.

Lemma paper_main_symmetric_dotBl {N : nat} (u u' v : 'cV[R]_N) :
  ((u - u')^T *m v) 0 0 = (u^T *m v) 0 0 - (u'^T *m v) 0 0.
Proof. by rewrite linearB /= mulmxBl paper_main_symmetric_entryB. Qed.

Lemma paper_main_symmetric_dotBr {N : nat} (u v v' : 'cV[R]_N) :
  (u^T *m (v - v')) 0 0 = (u^T *m v) 0 0 - (u^T *m v') 0 0.
Proof. by rewrite mulmxBr paper_main_symmetric_entryB. Qed.

Lemma paper_main_symmetric_outer_mul {N : nat} (w x : 'cV[R]_N) :
  (w *m w^T) *m x = (w^T *m x) 0 0 *: w.
Proof. by rewrite -mulmxA {1}[w^T *m x]mx11_scalar mul_mx_scalar. Qed.

Lemma paper_main_symmetric_dot_eq0 {N : nat} (w : 'cV[R]_N) :
  (w^T *m w) 0 0 = 0 -> w = 0.
Proof.
by rewrite paper_main_symmetric_sq_dot => H; exact: paper_main_symmetric_sq_eq0.
Qed.

(* The Householder reflection. *)

Definition paper_main_householder {N : nat} (v e : 'cV[R]_N) : 'M[R]_N :=
  1%:M - (2 / ((v - e)^T *m (v - e)) 0 0) *: ((v - e) *m (v - e)^T).

Lemma paper_main_householder_tr {N : nat} (v e : 'cV[R]_N) :
  (paper_main_householder v e)^T = paper_main_householder v e.
Proof.
by rewrite /paper_main_householder linearB /= trmx1 linearZ /= trmx_mul trmxK.
Qed.

Lemma paper_main_householder_same {N : nat} (v e : 'cV[R]_N) :
  ((v - e)^T *m (v - e)) 0 0 = 0 -> v = e /\ paper_main_householder v e = 1%:M.
Proof.
move=> Hs; have Hw := paper_main_symmetric_dot_eq0 _ Hs.
split; first by apply/eqP; rewrite -subr_eq0 Hw.
by rewrite /paper_main_householder Hw mul0mx scaler0 subr0.
Qed.

Lemma paper_main_householder_apply {N : nat} (v e : 'cV[R]_N) :
  (v^T *m v) 0 0 = 1 -> (e^T *m e) 0 0 = 1 ->
  paper_main_householder v e *m v = e /\ paper_main_householder v e *m e = v.
Proof.
move=> Hv He.
set s := ((v - e)^T *m (v - e)) 0 0.
have [Hs0 | Hs0] := eqVneq s 0.
  have [-> ->] := paper_main_householder_same _ _ Hs0.
  by rewrite !mul1mx.
set t := (e^T *m v) 0 0.
have Hve : (v^T *m e) 0 0 = t by rewrite paper_main_symmetric_dotC.
have Hwv : ((v - e)^T *m v) 0 0 = 1 - t by rewrite paper_main_symmetric_dotBl Hv.
have Hwe : ((v - e)^T *m e) 0 0 = t - 1 by rewrite paper_main_symmetric_dotBl He Hve.
have Hs : s = 2 - 2 * t.
  by rewrite /s paper_main_symmetric_dotBr Hwv Hwe; ring.
have Hc1 : 2 / s * (1 - t) = 1.
  have H2 : 1 - t = s / 2 by rewrite Hs; field.
  by rewrite H2; field; exact: Hs0.
rewrite /paper_main_householder -/s.
set W := (v - e) *m (v - e)^T.
rewrite !mulmxBl !mul1mx -!scalemxAl /W !paper_main_symmetric_outer_mul Hwv Hwe.
rewrite !scalerA Hc1 scale1r.
split; first by rewrite subKr.
have -> : 2 / s * (t - 1) = - 1 by rewrite -opprB mulrN Hc1.
by rewrite scaleN1r opprK addrC subrK.
Qed.

Lemma paper_main_householder_involutive {N : nat} (v e : 'cV[R]_N) :
  paper_main_householder v e *m paper_main_householder v e = 1%:M.
Proof.
set s := ((v - e)^T *m (v - e)) 0 0.
have [Hs0 | Hs0] := eqVneq s 0.
  by have [_ ->] := paper_main_householder_same _ _ Hs0; rewrite mul1mx.
set W := (v - e) *m (v - e)^T.
have HWW : W *m W = s *: W.
  by rewrite /W mulmxA paper_main_symmetric_outer_mul -scalemxAl.
rewrite /paper_main_householder -/s -/W.
rewrite mulmxBl mul1mx mulmxBr mulmx1 -scalemxAl -scalemxAr HWW !scalerA.
have Hc : 2 / s * (2 / s) * s = 2 / s + 2 / s by field.
rewrite Hc scalerDl.
set X := (2 / s) *: W.
by rewrite opprB addrK subrK.
Qed.

(* Symmetric matrices with the first basis vector as eigenvector. *)

Lemma paper_main_symmetric_block_of_eigen k (M : 'M[R]_(1 + k)) (l : R) :
  M^T = M -> M *m col_mx (1%:M : 'cV[R]_1) 0 = l *: col_mx (1%:M : 'cV[R]_1) 0 ->
  M = block_mx (l%:M : 'M[R]_1) 0 0 (drsubmx M) /\ (drsubmx M)^T = drsubmx M.
Proof.
move=> HT He.
have HB := submxK M.
move: He; rewrite -{1}HB mul_block_col !mulmx1 !mulmx0 !addr0 scale_col_mx.
move=> /eq_col_mx [Hul Hdl].
have Hur : ursubmx M = 0.
  have := HT; rewrite -{1 2}HB tr_block_mx => /eq_block_mx [_ H _ _].
  by rewrite -H Hdl scaler0 trmx0.
have Hdr : (drsubmx M)^T = drsubmx M.
  by have := HT; rewrite -{1 2}HB tr_block_mx => /eq_block_mx [_ _ _ H].
split=> //.
rewrite -{1}HB Hur Hdl scaler0; congr block_mx.
by rewrite Hul -[l *: 1%:M]mul_mx_scalar mul1mx.
Qed.

(* Diagonal matrices. *)

Lemma paper_main_symmetric_diag1 (l : R) :
  diag_mx (l%:M : 'rV[R]_1) = (l%:M : 'M[R]_1).
Proof. by apply/matrixP => i j; rewrite !ord1 !mxE eqxx. Qed.

Lemma paper_main_symmetric_block1 k (O' : 'M[R]_k) :
  (block_mx (1%:M : 'M[R]_1) 0 0 O')^T *m block_mx (1%:M : 'M[R]_1) 0 0 O' =
  block_mx (1%:M : 'M[R]_1) 0 0 (O'^T *m O').
Proof.
rewrite tr_block_mx !trmx0 trmx1 mulmx_block.
by rewrite !mulmx0 !mul0mx !mulmx1 !addr0 !add0r.
Qed.

(* The orthogonal diagonalization. *)

Theorem paper_main_symmetric_diagonalization n (A : 'M[R]_n) :
  paper_main_symmetric A ->
  exists (O : 'M[R]_n) (a : 'rV[R]_n), O^T *m O = 1%:M /\ A = O^T *m diag_mx a *m O.
Proof.
elim: n A => [|k IH] A HA.
  exists 1%:M, 0; split; first by rewrite trmx1 mulmx1.
  by apply/matrixP => i; case: i.
have [v [Hv1 [Hev _]]] := paper_main_symmetric_eigenvector _ _ HA.
set l := paper_main_quadratic_form A v in Hev.
have HAt : A^T = A by apply/paper_main_symmetricP.
pose e : 'cV[R]_(1 + k) := col_mx (1%:M : 'cV[R]_1) 0.
have He1 : (e^T *m e) 0 0 = 1.
  by rewrite /e tr_col_mx mul_row_col trmx1 mulmx1 trmx0 mul0mx addr0 mxE eqxx.
have Hv1' : (v^T *m v) 0 0 = 1 by rewrite paper_main_symmetric_sq_dot.
pose H : 'M[R]_(1 + k) := paper_main_householder v e.
have [Hve Hev'] := paper_main_householder_apply _ _ Hv1' He1.
have HHt : H^T = H by exact: paper_main_householder_tr.
have HHH : H *m H = 1%:M by exact: paper_main_householder_involutive.
pose M : 'M[R]_(1 + k) := H *m A *m H.
have HMt : M^T = M by rewrite /M !trmx_mul HHt HAt mulmxA.
have HMe : M *m e = l *: e.
  by rewrite /M -!mulmxA Hev' Hev -scalemxAr Hve.
have [HMb HMdr] := paper_main_symmetric_block_of_eigen _ _ _ HMt HMe.
have HA' : paper_main_symmetric (drsubmx M) by apply/paper_main_symmetricP.
have [O' [a' [HO' HA'd]]] := IH _ HA'.
pose P : 'M[R]_(1 + k) := block_mx (1%:M : 'M[R]_1) 0 0 O'.
exists (P *m H), (row_mx (l%:M : 'rV[R]_1) a'); split.
  rewrite trmx_mul HHt mulmxA -(mulmxA H) paper_main_symmetric_block1 HO'.
  by rewrite -scalar_mx_block mulmx1 HHH.
have HPDP : P^T *m diag_mx (row_mx (l%:M : 'rV[R]_1) a') *m P = M.
  rewrite diag_mx_row paper_main_symmetric_diag1 /P tr_block_mx !trmx0 trmx1.
  rewrite !mulmx_block !mulmx0 !mul0mx !mulmx1 !mul1mx !addr0 !add0r mul0mx.
  by rewrite -HA'd {2}HMb.
rewrite trmx_mul HHt.
have -> : H *m P^T *m diag_mx (row_mx l%:M a') *m (P *m H) =
    H *m (P^T *m diag_mx (row_mx l%:M a') *m P) *m H by rewrite !mulmxA.
by rewrite HPDP /M !mulmxA HHH mul1mx -mulmxA HHH mulmx1.
Qed.

(* Consequences. *)

Lemma paper_main_symmetric_orthogonal_tr n (O : 'M[R]_n) :
  O^T *m O = 1%:M -> O *m O^T = 1%:M.
Proof. exact: mulmx1C. Qed.

Lemma paper_main_symmetric_diag_form n (a : 'rV[R]_n) (y : 'cV[R]_n) :
  paper_main_quadratic_form (diag_mx a) y = \sum_(i < n) a 0 i * y i 0 ^+ 2.
Proof.
rewrite /paper_main_quadratic_form; apply: eq_bigr => i _.
rewrite (bigD1 i) //= big1.
- by move=> j Hj; rewrite mxE eq_sym (negbTE Hj) mulr0n mulr0 mul0r.
- by rewrite mxE eqxx mulr1n addr0 expr2; ring.
Qed.

Theorem paper_main_symmetric_form_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  A = O^T *m diag_mx a *m O ->
  forall x : 'cV[R]_n,
    paper_main_quadratic_form A x = \sum_(i < n) a 0 i * (O *m x) i 0 ^+ 2.
Proof.
move=> HA x.
rewrite -paper_main_symmetric_diag_form !paper_main_quadratic_formE HA.
by rewrite trmx_mul !mulmxA.
Qed.

Theorem paper_main_symmetric_trace_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  paper_main_trace A = \sum_(i < n) a 0 i.
Proof.
move=> HO HA.
have HO' := paper_main_symmetric_orthogonal_tr _ _ HO.
rewrite /paper_main_trace -/(mxtrace A) HA mxtrace_mulC.
by rewrite mulmxA HO' mul1mx mxtrace_diag.
Qed.

Theorem paper_main_symmetric_frobenius_diagonal n (A O : 'M[R]_n) (a : 'rV[R]_n) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  paper_main_pairing A A = \sum_(i < n) a 0 i ^+ 2.
Proof.
move=> HO HA.
have HO' := paper_main_symmetric_orthogonal_tr _ _ HO.
have Htr : paper_main_pairing A A = \tr (A *m A^T).
  rewrite /paper_main_pairing; apply: eq_bigr => i _.
  by rewrite mxE; apply: eq_bigr => j _; rewrite mxE.
have HAt : A^T = A by rewrite HA !trmx_mul trmxK mulmxA tr_diag_mx.
rewrite Htr HAt.
have -> : A *m A = O^T *m (diag_mx a *m diag_mx a) *m O.
  by rewrite HA -!mulmxA (mulmxA O) HO' mul1mx.
rewrite mxtrace_mulC [O *m _]mulmxA HO' mul1mx.
rewrite /mxtrace; apply: eq_bigr => i _.
rewrite mxE (bigD1 i) //= big1.
- by move=> j Hj; rewrite [diag_mx a i j]mxE eq_sym (negbTE Hj) mulr0n mul0r.
- by rewrite !mxE eqxx !mulr1n addr0 expr2.
Qed.

Theorem paper_main_symmetric_coefficient_bound n (A O : 'M[R]_n) (a : 'rV[R]_n) (b : R) :
  O^T *m O = 1%:M -> A = O^T *m diag_mx a *m O ->
  0 <= b -> paper_main_cone_opnorm_le A b ->
  forall i : 'I_n, `|a 0 i| <= b.
Proof.
move=> HO HA Hb HB i.
have HO' := paper_main_symmetric_orthogonal_tr _ _ HO.
pose u : 'cV[R]_n := O^T *m delta_mx i 0.
have Hu : (u^T *m u) 0 0 = 1.
  rewrite /u trmx_mul trmxK mulmxA -(mulmxA _ O) HO' mulmx1 trmx_delta.
  by rewrite mul_delta_mx mxE !eqxx.
have HAu : (u^T *m A *m u) 0 0 = a 0 i.
  rewrite /u HA trmx_mul trmxK !mulmxA -(mulmxA _ O) HO' mulmx1.
  rewrite -(mulmxA _ O) HO' mulmx1 trmx_delta.
  by rewrite -rowE -colE !mxE eqxx mulr1n.
have H := HB u u; rewrite HAu Hu !mulr1 in H.
by rewrite -sqrtr_sqr -(ger0_norm Hb) -sqrtr_sqr; apply: ler_wsqrtr.
Qed.
