From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets reals.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.

(**md**************************************************************************)
(* # The operator norm of real matrices                                       *)
(*                                                                            *)
(* The operator norm of A : 'M[R]_(m, n) is its norm as a linear map          *)
(* x |-> A *m x from 'cV[R]_n to 'cV[R]_m, both with the Euclidean norm       *)
(* frobenius. It is characterized by the inequality                           *)
(* frobenius (A *m x) <= b * frobenius x (opnorm_leP) and by the bilinear     *)
(* inequality `|mxdot y (A *m x)| <= b * frobenius y * frobenius x            *)
(* (opnorm_bilinearP). For a symmetric matrix, it is the smallest b such that *)
(* `|mxdot x (A *m x)| <= b * mxdot x x for every x (opnorm_symP), and the    *)
(* largest absolute value of an eigenvalue (opnorm_spectral).                 *)
(*                                                                            *)
(* ```                                                                        *)
(*   opnorm A == the operator norm of A, the supremum of frobenius (A *m x)   *)
(*               over the columns x with frobenius x <= 1                     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section opnorm.
Variable R : realType.
Implicit Types m n p : nat.

Definition opnorm m n (A : 'M[R]_(m, n)) : R :=
  sup [set frobenius (A *m x) | x in [set x : 'cV[R]_n | frobenius x <= 1]].

Lemma opnorm_has_sup m n (A : 'M[R]_(m, n)) :
  has_sup [set frobenius (A *m x) | x in [set x : 'cV[R]_n | frobenius x <= 1]].
Proof.
split.
  by exists (frobenius (A *m (0 : 'cV[R]_n))), 0; rewrite //= frobenius0 ler01.
exists (frobenius A) => _ [x /= x1 <-].
rewrite (le_trans (frobenius_mulmx _ _)) // -[leRHS]mulr1.
by rewrite ler_wpM2l ?frobenius_ge0.
Qed.

Lemma opnorm_ub m n (A : 'M[R]_(m, n)) (x : 'cV[R]_n) :
  frobenius x <= 1 -> frobenius (A *m x) <= opnorm A.
Proof. by move=> x1; apply: (ub_le_sup (proj2 (opnorm_has_sup A))); exists x. Qed.

Lemma opnorm_le m n (A : 'M[R]_(m, n)) (b : R) :
  (forall x : 'cV[R]_n, frobenius x <= 1 -> frobenius (A *m x) <= b) ->
  opnorm A <= b.
Proof.
move=> Ab; apply: ge_sup; first exact: (proj1 (opnorm_has_sup A)).
by move=> _ [x /= x1 <-]; exact: Ab.
Qed.

Lemma opnorm_ge0 m n (A : 'M[R]_(m, n)) : 0 <= opnorm A.
Proof.
by have := @opnorm_ub _ _ A 0; rewrite frobenius0 mulmx0 frobenius0 ler01; apply.
Qed.

Lemma opnorm_le_frobenius m n (A : 'M[R]_(m, n)) : opnorm A <= frobenius A.
Proof.
apply: opnorm_le => x x1; rewrite (le_trans (frobenius_mulmx _ _)) //.
by rewrite -[leRHS]mulr1 ler_wpM2l ?frobenius_ge0.
Qed.

Lemma frobenius_mulmx_opnorm m n (A : 'M[R]_(m, n)) (x : 'cV[R]_n) :
  frobenius (A *m x) <= opnorm A * frobenius x.
Proof.
have [->|x0] := eqVneq x 0; first by rewrite mulmx0 !frobenius0 mulr0.
have xp : 0 < frobenius x by rewrite frobenius_gt0.
have x1 : frobenius ((frobenius x)^-1 *: x) <= 1.
  by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
have := opnorm_ub A x1.
by rewrite -scalemxAr frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulrC ler_pdivrMr.
Qed.

Lemma opnorm_leP m n (A : 'M[R]_(m, n)) (b : R) : 0 <= b ->
  (forall x : 'cV[R]_n, frobenius (A *m x) <= b * frobenius x) <-> opnorm A <= b.
Proof.
move=> b0; split=> [Ab|Ab x].
  apply: opnorm_le => x x1; apply: le_trans (Ab x) _.
  by rewrite -[leRHS]mulr1 ler_wpM2l.
by apply: le_trans (frobenius_mulmx_opnorm A x) _; rewrite ler_wpM2r ?frobenius_ge0.
Qed.

Lemma mxdot_col m n (A B : 'M[R]_(m, n)) :
  mxdot A B = \sum_k mxdot (col k A) (col k B).
Proof.
rewrite /mxdot exchange_big /=; apply: eq_bigr => k _.
by apply: eq_bigr => i _; rewrite big_ord1 !mxE.
Qed.

Lemma frobenius_mulmx_mx_opnorm m n p (A : 'M[R]_(m, n)) (X : 'M[R]_(n, p)) :
  frobenius (A *m X) <= opnorm A * frobenius X.
Proof.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 ?opnorm_ge0 // exprMn.
rewrite !frobenius_sqr !mxdot_col mulr_sumr; apply: ler_sum => k _.
have -> : col k (A *m X) = A *m col k X by rewrite !colE mulmxA.
rewrite -!frobenius_sqr -exprMn ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 ?opnorm_ge0 //.
exact: frobenius_mulmx_opnorm.
Qed.

Lemma opnorm0 m n : opnorm (0 : 'M[R]_(m, n)) = 0.
Proof.
apply/le_anti; rewrite opnorm_ge0 andbT.
by rewrite (le_trans (opnorm_le_frobenius _)) // frobenius0.
Qed.

Lemma opnormZ m n a (A : 'M[R]_(m, n)) : opnorm (a *: A) = `|a| * opnorm A.
Proof.
have le_scale c (B : 'M[R]_(m, n)) : opnorm (c *: B) <= `|c| * opnorm B.
  apply/opnorm_leP => [|x]; first by rewrite mulr_ge0 ?opnorm_ge0.
  rewrite -scalemxAl frobeniusZ -mulrA ler_wpM2l //.
  exact: frobenius_mulmx_opnorm.
have [->|a0] := eqVneq a 0; first by rewrite scale0r opnorm0 normr0 mul0r.
apply/le_anti; rewrite le_scale /=.
have := le_scale a^-1 (a *: A); rewrite scalerA mulVf // scale1r normrV ?unitfE //.
by rewrite ler_pdivlMl ?normr_gt0.
Qed.

Lemma opnormN m n (A : 'M[R]_(m, n)) : opnorm (- A) = opnorm A.
Proof. by rewrite -scaleN1r opnormZ normrN1 mul1r. Qed.

Lemma opnormD m n (A B : 'M[R]_(m, n)) : opnorm (A + B) <= opnorm A + opnorm B.
Proof.
apply/opnorm_leP => [|x]; first by rewrite addr_ge0 ?opnorm_ge0.
rewrite mulmxDl mulrDl (le_trans (frobeniusD _ _)) //.
by rewrite lerD ?frobenius_mulmx_opnorm.
Qed.

Lemma opnorm_mulmx m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  opnorm (A *m B) <= opnorm A * opnorm B.
Proof.
apply/opnorm_leP => [|x]; first by rewrite mulr_ge0 ?opnorm_ge0.
rewrite -mulmxA (le_trans (frobenius_mulmx_opnorm _ _)) // -mulrA.
by rewrite ler_wpM2l ?opnorm_ge0 ?frobenius_mulmx_opnorm.
Qed.

Lemma mxdot_opnorm m n (A : 'M[R]_(m, n)) (y : 'cV[R]_m) (x : 'cV[R]_n) :
  `|mxdot y (A *m x)| <= opnorm A * frobenius y * frobenius x.
Proof.
rewrite (le_trans (mxdot_le _ _)) // [opnorm A * _]mulrC -mulrA.
by rewrite ler_wpM2l ?frobenius_ge0 ?frobenius_mulmx_opnorm.
Qed.

Lemma opnorm_bilinearP m n (A : 'M[R]_(m, n)) (b : R) : 0 <= b ->
  (forall (y : 'cV[R]_m) (x : 'cV[R]_n),
    `|mxdot y (A *m x)| <= b * frobenius y * frobenius x) <->
  opnorm A <= b.
Proof.
move=> b0; split=> [Ab|Ab y x]; last first.
  by apply: le_trans (mxdot_opnorm _ _ _) _; rewrite !ler_wpM2r ?frobenius_ge0.
apply/opnorm_leP => // x; have := Ab (A *m x) x.
rewrite -frobenius_sqr ger0_norm ?sqr_ge0 // expr2.
have [->|Ax0] := eqVneq (frobenius (A *m x)) 0; first by rewrite mulr_ge0 ?frobenius_ge0.
by rewrite [b * _]mulrC -mulrA ler_pM2l // lt_def Ax0 frobenius_ge0.
Qed.

Lemma opnorm_trmx m n (A : 'M[R]_(m, n)) : opnorm A^T = opnorm A.
Proof.
have le_tr p q (B : 'M[R]_(p, q)) : opnorm B^T <= opnorm B.
  apply/opnorm_bilinearP => [|y x]; first exact: opnorm_ge0.
  by rewrite mxdotC mxdot_mulmxl trmxK mulrAC mxdot_opnorm.
by apply/le_anti; rewrite le_tr /= -{1}[A]trmxK le_tr.
Qed.

Lemma opnorm_orthogonalmxl m n (P : 'M[R]_m) (A : 'M[R]_(m, n)) :
  P \is orthogonalmx -> opnorm (P *m A) = opnorm A.
Proof.
move=> Po; congr sup; apply/seteqP; split=> _ [x x1 <-]; exists x => //.
  by rewrite -mulmxA frobenius_orthogonalmxl.
by rewrite -mulmxA frobenius_orthogonalmxl.
Qed.

Lemma opnorm_orthogonalmxr m n (A : 'M[R]_(m, n)) (Q : 'M[R]_n) :
  Q \is orthogonalmx -> opnorm (A *m Q) = opnorm A.
Proof.
move=> Qo; congr sup; apply/seteqP; split=> _ [x /= x1 <-].
  by exists (Q *m x); rewrite ?mulmxA //= frobenius_orthogonalmxl.
exists (Q^T *m x); first by rewrite /= frobenius_orthogonalmxl ?trmx_orthogonal.
by rewrite mulmxA -(mulmxA A) (orthogonalmxP _ Qo) mulmx1.
Qed.

Lemma opnorm_symP n (A : 'M[R]_n) (b : R) : A \is symmetricmx -> 0 <= b ->
  (forall x : 'cV[R]_n, `|mxdot x (A *m x)| <= b * mxdot x x) <-> opnorm A <= b.
Proof.
move=> Asym b0; split=> [Ab|Ab x]; last first.
  apply: le_trans (mxdot_opnorm _ _ _) _.
  by rewrite -mulrA -expr2 frobenius_sqr ler_wpM2r ?mxdot_ge0.
have [P Po [d AE]] := symmetric_spectral Asym.
have db i : `|d 0 i| <= b := proj1 (spectral_form_abs b Po AE) Ab i.
apply/opnorm_leP => // x.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // exprMn !frobenius_sqr.
rewrite AE -!mulmxA mxdot_orthogonalmxl ?trmx_orthogonal //.
rewrite -(mxdot_orthogonalmxl x x Po) /mxdot mulr_sumr; apply: ler_sum => i _.
rewrite !big_ord1 mul_diag_mx mxE mulrACA -!expr2 ler_wpM2r ?sqr_ge0 //.
by rewrite -real_normK ?num_real // ler_sqr ?nnegrE.
Qed.

Lemma opnorm_spectral n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  opnorm A = \big[Num.max/0]_i `|d 0 i|.
Proof.
move=> Po AE; have Asym : A \is symmetricmx.
  rewrite AE -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
have M0 : 0 <= \big[Num.max/0]_i `|d 0 i|.
  by elim/big_rec: _ => // i x _ x0; rewrite le_max x0 orbT.
apply/le_anti/andP; split.
  apply/(opnorm_symP Asym M0)/(spectral_form_abs _ Po AE) => i.
  by rewrite (bigD1 i) //= le_max lexx.
elim/big_rec: _ => [|i x _ xA]; first exact: opnorm_ge0.
rewrite ge_max xA andbT; have := mxdot_opnorm A (row i P)^T (row i P)^T.
rewrite (spectral_eigenvector _ Po AE) mxdotZr orthogonalmx_row_unit // mulr1.
by rewrite -mulrA -expr2 frobenius_sqr orthogonalmx_row_unit // mulr1.
Qed.

End opnorm.
