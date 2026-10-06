From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix ring_tactic.

(**md**************************************************************************)
(* # The Euclidean structure of real matrices                                 *)
(*                                                                            *)
(* The Frobenius inner product and norm of rectangular matrices, and          *)
(* orthogonal matrices. On row and column vectors, the Frobenius inner        *)
(* product and norm are the Euclidean inner product and norm.                 *)
(*                                                                            *)
(* ```                                                                        *)
(*           mxdot A B == the Frobenius inner product of A, B : 'M[R]_(m, n), *)
(*                        \sum_i \sum_j A i j * B i j                         *)
(*         frobenius A == the Frobenius norm Num.sqrt (mxdot A A) of A; the   *)
(*                        Euclidean norm when A is a row or a column vector   *)
(*  M \is orthogonalmx == the square matrix M is orthogonal: M *m M^T = 1     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section mxdot.
Variable R : comNzRingType.
Implicit Types m n p : nat.

Definition mxdot m n (A B : 'M[R]_(m, n)) : R := \sum_i \sum_j A i j * B i j.

Lemma mxdotC m n (A B : 'M[R]_(m, n)) : mxdot A B = mxdot B A.
Proof. by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite mulrC. Qed.

Lemma mxdotDl m n (A B C : 'M[R]_(m, n)) :
  mxdot (A + B) C = mxdot A C + mxdot B C.
Proof.
rewrite /mxdot -big_split /=; apply: eq_bigr => i _.
by rewrite -big_split /=; apply: eq_bigr => j _; rewrite mxE mulrDl.
Qed.

Lemma mxdotDr m n (A B C : 'M[R]_(m, n)) :
  mxdot A (B + C) = mxdot A B + mxdot A C.
Proof. by rewrite mxdotC mxdotDl ![mxdot _ A]mxdotC. Qed.

Lemma mxdotZl m n a (A B : 'M[R]_(m, n)) : mxdot (a *: A) B = a * mxdot A B.
Proof.
rewrite /mxdot mulr_sumr; apply: eq_bigr => i _.
by rewrite mulr_sumr; apply: eq_bigr => j _; rewrite mxE mulrA.
Qed.

Lemma mxdotZr m n a (A B : 'M[R]_(m, n)) : mxdot A (a *: B) = a * mxdot A B.
Proof. by rewrite mxdotC mxdotZl mxdotC. Qed.

Lemma mxdotNl m n (A B : 'M[R]_(m, n)) : mxdot (- A) B = - mxdot A B.
Proof. by rewrite -scaleN1r mxdotZl mulN1r. Qed.

Lemma mxdotNr m n (A B : 'M[R]_(m, n)) : mxdot A (- B) = - mxdot A B.
Proof. by rewrite mxdotC mxdotNl mxdotC. Qed.

Lemma mxdotBl m n (A B C : 'M[R]_(m, n)) :
  mxdot (A - B) C = mxdot A C - mxdot B C.
Proof. by rewrite mxdotDl mxdotNl. Qed.

Lemma mxdotBr m n (A B C : 'M[R]_(m, n)) :
  mxdot A (B - C) = mxdot A B - mxdot A C.
Proof. by rewrite mxdotDr mxdotNr. Qed.

Lemma mxdot0l m n (A : 'M[R]_(m, n)) : mxdot 0 A = 0.
Proof. by apply: big1 => i _; apply: big1 => j _; rewrite mxE mul0r. Qed.

Lemma mxdot0r m n (A : 'M[R]_(m, n)) : mxdot A 0 = 0.
Proof. by rewrite mxdotC mxdot0l. Qed.

Lemma mxdot_suml m n I (r : seq I) (P : pred I) (F : I -> 'M[R]_(m, n)) B :
  mxdot (\sum_(k <- r | P k) F k) B = \sum_(k <- r | P k) mxdot (F k) B.
Proof. by elim/big_rec2: _ => [|k x y _ <-]; rewrite ?mxdot0l ?mxdotDl. Qed.

Lemma mxdot_sumr m n I (r : seq I) (P : pred I) (F : I -> 'M[R]_(m, n)) A :
  mxdot A (\sum_(k <- r | P k) F k) = \sum_(k <- r | P k) mxdot A (F k).
Proof. by rewrite mxdotC mxdot_suml; apply: eq_bigr => k _; rewrite mxdotC. Qed.

Lemma mxdot_trmx m n (A B : 'M[R]_(m, n)) : mxdot A^T B^T = mxdot A B.
Proof.
rewrite /mxdot exchange_big /=; apply: eq_bigr => j _.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma mxdot_trace m n (A B : 'M[R]_(m, n)) : mxdot A B = \tr (A *m B^T).
Proof.
apply: eq_bigr => i _; rewrite mxE.
by apply: eq_bigr => j _; rewrite mxE.
Qed.

Lemma mxdot_mulmxl m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) C :
  mxdot (A *m B) C = mxdot B (A^T *m C).
Proof.
by rewrite !mxdot_trace -mulmxA mxtrace_mulC -mulmxA trmx_mul trmxK.
Qed.

Lemma mxdot_mulmxr m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) C :
  mxdot (A *m B) C = mxdot A (C *m B^T).
Proof. by rewrite !mxdot_trace trmx_mul trmxK mulmxA. Qed.

Lemma mxdot_rowE n (u v : 'rV[R]_n) : mxdot u v = (u *m v^T) 0 0.
Proof. by rewrite mxdot_trace /mxtrace big_ord1. Qed.

Lemma mxdot_colE n (x y : 'cV[R]_n) : mxdot x y = (x^T *m y) 0 0.
Proof. by rewrite -mxdot_trmx mxdot_rowE trmxK. Qed.

Lemma mxdot_outer m n (A : 'M[R]_(m, n)) (x : 'cV[R]_m) (y : 'cV[R]_n) :
  mxdot A (x *m y^T) = (x^T *m A *m y) 0 0.
Proof.
rewrite mxdotC mxdot_mulmxl mxdot_rowE trmx_mul trmxK.
by rewrite -[x^T *m A *m y]trmxK [in RHS]mxE !trmx_mul trmxK mulmxA.
Qed.

Lemma mxdot_outer2 m n (a c : 'cV[R]_m) (b e : 'cV[R]_n) :
  mxdot (a *m b^T) (c *m e^T) = mxdot a c * mxdot b e.
Proof.
rewrite mxdot_outer mulmxA -mulmxA [in LHS]mxE big_ord1.
by rewrite -!mxdot_colE mxdotC.
Qed.

Lemma mxdot_diag n (a b : 'rV[R]_n) :
  mxdot (diag_mx a) (diag_mx b) = \sum_i a 0 i * b 0 i.
Proof.
apply: eq_bigr => i _; rewrite (bigD1 i) //= big1 ?addr0.
  by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0n mul0r.
by rewrite !mxE eqxx !mulr1n.
Qed.

Lemma mxdot_delta m n (A : 'M[R]_(m, n)) i j : mxdot A (delta_mx i j) = A i j.
Proof.
rewrite /mxdot (bigD1 i) //= (bigD1 j) //= big1 ?addr0.
  by move=> k kj; rewrite mxE eqxx (negbTE kj) mulr0.
rewrite big1 ?addr0.
  by move=> k ki; apply: big1 => l _; rewrite mxE (negbTE ki) mulr0.
by rewrite mxE !eqxx mulr1.
Qed.

End mxdot.

Section mxdot_real.
Variable R : realDomainType.
Implicit Types m n : nat.

Lemma mxdot_ge0 m n (A : 'M[R]_(m, n)) : 0 <= mxdot A A.
Proof.
by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
Qed.

Lemma mxdot_eq0 m n (A : 'M[R]_(m, n)) : (mxdot A A == 0) = (A == 0).
Proof.
apply/eqP/eqP => [AA0|->]; last exact: mxdot0l.
have sq_ge0 (x : R) : 0 <= x * x by rewrite -expr2 sqr_ge0.
have rows_ge0 i (_ : true) : 0 <= \sum_j A i j * A i j by apply: sumr_ge0.
apply/matrixP => i j; rewrite mxE.
have /(_ i isT)/psumr_eq0P := psumr_eq0P rows_ge0 AA0.
move=> /(_ (fun k _ => sq_ge0 _) j isT)/eqP.
by rewrite mulf_eq0 orbb => /eqP.
Qed.

Lemma mxdot_gt0 m n (A : 'M[R]_(m, n)) : (0 < mxdot A A) = (A != 0).
Proof. by rewrite lt_def mxdot_eq0 mxdot_ge0 andbT. Qed.

Lemma mxdot_cauchy_schwarz m n (A B : 'M[R]_(m, n)) :
  mxdot A B ^+ 2 <= mxdot A A * mxdot B B.
Proof.
have [->|B0] := eqVneq B 0; first by rewrite mxdot0r mxdot0l expr0n mulr0.
have c_gt0 : 0 < mxdot B B by rewrite mxdot_gt0.
have := mxdot_ge0 (mxdot B B *: A - mxdot A B *: B).
rewrite mxdotBl !mxdotBr !mxdotZl !mxdotZr (mxdotC B A).
set a := mxdot A A; set b := mxdot A B; set c := mxdot B B.
have -> : c * (c * a) - c * (b * b) - (b * (c * b) - b * (b * c)) =
    c * (a * c - b ^+ 2) by ring.
by rewrite pmulr_rge0 // subr_ge0.
Qed.

Lemma sum_cauchy_schwarz n (a b : 'I_n -> R) :
  (\sum_i a i * b i) ^+ 2 <= (\sum_i a i * a i) * (\sum_i b i * b i).
Proof.
have dotE (c e : 'I_n -> R) :
    mxdot (\row_j c j) (\row_j e j) = \sum_j c j * e j.
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE.
by have := mxdot_cauchy_schwarz (\row_j a j) (\row_j b j); rewrite !dotE.
Qed.

Lemma mxdot_entry m n (A : 'M[R]_(m, n)) i j : A i j ^+ 2 <= mxdot A A.
Proof.
rewrite /mxdot (bigD1 i) //= (bigD1 j) //= -expr2 -addrA lerDl.
apply: addr_ge0; first by apply: sumr_ge0 => k _; rewrite -expr2 sqr_ge0.
by apply: sumr_ge0 => k _; apply: sumr_ge0 => l _; rewrite -expr2 sqr_ge0.
Qed.

End mxdot_real.

Section frobenius.
Variable R : rcfType.
Implicit Types m n p : nat.

Definition frobenius m n (A : 'M[R]_(m, n)) : R := Num.sqrt (mxdot A A).

Lemma frobenius_ge0 m n (A : 'M[R]_(m, n)) : 0 <= frobenius A.
Proof. exact: sqrtr_ge0. Qed.

Lemma frobenius_sqr m n (A : 'M[R]_(m, n)) : frobenius A ^+ 2 = mxdot A A.
Proof. by rewrite sqr_sqrtr // mxdot_ge0. Qed.

Lemma frobenius_eq0 m n (A : 'M[R]_(m, n)) : (frobenius A == 0) = (A == 0).
Proof. by rewrite sqrtr_eq0 -mxdot_eq0 eq_le mxdot_ge0 andbT. Qed.

Lemma frobenius_gt0 m n (A : 'M[R]_(m, n)) : (0 < frobenius A) = (A != 0).
Proof. by rewrite sqrtr_gt0 mxdot_gt0. Qed.

Lemma frobenius0 m n : frobenius (0 : 'M[R]_(m, n)) = 0.
Proof. by rewrite /frobenius mxdot0l sqrtr0. Qed.

Lemma frobeniusZ m n a (A : 'M[R]_(m, n)) :
  frobenius (a *: A) = `|a| * frobenius A.
Proof.
by rewrite /frobenius mxdotZl mxdotZr mulrA -expr2 sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma frobeniusN m n (A : 'M[R]_(m, n)) : frobenius (- A) = frobenius A.
Proof. by rewrite -scaleN1r frobeniusZ normrN1 mul1r. Qed.

Lemma frobenius_trmx m n (A : 'M[R]_(m, n)) : frobenius A^T = frobenius A.
Proof. by rewrite /frobenius mxdot_trmx. Qed.

Lemma frobenius_rowE n (u : 'rV[R]_n) : frobenius u = Num.sqrt ((u *m u^T) 0 0).
Proof. by rewrite /frobenius mxdot_rowE. Qed.

Lemma frobenius_colE n (x : 'cV[R]_n) : frobenius x = Num.sqrt ((x^T *m x) 0 0).
Proof. by rewrite /frobenius mxdot_colE. Qed.

Lemma mxdot_le m n (A B : 'M[R]_(m, n)) :
  `|mxdot A B| <= frobenius A * frobenius B.
Proof.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // exprMn !frobenius_sqr.
by rewrite real_normK ?num_real // mxdot_cauchy_schwarz.
Qed.

Lemma ler_mxdot m n (A B : 'M[R]_(m, n)) :
  mxdot A B <= frobenius A * frobenius B.
Proof. exact: le_trans (ler_norm _) (mxdot_le A B). Qed.

Lemma frobeniusD m n (A B : 'M[R]_(m, n)) :
  frobenius (A + B) <= frobenius A + frobenius B.
Proof.
rewrite -ler_sqr ?nnegrE ?addr_ge0 ?frobenius_ge0 // sqrrD !frobenius_sqr.
rewrite mxdotDl !mxdotDr (mxdotC B A) addrA -[_ + mxdot A B + mxdot A B]addrA.
by rewrite -mulr2n lerD2r lerD2l lerMn2r ler_mxdot orbT.
Qed.

Lemma frobeniusB m n (A B : 'M[R]_(m, n)) :
  frobenius (A - B) <= frobenius A + frobenius B.
Proof. by rewrite -(frobeniusN B) frobeniusD. Qed.

Lemma ler_frobeniusB m n (A B : 'M[R]_(m, n)) :
  `|frobenius A - frobenius B| <= frobenius (A - B).
Proof.
have le_sub (X Y : 'M[R]_(m, n)) :
    frobenius X - frobenius Y <= frobenius (X - Y).
  by rewrite lerBlDr -{1}(subrK Y X) frobeniusD.
rewrite ler_norml le_sub andbT lerNl opprB.
by rewrite -[frobenius (A - B)]frobeniusN opprB le_sub.
Qed.

Lemma frobenius_entry m n (A : 'M[R]_(m, n)) i j : `|A i j| <= frobenius A.
Proof. by rewrite -sqrtr_sqr ler_wsqrtr // mxdot_entry. Qed.

Lemma frobenius_mulmx m n p (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  frobenius (A *m B) <= frobenius A * frobenius B.
Proof.
rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // exprMn !frobenius_sqr.
have -> : mxdot A A * mxdot B B =
    \sum_i \sum_k (\sum_j A i j * A i j) * (\sum_j B j k * B j k).
  rewrite [mxdot B B]exchange_big /= mulr_suml; apply: eq_bigr => i _.
  by rewrite mulr_sumr.
apply: ler_sum => i _; apply: ler_sum => k _; rewrite mxE -expr2.
exact: (sum_cauchy_schwarz (fun j => A i j) (fun j => B j k)).
Qed.

End frobenius.

Section orthogonal.
Variable R : comUnitRingType.
Implicit Types m n : nat.

Definition orthogonalmx {n} := [qualify M : 'M[R]_n | M *m M^T == 1%:M].
Fact orthogonalmx_key n : pred_key (@orthogonalmx n). Proof. by []. Qed.
Canonical orthogonalmx_keyed n := KeyedQualifier (orthogonalmx_key n).

Lemma orthogonalmxP n (M : 'M[R]_n) :
  reflect (M *m M^T = 1%:M) (M \is orthogonalmx).
Proof. by apply: (iffP eqP). Qed.

Lemma orthogonalmxT n (M : 'M[R]_n) : M \is orthogonalmx -> M^T *m M = 1%:M.
Proof. by move=> /orthogonalmxP/mulmx1C. Qed.

Lemma trmx_orthogonal n (M : 'M[R]_n) :
  (M^T \is orthogonalmx) = (M \is orthogonalmx).
Proof. by apply/orthogonalmxP/orthogonalmxP; rewrite trmxK => /mulmx1C. Qed.

Lemma orthogonalmx1 n : (1%:M : 'M[R]_n) \is orthogonalmx.
Proof. by apply/orthogonalmxP; rewrite trmx1 mulmx1. Qed.

Lemma mul_orthogonalmx n (A B : 'M[R]_n) :
  A \is orthogonalmx -> B \is orthogonalmx -> A *m B \is orthogonalmx.
Proof.
move=> /orthogonalmxP AA /orthogonalmxP BB; apply/orthogonalmxP.
by rewrite trmx_mul mulmxA -(mulmxA A) BB mulmx1 AA.
Qed.

Lemma orthogonalmx_unit n (M : 'M[R]_n) : M \is orthogonalmx -> M \in unitmx.
Proof. by move=> /orthogonalmxP/mulmx1_unit[]. Qed.

Lemma invmx_orthogonal n (M : 'M[R]_n) : M \is orthogonalmx -> invmx M = M^T.
Proof.
move=> Mo; rewrite -[LHS]mulmx1 -(orthogonalmxP _ Mo) mulmxA.
by rewrite mulVmx ?orthogonalmx_unit // mul1mx.
Qed.

Lemma orthogonal_block_mx m n (P : 'M[R]_m) (Q : 'M[R]_n) :
  P \is orthogonalmx -> Q \is orthogonalmx -> block_mx P 0 0 Q \is orthogonalmx.
Proof.
move=> /orthogonalmxP PP /orthogonalmxP QQ; apply/orthogonalmxP.
rewrite tr_block_mx !trmx0 mulmx_block !mulmx0 !mul0mx !addr0 !add0r PP QQ.
by rewrite -scalar_mx_block.
Qed.

Lemma perm_mx_orthogonal n (s : 'S_n) : perm_mx s \is orthogonalmx.
Proof. by apply/orthogonalmxP; rewrite tr_perm_mx -perm_mxM mulgV perm_mx1. Qed.

Lemma mxdot_orthogonalmxl m n (P : 'M[R]_m) (A B : 'M[R]_(m, n)) :
  P \is orthogonalmx -> mxdot (P *m A) (P *m B) = mxdot A B.
Proof. by move=> Po; rewrite mxdot_mulmxl mulmxA orthogonalmxT // mul1mx. Qed.

Lemma mxdot_orthogonalmxr m n (P : 'M[R]_n) (A B : 'M[R]_(m, n)) :
  P \is orthogonalmx -> mxdot (A *m P) (B *m P) = mxdot A B.
Proof.
by move=> /orthogonalmxP Po; rewrite mxdot_mulmxr -mulmxA Po mulmx1.
Qed.

End orthogonal.
Arguments orthogonalmx {R n}.

Section orthogonal_frobenius.
Variable R : rcfType.
Implicit Types m n : nat.

Lemma frobenius_orthogonalmxl m n (P : 'M[R]_m) (A : 'M[R]_(m, n)) :
  P \is orthogonalmx -> frobenius (P *m A) = frobenius A.
Proof. by move=> Po; rewrite /frobenius mxdot_orthogonalmxl. Qed.

Lemma frobenius_orthogonalmxr m n (P : 'M[R]_n) (A : 'M[R]_(m, n)) :
  P \is orthogonalmx -> frobenius (A *m P) = frobenius A.
Proof. by move=> Po; rewrite /frobenius mxdot_orthogonalmxr. Qed.

End orthogonal_frobenius.
