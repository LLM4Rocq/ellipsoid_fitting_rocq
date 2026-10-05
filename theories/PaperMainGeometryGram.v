(* Deterministic geometry for the main results of the paper, part 2: every
   positive semidefinite matrix is a sum of rank-one matrices w w^T, and
   the pairing of a nonzero positive semidefinite matrix with a positive
   definite one is strictly positive.

   The decomposition is by a rank-one peeling: if S >= 0 has a nonzero
   diagonal entry a = S_kk, then S - a^-1 s s^T with s the k-th column of S
   is again >= 0 (the Cauchy-Schwarz inequality of the form), its k-th
   diagonal entry is 0, and every zero diagonal entry of S stays zero. The
   number of nonzero diagonal entries decreases, and a matrix >= 0 with a
   zero diagonal is 0. No spectral theorem and no square root of matrices
   is needed; MathComp's spectral theory is over closed fields only.

   Internal proof workstream (analysis/reports/PROGRESS-main-geometry.md);
   not part of any contract. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section RankOne.
Variable d : nat.
Implicit Types (S : 'M[R]_d) (v w s : 'cV[R]_d).

(* 1 x 1 matrices as scalars. *)
Lemma paper_main_mx11_mul (A B : 'M[R]_1) : (A *m B) 0 0 = A 0 0 * B 0 0.
Proof. by rewrite mxE big_ord1. Qed.

Lemma paper_main_mx11_tr (A : 'M[R]_1) : A^T 0 0 = A 0 0.
Proof. by rewrite mxE. Qed.

Lemma paper_main_inner_sym s v : (s^T *m v) 0 0 = (v^T *m s) 0 0.
Proof. by rewrite -paper_main_mx11_tr trmx_mul trmxK. Qed.

(* The form of a rank-one matrix: v^T (s s^T) v = (v^T s)^2. *)
Lemma paper_main_form_rank1E v s :
  (v^T *m (s *m s^T) *m v) 0 0 = (v^T *m s) 0 0 ^+ 2.
Proof.
by rewrite mulmxA -mulmxA paper_main_mx11_mul paper_main_inner_sym -expr2.
Qed.

(* The form at a basis vector is a diagonal entry. *)
Lemma paper_main_form_deltaE S (j : 'I_d) :
  ((delta_mx j 0 : 'cV[R]_d)^T *m S *m (delta_mx j 0 : 'cV[R]_d)) 0 0 = S j j.
Proof.
rewrite trmx_delta -mulmxA -colE -rowE.
by rewrite [fun_of_matrix (row _ _) _ _]mxE [fun_of_matrix (col _ _) _ _]mxE.
Qed.

Lemma paper_main_form_delta S (j : 'I_d) :
  paper_main_quadratic_form S (delta_mx j 0 : 'cV[R]_d) = S j j.
Proof. by rewrite paper_main_quadratic_formE paper_main_form_deltaE. Qed.

(* Diagonal entries of S >= 0 are nonnegative. *)
Lemma paper_main_psd_diag_ge0 S (j : 'I_d) : paper_main_psd S -> 0 <= S j j.
Proof. by move=> [_ Hpos]; rewrite -paper_main_form_delta. Qed.

(* A zero diagonal entry of S >= 0 kills its column, hence its row. *)
Lemma paper_main_psd_zero_diag_col S (j : 'I_d) :
  paper_main_psd S -> S j j = 0 -> S *m (delta_mx j 0 : 'cV[R]_d) = 0.
Proof.
by move=> HS Hj; apply: paper_main_psd_form_eq0 => //; rewrite paper_main_form_delta.
Qed.

Lemma paper_main_psd_zero_diag_entry S (i j : 'I_d) :
  paper_main_psd S -> S j j = 0 -> S i j = 0.
Proof.
move=> HS Hj; have := paper_main_psd_zero_diag_col S j HS Hj.
rewrite -colE; move/matrixP/(_ i 0).
by rewrite [fun_of_matrix (col _ _) _ _]mxE [RHS]mxE.
Qed.

(* The Cauchy-Schwarz inequality of a form >= 0. *)
Lemma paper_main_psd_cauchy_schwarz S v w : paper_main_psd S ->
  (v^T *m S *m w) 0 0 ^+ 2 <= (v^T *m S *m v) 0 0 * (w^T *m S *m w) 0 0.
Proof.
move=> HS; have Hs : S^T = S by apply/paper_main_symmetricP; case: HS.
have Hq (u : 'cV[R]_d) : 0 <= (u^T *m S *m u) 0 0.
  by rewrite -paper_main_quadratic_formE; case: HS => _; exact.
set c : R := (v^T *m S *m w) 0 0.
set qv : R := (v^T *m S *m v) 0 0; set qw : R := (w^T *m S *m w) 0 0.
have [qw0 | qw0] := eqVneq qw 0.
  have Sw : S *m w = 0.
    by apply: paper_main_psd_form_eq0 => //; rewrite paper_main_quadratic_formE.
  have c0 : c = 0 by rewrite /c -mulmxA Sw mulmx0 mxE.
  by rewrite c0 qw0 mulr0 expr2 mul0r.
have qwpos : 0 < qw by rewrite lt0r qw0 Hq.
have line t : 0 <= qv + t * c + t * c + t * t * qw.
  have := Hq (v + t *: w); rewrite paper_main_form_line //.
  by rewrite -/qv -/qw -(paper_main_cross_sym _ S v w Hs) -/c.
set u := qw^-1.
have uq : u * qw = 1 by rewrite /u mulVf.
have u0 : 0 < u by rewrite /u invr_gt0.
(* Stdlib's vocabulary with explicit zeros and ones. *)
have Hl : Rle (IZR 0)
    (Rplus (Rplus (Rplus qv (Rmult (Ropp (Rmult c u)) c)) (Rmult (Ropp (Rmult c u)) c))
      (Rmult (Rmult (Ropp (Rmult c u)) (Ropp (Rmult c u))) qw)).
  by apply/RleP; exact: (line (- (c * u))).
have uq' : Rmult u qw = IZR 1 := uq.
have qw' : Rlt (IZR 0) qw by apply/RltP.
have u' : Rlt (IZR 0) u by apply/RltP.
have P1 : Rmult (Rmult (Rmult (Rmult c c) u) u) qw = Rmult (Rmult c c) u.
  by rewrite Rmult_assoc uq' Rmult_1_r.
have P2 : Rmult (Rmult (Rmult c c) u) qw = Rmult c c.
  by rewrite Rmult_assoc uq' Rmult_1_r.
rewrite expr2; apply/RleP; change (Rle (Rmult c c) (Rmult qv qw)).
nra.
Qed.

End RankOne.

Section Peel.
Variable d : nat.
Implicit Types (S : 'M[R]_d) (v : 'cV[R]_d).

(* One peeling step: remove the rank-one part carried by column k. *)
Definition paper_main_peel S (k : 'I_d) : 'M[R]_d :=
  S - (S k k)^-1 *: (col k S *m (col k S)^T).

Lemma paper_main_peel_entry S k i j :
  paper_main_peel S k i j = S i j - (S k k)^-1 * (S i k * S j k).
Proof. by rewrite !mxE big_ord1 !mxE. Qed.

Lemma paper_main_peel_form S k v :
  paper_main_quadratic_form (paper_main_peel S k) v =
  paper_main_quadratic_form S v -
    (S k k)^-1 * (v^T *m S *m (delta_mx k 0 : 'cV[R]_d)) 0 0 ^+ 2.
Proof.
rewrite !paper_main_quadratic_formE /paper_main_peel.
rewrite mulmxBr mulmxBl -scalemxAr -scalemxAl.
rewrite [fun_of_matrix (_ + _) _ _]mxE [fun_of_matrix (- _) _ _]mxE
  [fun_of_matrix (_ *: _) _ _]mxE.
by rewrite paper_main_form_rank1E colE mulmxA.
Qed.

Lemma paper_main_peel_psd S k :
  paper_main_psd S -> 0 < S k k -> paper_main_psd (paper_main_peel S k).
Proof.
move=> HS Hk; have [Hsym Hpos] := HS; split.
  move=> i j; rewrite !paper_main_peel_entry.
  by rewrite (Hsym i j) (mulrC (S i k)).
move=> v; rewrite paper_main_peel_form subr_ge0 mulrC ler_pdivrMr //.
have := paper_main_psd_cauchy_schwarz _ S v (delta_mx k 0 : 'cV[R]_d) HS.
by rewrite paper_main_form_deltaE -paper_main_quadratic_formE.
Qed.

Lemma paper_main_peel_diag_zero S k j :
  paper_main_psd S -> S j j = 0 -> paper_main_peel S k j j = 0.
Proof.
move=> HS Hj; rewrite paper_main_peel_entry Hj.
have -> : S j k = 0.
  by have [Hsym _] := HS; rewrite (Hsym j k); exact: (paper_main_psd_zero_diag_entry _ S k j HS Hj).
by rewrite !mulr0 subr0.
Qed.

Lemma paper_main_peel_kk S k : S k k != 0 -> paper_main_peel S k k k = 0.
Proof. by move=> Hk; rewrite paper_main_peel_entry mulrA mulVf // mul1r subrr. Qed.

Lemma paper_main_peel_card S k : paper_main_psd S -> S k k != 0 ->
  (#|[set j : 'I_d | paper_main_peel S k j j != (0 : R)]%SET| <
    #|[set j : 'I_d | S j j != (0 : R)]%SET|)%nat.
Proof.
move=> HS Hk; apply: proper_card; apply/properP; split.
  apply/fintype.subsetP => j; rewrite !inE; apply: contraNneq => Hj.
  by rewrite paper_main_peel_diag_zero // eqxx.
exists k; rewrite !inE //.
by rewrite paper_main_peel_kk // eqxx.
Qed.

End Peel.

(* Every S >= 0 is a sum of rank-one matrices w_i w_i^T. *)
Theorem paper_main_psd_decomp d (S : 'M[R]_d) : paper_main_psd S ->
  exists m (w : 'I_m -> 'cV[R]_d), S = \sum_(i < m) w i *m (w i)^T.
Proof.
have [m] := ubnP #|[set j : 'I_d | S j j != (0 : R)]%SET|.
elim: m S => [S | m IH S]; first by rewrite ltn0.
rewrite ltnS => cardS HS.
have [k Hk | H0] := pickP [pred j : 'I_d | S j j != 0].
  have Hk' : S k k != 0 := Hk.
  have a0 : 0 < S k k by rewrite lt0r Hk' (paper_main_psd_diag_ge0 _ S k HS).
  have HS' := paper_main_peel_psd _ S k HS a0.
  have cardS' := leq_trans (paper_main_peel_card _ S k HS Hk') cardS.
  have [m' [w' E']] := IH _ cardS' HS'.
  set s := col k S.
  set w0 : 'cV[R]_d := (Num.sqrt (S k k))^-1 *: s.
  exists m'.+1, (fun i => if unlift ord0 i is Some j then w' j else w0).
  rewrite big_ord_recl /= unlift_none /=.
  under eq_bigr => j _ do rewrite /= liftK.
  rewrite -E' /paper_main_peel -/s.
  have -> : w0 *m w0^T = (S k k)^-1 *: (s *m s^T).
    rewrite /w0 [(_ *: _)^T]linearZ /= -scalemxAl -scalemxAr scalerA -invfM.
    by rewrite -expr2 sqr_sqrtr ?(ltW a0).
  by rewrite addrC subrK.
exists 0%N, (fun _ => 0); rewrite big_ord0.
apply/matrixP => i j.
have Sjj : S j j = 0 by apply/eqP; have := H0 j; rewrite /= => /negbFE.
by rewrite (paper_main_psd_zero_diag_entry _ S i j HS Sjj) [RHS]mxE.
Qed.

(* The pairing of a positive definite matrix with a nonzero positive
   semidefinite one is strictly positive. *)
Theorem paper_main_pairing_pd_psd_gt0 d (M S : 'M[R]_d) :
  paper_main_pd M -> paper_main_psd S -> S != 0 -> 0 < paper_main_pairing M S.
Proof.
move=> [_ HM] HS S0.
have [m [w E]] := paper_main_psd_decomp d S HS.
have Ew : paper_main_pairing M S = \sum_(i < m) paper_main_quadratic_form M (w i).
  have -> : S = \sum_(i < m) 1 *: (w i *m (w i)^T).
    by rewrite E; apply: eq_bigr => i _; rewrite scale1r.
  rewrite paper_main_pairing_sum; apply: eq_bigr => i _.
  by rewrite mul1r paper_main_pairing_outer.
have term_ge0 i : 0 <= paper_main_quadratic_form M (w i).
  have [-> | wi0] := eqVneq (w i) 0.
    by rewrite paper_main_quadratic_formE trmx0 !mul0mx mxE lexx.
  by apply/ltW/HM.
rewrite Ew lt0r; apply/andP; split; last by apply: sumr_ge0 => i _; exact: term_ge0.
apply/eqP => Hsum0.
have Hall := psumr_eq0P (fun i _ => term_ge0 i) Hsum0.
move/negP: S0; apply; rewrite E; apply/eqP; rewrite big1 // => i _.
have wi0 : w i = 0.
  apply/eqP; apply: contraT => wi0.
  by have := HM _ wi0; rewrite (Hall i isT) ltxx.
by rewrite wi0 mul0mx.
Qed.
