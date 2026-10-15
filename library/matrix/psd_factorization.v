From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear boolp classical_sets reals.
From mathcomp Require Import topology normedtype derive exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.
From GaussianAnalysis.matrix Require Import psd_splitting.
From GaussianAnalysis.convex Require Import logdet_barrier moreau.

(**md**************************************************************************)
(* # PSD factorizations                                                       *)
(*                                                                            *)
(* A real PSD factorization of size r of a matrix A : I -> J -> R, indexed by *)
(* two finite types, is a family of positive semidefinite r x r matrices F i  *)
(* for the rows and G j for the columns with A i j = tr (F i G j) for all i   *)
(* and j (psd_factorization A r). The PSD rank of A is the least such r; this *)
(* file does not define it, and the statements that use it are written for    *)
(* every factorization of a given size. With r = 0 allowed, the least size is *)
(* 0 for the zero matrix, where the manuscript's convention (the least r >=   *)
(* 1) gives 1; the two agree for every matrix with a nonzero entry.           *)
(*                                                                            *)
(* The general statements of this file, which the user accepted with batch    *)
(* 2 of phase 13 (AGENTS.md, section Phase 13, step 0, items 3 and 4), are    *)
(* the following lemmas, with the accepted texts:                             *)
(* - psd_factorization_ge0: the entries of a matrix with a PSD factorization  *)
(*   are nonnegative.                                                         *)
(* - psd_factorization_size_gt0: a factorization of a matrix with a nonzero   *)
(*   entry has a positive size.                                               *)
(* - psd_factorization_restrict: a factorization restricts to the rows and    *)
(*   columns of any maps I' -> I and J' -> J.                                 *)
(* - psd_factorization_widen: a factorization of size r gives one of every    *)
(*   size s >= r, by zero blocks.                                             *)
(* - psd_factorization_shift: a factorization of A of size r gives one of     *)
(*   A + rho of size r + 1 for rho >= 0, by a block of size one.              *)
(* - psd_factorization_nonneg: a nonnegative factorization                    *)
(*   A i j = sum_(k < r) a i k b j k, with a, b >= 0, gives a PSD             *)
(*   factorization of size r, by diagonal matrices.                           *)
(*                                                                            *)
(* The exact normalization of the factors, target T10 of phase 13, is stated  *)
(* in applications/PsdNormalizationStatement.v, written out with psdmx and    *)
(* the trace, and proved here (psd_normalization): PSD factors F i, G j of    *)
(* size r, J nonempty, with pairings tr (F i G j) <= m have PSD factors F' i, *)
(* G' j of the same size with the same pairings, tr (F' i) <= m and tr (G' j) *)
(* <= r.                                                                      *)
(*                                                                            *)
(* The route of T10 (the user's decision D9 asks for the exact form). Let S = *)
(* sum_j G j and Q the orthogonal projection onto the kernel of S             *)
(* (psd_kernel_proj); every G j vanishes on the range of Q. The determinant   *)
(* of Q + sum_j w_j G j is continuous in w (continuous_det_affine) and is     *)
(* maximized over the probability vectors w (prob_simplex_compact); at a      *)
(* maximizer w*, D = Q + sum_j w*_j G j is positive definite, and the         *)
(* first-order condition along the segments towards the vertices              *)
(* (det_max_first_order, from logdet_line of convex/logdet_barrier.v) gives   *)
(* tr (D^-1 G j) <= r. With the square roots of D and D^-1 (posdefmx_sqrt),   *)
(* G' j = D^-1/2 G j D^-1/2 and F' i = D^1/2 (1 - Q) F i (1 - Q) D^1/2 keep   *)
(* the pairings, and tr (F' i) = sum_j w*_j tr (F i G j) <= m. The            *)
(* compression by 1 - Q replaces the manuscript's restriction to the span of  *)
(* the column factors and keeps the size r; the Lean development regularizes  *)
(* by eps I instead and loses an additive constant in the row traces.         *)
(*                                                                            *)
(* These are Rocq formalizations of the credited arguments of 'Exponential    *)
(* PSD rank of positively shifted matching matrices' (family 126 of the       *)
(* OpenAI math collection, revision 1581d4cbd): the definition of a PSD       *)
(* factorization (source/sections/introduction.tex, lines 25-35), the lemma   *)
(* 'Normalization of PSD factors' (source/sections/matching.tex, lines        *)
(* 13-39), the padding of the proof of the corollary on semidefinite lifts    *)
(* (introduction.tex, lines 82-86), and the diagonal factorization of A_n(1)  *)
(* of size the number of edges (introduction.tex, lines 46-50), which         *)
(* psd_factorization_nonneg gives. The Lean development of the collection for *)
(* family 126 has the diagonal factorization of a nonnegative matrix and the  *)
(* normalization, in these declarations:                                      *)
(* Lean: exists_diagonal_factorization (FiniteFactorization.lean, line 69)    *)
(* Lean: exists_normalized_factors (DeterminantNormalization.lean, line 133)  *)
(*                                                                            *)
(* - The example psd_factorization_cols: every nonnegative matrix has a PSD   *)
(*   factorization of the size of its column type.                            *)
(*                                                                            *)
(* ```                                                                        *)
(*   psd_factorization A r == there are PSD matrices F i and G j of size r    *)
(*                            with A i j = \tr (F i *m G j) for all i and j   *)
(*          prob_simplex k == the probability vectors of 'rV[R]_k             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section factorization.
Variable R : realType.

(* A real PSD factorization of size r of A: PSD factors F i for the rows and
   G j for the columns, with the entries as their trace pairings. *)
Definition psd_factorization (I J : finType) (A : I -> J -> R) (r : nat) :
    Prop :=
  exists (F : I -> 'M[R]_r) (G : J -> 'M[R]_r),
    [/\ forall i, psdmx (F i), forall j, psdmx (G j) &
        forall i j, A i j = \tr (F i *m G j)].

End factorization.

Section closure.
Variable R : realType.
Implicit Types (I J : finType).

Lemma psd_factorization_ge0 I J (A : I -> J -> R) (r : nat) :
  psd_factorization A r -> forall i j, 0 <= A i j.
Proof.
by move=> [F [G [Fp Gp AE]]] i j; rewrite AE; exact: mxtrace_psd_ge0.
Qed.

Lemma psd_factorization_size_gt0 I J (A : I -> J -> R) (r : nat) :
  psd_factorization A r -> (exists i j, A i j != 0) -> (0 < r)%N.
Proof.
move=> [F [G [_ _ AE]]] [i [j]]; rewrite lt0n; apply: contra => /eqP r0.
by rewrite AE; move: (F i *m G j); rewrite r0 => M; rewrite /mxtrace big_ord0.
Qed.

Lemma psd_factorization_restrict I J I' J' (A : I -> J -> R) (r : nat)
    (f : I' -> I) (g : J' -> J) :
  psd_factorization A r -> psd_factorization (fun i j => A (f i) (g j)) r.
Proof.
move=> [F [G [Fp Gp AE]]]; exists (F \o f), (G \o g).
by split => [i|j|i j] /=; [exact: Fp | exact: Gp | exact: AE].
Qed.

(* Block-diagonal and diagonal positive semidefinite matrices; psdmx_diag is
   the case P = 1 of psd_conj (matrix/psd_part.v). *)
Lemma psdmx_block_diag m n (A : 'M[R]_m) (B : 'M[R]_n) :
  psdmx A -> psdmx B -> psdmx (block_mx A 0 0 B).
Proof.
move=> [As Ap] [Bs Bp]; split.
  apply/symmetricmxP; rewrite tr_block_mx !trmx0.
  by rewrite (symmetricmxP _ As) (symmetricmxP _ Bs).
move=> x; rewrite -[x](@vsubmxK _ m n 1) mul_block_col !mul0mx addr0 add0r.
rewrite !mxdot_colE tr_col_mx mul_row_col mxE.
by rewrite -!mxdot_colE addr_ge0.
Qed.

Lemma psdmx_diag n (d : 'rV[R]_n) : (forall k, 0 <= d 0 k) ->
  psdmx (diag_mx d).
Proof.
move=> d0; split; first by apply/symmetricmxP; rewrite tr_diag_mx.
move=> x; rewrite mxdot_colE mxE; apply: sumr_ge0 => k _.
rewrite mul_diag_mx !mxE mulrCA -expr2.
exact: mulr_ge0 (d0 k) (sqr_ge0 _).
Qed.

Lemma psd_factorization_widen I J (A : I -> J -> R) (r s : nat) :
  (r <= s)%N -> psd_factorization A r -> psd_factorization A s.
Proof.
move=> rs [F [G [Fp Gp AE]]]; rewrite -(subnKC rs).
exists (fun i => block_mx (F i) 0 0 (0 : 'M_(s - r))).
exists (fun j => block_mx (G j) 0 0 (0 : 'M_(s - r))).
split => [i|j|i j]; first exact/psdmx_block_diag/psdmx0.
  exact/psdmx_block_diag/psdmx0.
rewrite mulmx_block !mulmx0 !mul0mx !addr0 mxtrace_block.
by rewrite mxtrace0 addr0 AE.
Qed.

Lemma psd_factorization_shift I J (A : I -> J -> R) (r : nat) (rho : R) :
  0 <= rho -> psd_factorization A r ->
  psd_factorization (fun i j => A i j + rho) r.+1.
Proof.
move=> rho0 [F [G [Fp Gp AE]]].
have sc (c : R) : 0 <= c -> psdmx (c%:M : 'M[R]_1).
  by move=> c0; rewrite -diag_const_mx; apply: psdmx_diag => k; rewrite mxE.
exists (fun i => block_mx (rho%:M : 'M_1) 0 0 (F i)).
exists (fun j => block_mx (1%:M : 'M_1) 0 0 (G j)).
split => [i|j|i j].
- exact: (@psdmx_block_diag 1 r _ _ (sc _ rho0) (Fp i)).
- exact: (@psdmx_block_diag 1 r _ _ (sc _ ler01) (Gp j)).
rewrite (@mulmx_block _ 1 r 1 r 1 r) !mulmx0 !mul0mx !addr0 !add0r.
by rewrite (@mxtrace_block _ 1 r) mulmx1 mxtrace_scalar AE addrC.
Qed.

Lemma psd_factorization_nonneg I J (r : nat) (a : I -> 'I_r -> R)
    (b : J -> 'I_r -> R) :
  (forall i k, 0 <= a i k) -> (forall j k, 0 <= b j k) ->
  psd_factorization (fun i j => \sum_(k < r) a i k * b j k) r.
Proof.
move=> a0 b0; exists (fun i => diag_mx (\row_k a i k)).
exists (fun j => diag_mx (\row_k b j k)).
split => [i|j|i j].
- by apply: psdmx_diag => k; rewrite mxE.
- by apply: psdmx_diag => k; rewrite mxE.
by rewrite mulmx_diag mxtrace_diag; apply: eq_bigr => k _; rewrite !mxE.
Qed.

End closure.

Local Open Scope classical_set_scope.

Section normalization.
Variable R : realType.

(* The determinant of an affine family of matrices is continuous. *)
Lemma continuous_det_affine n k (M0 : 'M[R]_n) (M : 'I_k -> 'M[R]_n) :
  continuous (fun w : 'rV[R]_k => \det (M0 + \sum_(l < k) w 0 l *: M l)).
Proof.
have entry i j : continuous (fun w : 'rV[R]_k =>
    (M0 + \sum_(l < k) w 0 l *: M l) i j).
  have -> : (fun w : 'rV[R]_k => (M0 + \sum_(l < k) w 0 l *: M l) i j) =
      (fun w => M0 i j + \sum_(l < k) w 0 l * M l i j).
    by apply/funext => w; rewrite !mxE summxE; congr (_ + _);
      apply: eq_bigr => l _; rewrite mxE.
  move=> w; apply: (@continuousD _ R^o) => //; first exact: cst_continuous.
  apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
    (fun l (v : 'rV[R]_k) => v 0 l * M l i j)) => l _ v.
  apply: (continuousM (s := fun v : 'rV[R]_k => v 0 l) (t := fun=> M l i j)).
    exact: coord_continuous.
  exact: cst_continuous.
have -> : (fun w : 'rV[R]_k => \det (M0 + \sum_(l < k) w 0 l *: M l)) =
    (fun w => \sum_(s : 'S_n) (-1) ^+ s *
       \prod_i (M0 + \sum_(l < k) w 0 l *: M l) i (s i)).
  by apply/funext => w.
apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
  (fun (s : 'S_n) (w : 'rV[R]_k) => (-1) ^+ s * \prod_i
     (M0 + \sum_(l < k) w 0 l *: M l) i (s i))) => s _ w.
apply: (continuousM (s := fun=> (-1) ^+ s : R)); first exact: cst_continuous.
apply: (@continuous_big R^o _ *%R 1 xpredT (@mul_continuous R) _ _
  (fun i (v : 'rV[R]_k) => (M0 + \sum_(l < k) v 0 l *: M l) i (s i))) => i _.
exact: entry.
Qed.

(* Products of matrices diagonal in the same orthonormal basis. *)
Lemma conj_diag_mul n (P : 'M[R]_n) (a b : 'rV[R]_n) : P \is orthogonalmx ->
  (P^T *m diag_mx a *m P) *m (P^T *m diag_mx b *m P) =
  P^T *m diag_mx (\row_k (a 0 k * b 0 k)) *m P.
Proof.
move=> Po; rewrite -!mulmxA (mulmxA P) (orthogonalmxP _ Po) mul1mx.
by rewrite !mulmxA -(mulmxA _ (diag_mx a)) mulmx_diag.
Qed.

(* The orthogonal projection Q onto the kernel of a positive semidefinite
   S: S Q = 0, S + Q is positive definite, and every positive semidefinite
   G below S vanishes on the range of Q. *)
Lemma psd_kernel_proj n (S : 'M[R]_n) : psdmx S ->
  exists Q : 'M[R]_n,
  [/\ orthoprojmx Q, S *m Q = 0, posdefmx (S + Q) &
      forall G, psdmx G -> psdmx (S - G) -> G *m Q = 0].
Proof.
move=> [Ssym Spos].
set P := sym_spectralmx S; set d := sym_spectral_diag S.
have Po : P \is orthogonalmx := sym_spectralmx_orthogonal S.
have SE : S = P^T *m diag_mx d *m P := sym_spectralE Ssym.
have d0 : forall k, 0 <= d 0 k by apply/(spectral_psd Po SE).
pose e := \row_k ((d 0 k == 0)%:R : R).
pose Q := P^T *m diag_mx e *m P.
have Qsym : Q \is symmetricmx.
  by apply/symmetricmxP; rewrite /Q !trmx_mul trmxK tr_diag_mx mulmxA.
have SQ : S *m Q = 0.
  rewrite SE /Q conj_diag_mul //.
  have -> : \row_k (d 0 k * e 0 k) = 0.
    by apply/rowP => k; rewrite !mxE; case: eqP => [->|_];
      rewrite ?mul0r ?mulr0.
  by rewrite linear0 mulmx0 mul0mx.
exists Q; split => //.
- split => //; rewrite /Q conj_diag_mul //; congr (_ *m diag_mx _ *m _).
  by apply/rowP => k; rewrite !mxE; case: eqP; rewrite ?mulr1 ?mulr0.
- have -> : S + Q = P^T *m diag_mx (d + e) *m P.
    by rewrite SE /Q linearD /= mulmxDr mulmxDl.
  apply/(posdefmx_congruence _ (orthogonalmx_unit Po)) => k.
  rewrite !mxE; have := d0 k; rewrite le_eqVlt => /predU1P[<-|dk].
    by rewrite eqxx add0r ltr01.
  by rewrite gt_eqF // addr0.
- move=> G [Gsym Gpos] [SGsym SGpos].
  have colQ : forall y : 'cV[R]_n, G *m (Q *m y) = 0.
    move=> y; apply: psd_form_eq0 => //.
    apply/eqP; rewrite eq_le Gpos andbT.
    have := SGpos (Q *m y); rewrite mulmxBl mxdotBr subr_ge0.
    by rewrite [S *m _]mulmxA SQ mul0mx mxdot0r.
  apply/matrixP => i j; have h := colQ (delta_mx j 0).
  rewrite mulmxA -colE in h.
  by have := congr1 (fun M : 'cV[R]_n => M i 0) h; rewrite !mxE => ->.
Qed.

(* Positive definite matrices, in the row-vector form of logdet_barrier.v,
   and positive semidefinite ones, in the column-vector form of psd_part.v. *)
Lemma posdefmx_form n (A : 'M[R]_n) (x : 'cV[R]_n) : A \is symmetricmx ->
  mxdot x (A *m x) = mxdot x^T (x^T *m A).
Proof.
by move=> /symmetricmxP As; rewrite -[RHS]mxdot_trmx !trmxK trmx_mul trmxK As.
Qed.

Lemma posdefmx_psd n (A : 'M[R]_n) : posdefmx A -> psdmx A.
Proof.
move=> [As Ap]; split => // x; rewrite posdefmx_form //.
have [->|x0] := eqVneq x^T 0; first by rewrite mxdot0l.
exact/ltW/Ap.
Qed.

Lemma psdmx_unit_posdefmx n (A : 'M[R]_n) : psdmx A -> A \in unitmx ->
  posdefmx A.
Proof.
move=> [As Ap] Au; split => // x x0.
rewrite lt_neqAle; have := Ap x^T; rewrite posdefmx_form // trmxK => -> .
rewrite andbT eq_sym; apply/negP => /eqP h.
have : A *m x^T = 0.
  by apply: psd_form_eq0 => //; rewrite posdefmx_form // trmxK.
move=> /(congr1 (mulmx (invmx A))); rewrite mulmxA mulVmx // mul1mx mulmx0.
move=> /(congr1 trmx); rewrite trmxK trmx0 => x00.
by move: x0; rewrite x00 eqxx.
Qed.

Lemma posdefmx_det_gt0 n (A : 'M[R]_n) : posdefmx A -> 0 < \det A.
Proof.
move=> /posdefmx_spectral [P Po [d -> d0]].
rewrite det_congruence mulr_gt0 //.
  rewrite exprn_even_gt0 //= -unitfE -unitmxE.
  exact: orthogonalmx_unit.
by rewrite prodr_gt0.
Qed.

(* The square root of a positive definite matrix and of its inverse. *)
Lemma posdefmx_sqrt n (D : 'M[R]_n) : posdefmx D ->
  exists Dh Wi : 'M[R]_n,
  [/\ Dh \is symmetricmx, Wi \is symmetricmx, Dh *m Dh = D,
      Wi *m Wi = invmx D & Dh *m Wi = 1%:M /\ Wi *m Dh = 1%:M].
Proof.
move=> Dpd; have [P Po [d DE d0]] := posdefmx_spectral Dpd.
pose sq := \row_k Num.sqrt (d 0 k); pose isq := \row_k (Num.sqrt (d 0 k))^-1.
have sq0 k : 0 < Num.sqrt (d 0 k) by rewrite sqrtr_gt0.
exists (P^T *m diag_mx sq *m P), (P^T *m diag_mx isq *m P).
have symc (c : 'rV[R]_n) : P^T *m diag_mx c *m P \is symmetricmx.
  by apply/symmetricmxP; rewrite !trmx_mul trmxK tr_diag_mx mulmxA.
have DhDh : P^T *m diag_mx sq *m P *m (P^T *m diag_mx sq *m P) = D.
  rewrite conj_diag_mul // DE; congr (_ *m diag_mx _ *m _).
  by apply/rowP => k; rewrite !mxE -expr2 sqr_sqrtr // ltW.
have DhWi : P^T *m diag_mx sq *m P *m (P^T *m diag_mx isq *m P) = 1%:M.
  rewrite conj_diag_mul //.
  have -> : \row_k (sq 0 k * isq 0 k) = const_mx 1.
    by apply/rowP => k; rewrite !mxE mulfV // gt_eqF.
  rewrite diag_const_mx mulmx1; exact: orthogonalmxT.
have WiDh : P^T *m diag_mx isq *m P *m (P^T *m diag_mx sq *m P) = 1%:M.
  rewrite conj_diag_mul //.
  have -> : \row_k (isq 0 k * sq 0 k) = const_mx 1.
    by apply/rowP => k; rewrite !mxE mulVf // gt_eqF.
  rewrite diag_const_mx mulmx1; exact: orthogonalmxT.
split; [exact: symc | exact: symc | exact: DhDh | | by split].
set Dh := P^T *m diag_mx sq *m P in DhDh DhWi WiDh *.
set Wi := P^T *m diag_mx isq *m P in DhWi WiDh *.
have DWW : D *m (Wi *m Wi) = 1%:M.
  by rewrite -DhDh -mulmxA (mulmxA Dh Wi) DhWi mul1mx DhWi.
have Du : D \in unitmx by case: (mulmx1_unit DWW).
by rewrite -[LHS]mul1mx -(mulVmx Du) -mulmxA DWW mulmx1.
Qed.

Lemma posdefmx_inv_psd n (D : 'M[R]_n) : posdefmx D -> psdmx (invmx D).
Proof.
move=> /posdefmx_sqrt [Dh [Wi [_ Wis _ <- _]]].
split; first by apply/symmetricmxP; rewrite trmx_mul (symmetricmxP _ Wis).
by move=> x; rewrite -mulmxA -mxdot_mulmx_sym // mxdot_ge0.
Qed.

(* ln (1 + x) >= x - 2 x^2 for x >= -1/2. *)
Lemma ln1D_ge (x : R) : - 2^-1 <= x -> x - 2 * x ^+ 2 <= ln (1 + x).
Proof.
move=> x2; have x1 : 0 < 1 + x by lra.
have := ln_sub_ge x1 ltr01; rewrite ln1 subr0 => h; apply: le_trans h.
have hy : (1 / (1 + x)) * (1 + x) = 1.
  by rewrite mulrC mulrA mulr1 divff // lt0r_neq0.
have y0 : 0 < 1 / (1 + x) by rewrite divr_gt0.
set y := 1 / (1 + x) in hy y0 *.
nra.
Qed.

(* The first-order condition at a maximum of the determinant along a
   segment: if det (D + t U) <= det D for 0 < t <= 1, D positive definite
   and U symmetric, then tr (D^-1 U) <= 0. *)
Lemma det_max_first_order n (D U : 'M[R]_n) : posdefmx D ->
  U \is symmetricmx ->
  (forall t, 0 < t <= 1 -> \det (D + t *: U) <= \det D) ->
  \tr (invmx D *m U) <= 0.
Proof.
move=> Dpd Us hmax.
have [c [l [pdE lnE trE _]]] := logdet_line Dpd Us.
rewrite trE.
have cE : c = - ln (\det D).
  have := lnE 0; rewrite scale0r addr0 => /(_ Dpd) ->.
  by rewrite big1 ?subr0 // => i _; rewrite mul0r addr0 ln1.
pose L := \sum_i `|l 0 i|.
have L0 : 0 <= L by rewrite sumr_ge0 // => i _; exact: normr_ge0.
pose t0 := (2 * (1 + L))^-1.
have t00 : 0 < t0 by rewrite invr_gt0 mulr_gt0 // ltr_wpDr.
have t0L : t0 * L <= 2^-1.
  by rewrite /t0 invfM mulrAC ler_pdivrMr ?ltr_wpDr //; lra.
have t01 : t0 <= 1.
  by rewrite /t0 invf_le1 ?mulr_gt0 ?ltr_wpDr //; lra.
have small t : 0 < t <= t0 -> \sum_i l 0 i <= t * (2 * \sum_i l 0 i ^+ 2).
  move=> /andP[tp tt0].
  have tl i : - 2^-1 <= t * l 0 i.
    have li : `|l 0 i| <= L.
      by rewrite /L (bigD1 i) //= lerDl sumr_ge0 // => j _.
    have : `|t * l 0 i| <= 2^-1.
      rewrite normrM gtr0_norm //; apply: le_trans t0L.
      by apply: ler_pM => //; exact: ltW.
    by rewrite ler_norml => /andP[].
  have pos i : 0 < 1 + t * l 0 i by have := tl i; lra.
  have pd : posdefmx (D + t *: U) by apply/pdE.
  have hdet : \det (D + t *: U) <= \det D.
    by apply: hmax; rewrite tp (le_trans tt0 t01).
  have lnsum : \sum_i ln (1 + t * l 0 i) <= 0.
    have dpos := posdefmx_det_gt0 pd; have Dpos := posdefmx_det_gt0 Dpd.
    have e := lnE t pd; rewrite cE in e.
    have : ln (\det (D + t *: U)) <= ln (\det D) by rewrite ler_ln ?posrE.
    lra.
  have low : \sum_i (t * l 0 i - 2 * (t * l 0 i) ^+ 2)
      <= \sum_i ln (1 + t * l 0 i).
    by apply: ler_sum => i _; exact: ln1D_ge.
  rewrite sumrB -mulr_sumr -mulr_sumr in low.
  have e2 : \sum_i (t * l 0 i) ^+ 2 = t ^+ 2 * \sum_i l 0 i ^+ 2.
    by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite exprMn.
  rewrite e2 in low.
  set A := \sum_i l 0 i in low *; set B := \sum_i l 0 i ^+ 2 in low *.
  nra.
apply: (@le0_small _ _ (t0 * (2 * \sum_i l 0 i ^+ 2))) => t /andP[tp t1].
rewrite mulrA; apply: small.
by rewrite mulr_gt0 //= ger_pMl.
Qed.

(* The probability vectors of 'rV[R]_k form a compact set. prob_simplex is
   the set of row vectors of this compactness argument; mixture_weights
   (probability/mixture.v) and prob_vec (fourier/product_smoothing.v) are the
   same notion for the functions on a finite type. *)
Definition prob_simplex (k : nat) : set 'rV[R]_k :=
  [set w | (forall l, 0 <= w 0 l) /\ \sum_l w 0 l = 1].

Lemma prob_simplex_compact (k : nat) : compact (@prob_simplex k).
Proof.
apply: bounded_closed_compact.
  exists 1; split; first exact: num_real.
  move=> M M1 w [w0 w1]; apply: le_trans (ltW M1).
  rewrite [leLHS]/Num.Def.normr /= (le_trans (mx_norm_le_frobenius w)) //.
  rewrite /frobenius -sqrtr1 ler_sqrt // -w1 /mxdot big_ord1.
  apply: ler_sum => l _.
  have wl1 : w 0 l <= 1 by rewrite -w1 (bigD1 l) //= lerDl sumr_ge0.
  by have := w0 l; nra.
have -> : @prob_simplex k = (\bigcap_(l in [set: 'I_k])
    [set w : 'rV[R]_k | 0 <= w 0 l]) `&` [set w | \sum_l w 0 l = 1].
  apply/seteqP; split => w /=.
    by move=> [w0 w1]; split => // l _; exact: w0.
  by move=> [w0 w1]; split => // l; exact: w0.
apply: closedI.
  apply: closed_bigI => l _.
  apply: (@preimage_closed _ _ (fun w : 'rV[R]_k => w 0 l) [set x | 0 <= x]).
    by move=> x _; exact: coord_continuous.
  exact: closed_ge.
apply: (@preimage_closed _ _ (fun w : 'rV[R]_k => \sum_l w 0 l) [set 1]).
  move=> x _.
  apply: (@continuous_big R^o _ +%R 0 xpredT (@add_continuous R^o) _ _
    (fun l (w : 'rV[R]_k) => w 0 l)) => l _; exact: coord_continuous.
exact: closed_eq.
Qed.

(* The exact normalization of PSD factors (target T10). *)
Theorem psd_normalization (I J : finType) (r : nat) (F : I -> 'M[R]_r)
    (G : J -> 'M[R]_r) (m : R) :
  (0 < #|J|)%N ->
  (forall i, psdmx (F i)) -> (forall j, psdmx (G j)) ->
  (forall i j, \tr (F i *m G j) <= m) ->
  exists (F' : I -> 'M[R]_r) (G' : J -> 'M[R]_r),
    [/\ forall i, psdmx (F' i), forall j, psdmx (G' j),
        forall i j, \tr (F' i *m G' j) = \tr (F i *m G j),
        forall i, \tr (F' i) <= m &
        forall j, \tr (G' j) <= r%:R].
Proof.
move=> J0 Fpsd Gpsd FGm.
pose k := #|J|.
pose Gk (l : 'I_k) := G (enum_val l).
have Gkpsd l : psdmx (Gk l) := Gpsd _.
pose S := \sum_(l < k) Gk l.
have Spsd : psdmx S by apply: psdmx_sum => l _; exact: Gkpsd.
have [Q [[Qsym QQ] SQ SQpd GQ]] := psd_kernel_proj Spsd.
have GkQ l : Gk l *m Q = 0.
  apply: GQ; first exact: Gkpsd.
  have -> : S - Gk l = \sum_(l' < k | l' != l) Gk l'.
    by rewrite /S (bigD1 l) //= addrC addKr.
  by apply: psdmx_sum => l' _; exact: Gkpsd.
have QGk l : Q *m Gk l = 0.
  have := congr1 trmx (GkQ l); rewrite trmx_mul trmx0.
  by rewrite (symmetricmxP _ Qsym) (symmetricmxP _ (Gkpsd l).1).
have Qpsd : psdmx Q.
  split => // x; rewrite -QQ -mulmxA -mxdot_mulmx_sym //; exact: mxdot_ge0.
pose f (w : 'rV[R]_k) := \det (Q + \sum_(l < k) w 0 l *: Gk l).
have fc : continuous f := @continuous_det_affine r k Q Gk.
pose u : 'rV[R]_k := const_mx (k%:R^-1).
have k0 : 0 < k%:R :> R by rewrite ltr0n.
have uS : prob_simplex u.
  split => [l|]; first by rewrite mxE invr_ge0 ltW.
  under eq_bigr do rewrite mxE.
  by rewrite sumr_const card_ord -[_ *+ _]mulr_natr mulVf // gt_eqF.
have fcA : {within @prob_simplex k, continuous f}.
  exact: continuous_subspaceT.
have [ws wsS wsmax] := @EVT_max_rV R k f (@prob_simplex k)
  (ex_intro _ u uS) (@prob_simplex_compact k) fcA.
move: wsS; rewrite inE => wsS.
have rowpsd (A : 'M[R]_r) (x : 'rV[R]_r) : psdmx A -> 0 <= mxdot x (x *m A).
  by move=> [As Ap]; have := Ap x^T; rewrite posdefmx_form // trmxK.
have fu : 0 < f u.
  apply: posdefmx_det_gt0.
  have -> : Q + \sum_(l < k) u 0 l *: Gk l = Q + k%:R^-1 *: S.
    rewrite /S scaler_sumr; congr (_ + _).
    by apply: eq_bigr => l _; rewrite mxE.
  have [SQs SQp] := SQpd.
  split.
    apply/symmetricmxP; rewrite linearD linearZ /= (symmetricmxP _ Qsym).
    by rewrite (symmetricmxP _ Spsd.1).
  move=> x x0; have := SQp x x0.
  rewrite !mulmxDr !mxdotDr -scalemxAr mxdotZr.
  have := rowpsd _ x Spsd; have := rowpsd _ x Qpsd.
  have : 0 < k%:R^-1 :> R by rewrite invr_gt0.
  nra.
pose D := Q + \sum_(l < k) ws 0 l *: Gk l.
have Dpsd : psdmx D.
  apply: psdmxD => //; apply: psdmx_sum => l _.
  by apply: psdmxZ; [exact: wsS.1 | exact: Gkpsd].
have Ddet : 0 < \det D by apply: lt_le_trans fu (wsmax u _); rewrite inE.
have Dpd : posdefmx D.
  by apply: psdmx_unit_posdefmx => //; rewrite unitmxE unitfE gt_eqF.
have Gksym l : (Gk l)^T = Gk l := symmetricmxP _ (Gkpsd l).1.
have foc l : \tr (invmx D *m Gk l) <= r%:R.
  pose U := Gk l - \sum_(l' < k) ws 0 l' *: Gk l'.
  have Usym : U \is symmetricmx.
    apply/symmetricmxP; rewrite /U linearB linear_sum /= Gksym.
    by congr (_ - _); apply: eq_bigr => l' _; rewrite linearZ /= Gksym.
  have trU : \tr (invmx D *m U) <= 0.
    apply: det_max_first_order => // t /andP[t0 t1].
    pose wt : 'rV[R]_k := (1 - t) *: ws + t *: delta_mx 0 l.
    have wtS : prob_simplex wt.
      split => [l'|].
        rewrite /wt !mxE addr_ge0 // mulr_ge0 ?ler0n ?subr_ge0 ?wsS.1 //.
        exact: ltW.
      rewrite /wt; under eq_bigr do rewrite !mxE.
      rewrite big_split /= -!mulr_sumr wsS.2 mulr1 (bigD1 l) //= eqxx.
      rewrite big1 ?addr0 ?mulr1 ?subrK // => l'.
      by move=> /negPf; rewrite eq_sym => ->.
    have e : Q + \sum_(l' < k) wt 0 l' *: Gk l' = D + t *: U.
      rewrite /D /U /wt -addrA; congr (_ + _).
      under eq_bigr do rewrite !mxE scalerDl -!scalerA.
      rewrite big_split /= -scaler_sumr -[X in _ + X]scaler_sumr.
      have dl : \sum_(i < k) (i == l)%:R *: Gk i = Gk l.
        rewrite (bigD1 l) //= eqxx scale1r big1 ?addr0 // => i il.
        by rewrite (negPf il) scale0r.
      rewrite dl; set A := \sum_(l0 < k) ws 0 l0 *: Gk l0.
      by rewrite scalerBl scale1r scalerBr addrA addrAC.
    by rewrite -e; have := wsmax wt; rewrite inE => /(_ wtS).
  have Du : D \in unitmx by rewrite unitmxE unitfE gt_eqF.
  have DQ : D - Q = \sum_(l' < k) ws 0 l' *: Gk l' by rewrite /D addrC addKr.
  have e1 : \tr (invmx D *m U) =
      \tr (invmx D *m Gk l) - \tr (invmx D *m (D - Q)).
    by rewrite /U DQ mulmxBr raddfB.
  have e2 : \tr (invmx D *m (D - Q)) = r%:R - \tr (invmx D *m Q).
    by rewrite mulmxBr (mulVmx Du) raddfB /= mxtrace1.
  have hQ : 0 <= \tr (invmx D *m Q).
    exact: mxtrace_psd_ge0 (posdefmx_inv_psd Dpd) Qpsd.
  by move: trU; rewrite e1 e2; lra.
have [Dh [Wi [Dhs Wis DhDh WiWi [DhWi WiDh]]]] := posdefmx_sqrt Dpd.
pose Pi := 1%:M - Q.
have Pis : Pi \is symmetricmx.
  by apply/symmetricmxP; rewrite /Pi linearB /= trmx1 (symmetricmxP _ Qsym).
have PiQ : Pi *m Q = 0 by rewrite /Pi mulmxBl mul1mx QQ subrr.
have GkPi l : Gk l *m Pi = Gk l by rewrite /Pi mulmxBr mulmx1 GkQ subr0.
have PiGk l : Pi *m Gk l = Gk l by rewrite /Pi mulmxBl mul1mx QGk subr0.
have PiDPi : Pi *m D *m Pi = \sum_(l < k) ws 0 l *: Gk l.
  rewrite /D (mulmxDr Pi Q) PiQ add0r mulmx_sumr mulmx_suml.
  by apply: eq_bigr => l _; rewrite -scalemxAr -scalemxAl PiGk GkPi.
exists (fun i => Dh *m (Pi *m F i *m Pi) *m Dh), (fun j => Wi *m G j *m Wi).
split.
- by move=> i; apply: psdmx_conj => //; apply: psdmx_conj.
- by move=> j; apply: psdmx_conj.
- move=> i j.
  have GPi : G j *m Pi = G j.
    by have := GkPi (enum_rank j); rewrite /Gk enum_rankK.
  have PiG : Pi *m G j = G j.
    by have := PiGk (enum_rank j); rewrite /Gk enum_rankK.
  have -> : Dh *m (Pi *m F i *m Pi) *m Dh *m (Wi *m G j *m Wi) =
      Dh *m (Pi *m F i *m Pi *m G j *m Wi).
    by rewrite !mulmxA -(mulmxA _ Dh Wi) DhWi mulmx1.
  rewrite mxtrace_mulC -[_ *m Wi *m Dh]mulmxA WiDh mulmx1.
  rewrite -[Pi *m F i *m Pi *m G j]mulmxA PiG mxtrace_mulC mulmxA GPi.
  exact: mxtrace_mulC.
- move=> i.
  have -> : \tr (Dh *m (Pi *m F i *m Pi) *m Dh) =
      \tr (F i *m (Pi *m D *m Pi)).
    rewrite -mulmxA mxtrace_mulC -[_ *m Dh *m Dh]mulmxA DhDh.
    rewrite -[Pi *m F i *m Pi *m D]mulmxA -[Pi *m F i *m _]mulmxA.
    by rewrite mxtrace_mulC !mulmxA.
  rewrite PiDPi mulmx_sumr raddf_sum /=.
  apply: le_trans (_ : \sum_(l < k) ws 0 l * m <= m).
    apply: ler_sum => l _; rewrite -scalemxAr linearZ /=.
    by apply: ler_wpM2l; [exact: wsS.1 | exact: FGm].
  by rewrite -mulr_suml wsS.2 mul1r.
- move=> j; rewrite mxtrace_mulC mulmxA WiWi.
  by have := foc (enum_rank j); rewrite /Gk enum_rankK.
Qed.

End normalization.

(* An example independent of any application: every nonnegative matrix
   A : I -> J -> R has a PSD factorization of the size #|J|, by the diagonal
   factors of the nonnegative factorization A i j = sum_k A i k' [k' = j]. *)
Example psd_factorization_cols (R : realType) (I J : finType)
    (A : I -> J -> R) :
  (forall i j, 0 <= A i j) -> psd_factorization A #|J|.
Proof.
move=> A0.
have := @psd_factorization_nonneg R I J #|J|
  (fun i k => A i (enum_val k)) (fun j k => (enum_val k == j)%:R).
move=> /(_ (fun i k => A0 _ _) (fun j k => ler0n _ _)) [F [G [Fp Gp AE]]].
exists F, G; split => // i j; rewrite -AE.
rewrite (bigD1 (enum_rank j)) //= enum_rankK eqxx mulr1 big1 ?addr0 // => k kj.
have : enum_val k != j by apply: contra kj => /eqP <-; rewrite enum_valK.
by move=> /negbTE ->; rewrite mulr0.
Qed.
