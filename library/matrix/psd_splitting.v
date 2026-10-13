From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral psd_part.

(**md**************************************************************************)
(* # Orthogonal splitting of positive semidefinite matrices                   *)
(*                                                                            *)
(* Target T5 of phase 12 (AGENTS.md, section Phase 12). A Rocq formalization  *)
(* of the credited argument of the lemma 'Orthogonal splitting' of            *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/splitting.tex). The collection has no Lean version of it.  *)
(*                                                                            *)
(* For positive semidefinite A_1, ..., A_L of 'M[R]_n, L >= 1, there are      *)
(* orthogonal projections P_1, ..., P_L, possibly zero, mutually orthogonal   *)
(* and of sum 1, such that the sum over z and s != z of |P_s A_z P_s|_F^2 is  *)
(* at most 2^(L-1) times the sum of tr (A_z A_z') over the ordered pairs of   *)
(* distinct indices.                                                          *)
(*                                                                            *)
(* The proof is the manuscript's. The two-matrix estimate: for A, B >= 0, the *)
(* spectral projection P of A - B onto its nonnegative eigenspaces satisfies  *)
(* tr (A B) >= |P B P|_F^2 + |(1 - P) A (1 - P)|_F^2, because the off-        *)
(* diagonal blocks of A and B along P agree and the diagonal blocks are       *)
(* ordered. Then an induction on L, which splits A_1 from the sum of the      *)
(* others and applies the induction hypothesis to the compressions on the     *)
(* range of 1 - P. To keep the dimension fixed, the induction is relative to  *)
(* an orthogonal projection Q (psd_splitting_rel): the projections are below  *)
(* Q, they sum to Q, and the overlaps are tr (A_z Q A_z' Q). The squared      *)
(* triangle inequality on Q - P uses the nonnegative quadratic form X |-> tr  *)
(* (A X B X), and the spectral projection is built from symmetric_spectral    *)
(* and commutes with every matrix that commutes with A - B                    *)
(* (diag_mx_commute_map), hence with Q.                                       *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - orthoprojmx1, orthoprojmx0, orthoprojmxB; psdmx_conj, psdmxD, psdmx_sum; *)
(*   mxtrace_psd_ge0 (tr (S T) >= 0 for S, T >= 0); frobenius_sqr_sym.        *)
(* - spectral_nonneg_proj: the spectral projection E of a symmetric M onto    *)
(*   its nonnegative eigenspaces, with E M = M E, E M E >= 0, (1 - E) M (1 -  *)
(*   E) <= 0, and X E = E X for every X that commutes with M.                 *)
(* - mxdot_block0, mxdot_sym_tr, mxdot_compress: blocks along orthogonal      *)
(*   projections; two_matrix_split: the two-matrix estimate, relative to Q.   *)
(* - frobenius_compress_le: compressing by projections of sum Q does not      *)
(*   increase the Frobenius norm of a matrix supported by Q;                  *)
(*   frobenius_sum_psd_le: the squared norms of positive semidefinite         *)
(*   matrices sum to at most the squared norm of their sum.                   *)
(* - sum_offdiag_recl: a sum over the ordered pairs of distinct indices of    *)
(*   'I_L.+2 split at the first index; trace_quad_ge0, trace_quad_sub_le: tr  *)
(*   (A (Q - P) B (Q - P)) <= 2 tr (A Q B Q) + 2 tr (A P B P).                *)
(* - psd_splitting_rel and psd_splitting: the lemma for L + 1 matrices, with  *)
(*   constant 2^L.                                                            *)
(*                                                                            *)
(* ```                                                                        *)
(*   orthoprojmx P == P is an orthogonal projection: symmetric and P P = P    *)
(*   nonneg_part x == 1 if x >= 0 and 0 otherwise                             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section orthoprojmx.
Variable R : realType.
Implicit Types n : nat.

(* P is an orthogonal projection: symmetric and idempotent. *)
Definition orthoprojmx n (P : 'M[R]_n) : Prop :=
  P \is symmetricmx /\ P *m P = P.

Lemma orthoprojmx1 n : orthoprojmx (1%:M : 'M[R]_n).
Proof. by split; [apply/symmetricmxP; rewrite trmx1 | rewrite mulmx1]. Qed.

Lemma orthoprojmx0 n : orthoprojmx (0 : 'M[R]_n).
Proof. by split; [apply/symmetricmxP; rewrite trmx0 | rewrite mulmx0]. Qed.

Lemma orthoprojmxB n (Q P : 'M[R]_n) : orthoprojmx Q -> orthoprojmx P ->
  P *m Q = P -> Q *m P = P -> orthoprojmx (Q - P).
Proof.
move=> [Qs QQ] [Ps PP] PQ QP; split.
  apply/symmetricmxP; rewrite linearB /=.
  by rewrite (symmetricmxP _ Qs) (symmetricmxP _ Ps).
by rewrite mulmxBl !mulmxBr QQ QP PQ PP subrr subr0.
Qed.

Lemma psdmx_conj n (P M : 'M[R]_n) : P \is symmetricmx -> psdmx M ->
  psdmx (P *m M *m P).
Proof.
move=> /symmetricmxP PT [/symmetricmxP MT Mpsd]; split.
  by apply/symmetricmxP; rewrite !trmx_mul PT MT mulmxA.
move=> x; have := Mpsd (P *m x).
by rewrite -!mulmxA mxdot_mulmxl PT.
Qed.

Lemma psdmxD n (A B : 'M[R]_n) : psdmx A -> psdmx B -> psdmx (A + B).
Proof.
move=> [As Ap] [Bs Bp]; split.
  apply/symmetricmxP; rewrite linearD /=.
  by rewrite (symmetricmxP _ As) (symmetricmxP _ Bs).
by move=> x; rewrite mulmxDl mxdotDr addr_ge0.
Qed.

Lemma psdmx0 n : psdmx (0 : 'M[R]_n).
Proof.
by split; [apply/symmetricmxP; rewrite trmx0 | move=> x; rewrite mul0mx mxdot0r].
Qed.

Lemma psdmx_sum n I (r : seq I) (P : pred I) (F : I -> 'M[R]_n) :
  (forall i, P i -> psdmx (F i)) -> psdmx (\sum_(i <- r | P i) F i).
Proof.
move=> FP; elim/big_rec: _ => [|i S Pi SP]; first exact: psdmx0.
exact: psdmxD (FP _ Pi) SP.
Qed.

(* The trace of a product of two positive semidefinite matrices is
   nonnegative. *)
Lemma mxtrace_psd_ge0 n (S T : 'M[R]_n) : psdmx S -> psdmx T ->
  0 <= \tr (S *m T).
Proof.
move=> Sp Tp; have := mxdot_psd_ge0 Sp Tp.
by rewrite mxdot_trace (symmetricmxP _ Tp.1).
Qed.

Lemma frobenius_sqr_sym n (M : 'M[R]_n) : M \is symmetricmx ->
  frobenius M ^+ 2 = \tr (M *m M).
Proof. by move=> /symmetricmxP MT; rewrite frobenius_sqr mxdot_trace MT. Qed.

End orthoprojmx.

Section spectral_projection.
Variable R : realType.
Implicit Types n : nat.

(* A matrix that commutes with diag_mx d commutes with diag_mx (f d). *)
Lemma diag_mx_commute_map n (X : 'M[R]_n) (d : 'rV[R]_n) (f : R -> R) :
  X *m diag_mx d = diag_mx d *m X ->
  X *m diag_mx (map_mx f d) = diag_mx (map_mx f d) *m X.
Proof.
move=> XD; apply/matrixP => i j; rewrite mul_mx_diag mul_diag_mx !mxE.
move/matrixP: XD => /(_ i j); rewrite mul_mx_diag mul_diag_mx !mxE => XE.
have [->|Xij] := eqVneq (X i j) 0; first by rewrite mul0r mulr0.
have dij : d 0 j = d 0 i by apply: (mulfI Xij); rewrite XE mulrC.
by rewrite dij mulrC.
Qed.

Definition nonneg_part (x : R) : R := if 0 <= x then 1 else 0.

(* The spectral projection of a symmetric matrix M onto its nonnegative
   eigenspaces: an orthogonal projection E commuting with M and with every
   matrix that commutes with M, with E M E >= 0 and (1 - E) M (1 - E) <= 0. *)
Lemma spectral_nonneg_proj n (M : 'M[R]_n) : M \is symmetricmx ->
  exists E : 'M[R]_n,
  [/\ orthoprojmx E, E *m M = M *m E,
      psdmx (E *m M *m E), psdmx (- ((1%:M - E) *m M *m (1%:M - E))) &
      forall X : 'M[R]_n, X *m M = M *m X -> X *m E = E *m X].
Proof.
move=> Ms; set U := sym_spectralmx M; set d := sym_spectral_diag M.
have Uo : U \is orthogonalmx := sym_spectralmx_orthogonal M.
have UUT : U *m U^T = 1%:M := orthogonalmxP _ Uo.
have UTU : U^T *m U = 1%:M := orthogonalmxT Uo.
have ME : M = U^T *m diag_mx d *m U := sym_spectralE Ms.
set f := map_mx nonneg_part d.
exists (U^T *m diag_mx f *m U).
have ff : diag_mx f *m diag_mx f = diag_mx f.
  apply/matrixP => i j; rewrite mul_diag_mx !mxE.
  have [->|_] := eqVneq i j; last by rewrite !mulr0n mulr0.
  by rewrite /nonneg_part; case: ifP; rewrite ?mul1r ?mul0r.
have conj (A B : 'M[R]_n) :
    U^T *m A *m U *m (U^T *m B *m U) = U^T *m (A *m B) *m U.
  by rewrite !mulmxA -(mulmxA (U^T *m A) U U^T) UUT mulmx1.
have fd : diag_mx f *m diag_mx d = diag_mx d *m diag_mx f.
  apply/matrixP => i j; rewrite !mul_diag_mx !mxE.
  have [->|_] := eqVneq i j; last by rewrite !mulr0n !mulr0.
  by rewrite !mulr1n mulrC.
split.
- split; last by rewrite conj ff.
  by apply/symmetricmxP; rewrite !trmx_mul trmxK tr_diag_mx mulmxA.
- by rewrite ME conj conj fd.
- rewrite ME !conj.
  have -> : diag_mx f *m diag_mx d *m diag_mx f =
      diag_mx (map_mx (fun x => nonneg_part x * x * nonneg_part x) d).
    apply/matrixP => i j; rewrite mul_mx_diag mul_diag_mx !mxE.
    have [->|_] := eqVneq i j; last by rewrite !mulr0n mulr0 mul0r.
    by rewrite !mulr1n.
  apply: psd_conj => // i; rewrite mxE /nonneg_part.
  case: ifP => x0; first by rewrite mulr1 mul1r.
  by rewrite mulr0.
- have IE : 1%:M - U^T *m diag_mx f *m U = U^T *m (1%:M - diag_mx f) *m U.
    by rewrite mulmxBr mulmxBl mulmx1 UTU.
  have Df : 1%:M - diag_mx f =
      diag_mx (map_mx (fun x => 1 - nonneg_part x) d).
    apply/matrixP => i j; rewrite !mxE.
    by have [->|_] := eqVneq i j; rewrite ?mulr1n ?mulr0n ?subrr.
  rewrite IE ME !conj Df -mulNmx -mulmxN.
  have -> : - (diag_mx (map_mx (fun x => 1 - nonneg_part x) d) *m
      diag_mx d *m diag_mx (map_mx (fun x => 1 - nonneg_part x) d)) =
      diag_mx (map_mx
        (fun x => - ((1 - nonneg_part x) * x * (1 - nonneg_part x))) d).
    apply/matrixP => i j; rewrite mul_mx_diag mul_diag_mx !mxE.
    have [->|_] := eqVneq i j; last by rewrite !mulr0n mulr0 mul0r oppr0.
    by rewrite !mulr1n.
  apply: psd_conj => // i; rewrite mxE /nonneg_part.
  case: ifP => x0; first by rewrite subrr !mul0r oppr0.
  rewrite subr0 mul1r mulr1 oppr_ge0; apply: ltW.
  by rewrite ltNge x0.
- move=> X XM.
  have UMU : U *m M *m U^T = diag_mx d.
    by rewrite ME !mulmxA UUT mul1mx -mulmxA UUT mulmx1.
  have XD : (U *m X *m U^T) *m diag_mx d = diag_mx d *m (U *m X *m U^T).
    rewrite -UMU !mulmxA -(mulmxA (U *m X) U^T U) UTU mulmx1.
    rewrite -(mulmxA (U *m M) U^T U) UTU mulmx1.
    by rewrite -(mulmxA U X M) XM mulmxA.
  have := diag_mx_commute_map nonneg_part XD; rewrite -/f => XF.
  have := congr1 (fun A => U^T *m A *m U) XF; rewrite /=.
  rewrite !mulmxA UTU mul1mx.
  by rewrite -(mulmxA (U^T *m diag_mx f *m U *m X) U^T U) UTU mulmx1.
Qed.

End spectral_projection.

Section two_matrix.
Variable R : realType.
Implicit Types n : nat.

(* Blocks along orthogonal projections are orthogonal for mxdot. *)
Lemma mxdot_block0 n (P1 Q1 P2 Q2 M N : 'M[R]_n) :
  P1 \is symmetricmx -> Q2 \is symmetricmx ->
  P1 *m P2 = 0 \/ Q1 *m Q2 = 0 ->
  mxdot (P1 *m M *m Q1) (P2 *m N *m Q2) = 0.
Proof.
move=> /symmetricmxP P1T /symmetricmxP Q2T [P12|Q12].
  rewrite mxdotC mxdot_trace !trmx_mul P1T.
  by rewrite !mulmxA mxtrace_mulC !mulmxA P12 !mul0mx mxtrace0.
rewrite mxdot_trace !trmx_mul Q2T.
by rewrite !mulmxA -(mulmxA (P1 *m M) Q1 Q2) Q12 mulmx0 !mul0mx mxtrace0.
Qed.

Lemma mxdot_sym_tr n (A B : 'M[R]_n) : B \is symmetricmx ->
  mxdot A B = \tr (A *m B).
Proof. by move=> /symmetricmxP BT; rewrite mxdot_trace BT. Qed.

(* The two-matrix estimate of the lemma 'Orthogonal splitting', relative to
   an orthogonal projection Q: for A, B >= 0 with Q A Q = A and Q B Q = B, the
   projection P = Q E, with E the spectral projection of A - B onto its
   nonnegative eigenspaces, satisfies P <= Q and
   |P B P|_F^2 + |(Q - P) A (Q - P)|_F^2 <= tr (A B). *)
Lemma two_matrix_split n (Q A B : 'M[R]_n) :
  orthoprojmx Q -> psdmx A -> psdmx B ->
  Q *m A *m Q = A -> Q *m B *m Q = B ->
  exists P : 'M[R]_n,
  [/\ orthoprojmx P, P *m Q = P, Q *m P = P &
      frobenius (P *m B *m P) ^+ 2 +
      frobenius ((Q - P) *m A *m (Q - P)) ^+ 2 <= \tr (A *m B)].
Proof.
move=> [Qs QQ] Ap Bp QAQ QBQ.
have QA : Q *m A = A by rewrite -QAQ !mulmxA QQ.
have AQ : A *m Q = A by rewrite -QAQ -mulmxA QQ.
have QB : Q *m B = B by rewrite -QBQ !mulmxA QQ.
have BQ : B *m Q = B by rewrite -QBQ -mulmxA QQ.
set M := A - B.
have Ms : M \is symmetricmx.
  apply/symmetricmxP; rewrite linearB /=.
  by rewrite (symmetricmxP _ Ap.1) (symmetricmxP _ Bp.1).
have [E [[Es EE] EM EMEp NEp Ecomm]] := spectral_nonneg_proj Ms.
have QM : Q *m M = M *m Q by rewrite mulmxBr mulmxBl QA QB AQ BQ.
have QE : Q *m E = E *m Q := Ecomm Q QM.
set P := Q *m E.
have Ps : P \is symmetricmx.
  apply/symmetricmxP; rewrite /P trmx_mul.
  by rewrite (symmetricmxP _ Qs) (symmetricmxP _ Es) QE.
have PP : P *m P = P.
  by rewrite /P mulmxA -(mulmxA Q E Q) -QE mulmxA QQ -mulmxA EE.
have PQ : P *m Q = P by rewrite /P -mulmxA -QE mulmxA QQ.
have QP : Q *m P = P by rewrite /P mulmxA QQ.
exists P; split => //.
set Q' := Q - P.
have [Q's Q'Q'] : orthoprojmx Q' by apply: orthoprojmxB.
have PQ' : P *m Q' = 0 by rewrite /Q' mulmxBr PQ PP subrr.
have Q'P : Q' *m P = 0 by rewrite /Q' mulmxBl QP PP subrr.
have QPQ' : P + Q' = Q by rewrite /Q' addrC subrK.
have Q'E : Q' = Q *m (1%:M - E) by rewrite /Q' /P mulmxBr mulmx1.
have QE' : Q *m (1%:M - E) = (1%:M - E) *m Q.
  by rewrite mulmxBr mulmxBl mulmx1 mul1mx QE.
have PMP : P *m M *m P = Q *m (E *m M *m E) *m Q.
  rewrite /P [in RHS]mulmxA -[in RHS](mulmxA _ E Q) -QE.
  by rewrite !mulmxA.
have Q'MQ' : Q' *m M *m Q' = Q *m ((1%:M - E) *m M *m (1%:M - E)) *m Q.
  rewrite Q'E [in RHS]mulmxA -[in RHS](mulmxA _ (1%:M - E) Q) -QE'.
  by rewrite !mulmxA.
have PMQ : P *m M *m Q = P *m M.
  by rewrite /P -mulmxA -QM mulmxA -(mulmxA Q E Q) -QE mulmxA QQ.
have EME : E *m M *m E = E *m M by rewrite -mulmxA -EM mulmxA EE.
have PMP' : P *m M *m P = P *m M by rewrite PMP EME mulmxA -/P PMQ.
have PMQ' : P *m M *m Q' = 0 by rewrite /Q' mulmxBr PMQ PMP' subrr.
have Q'MP : Q' *m M *m P = 0.
  have := congr1 trmx PMQ'; rewrite trmx0 trmx_mul [(P *m M)^T]trmx_mul.
  by rewrite (symmetricmxP _ Ps) (symmetricmxP _ Ms) (symmetricmxP _ Q's) mulmxA.
have comp (K1 K2 X Y : 'M[R]_n) : orthoprojmx K1 -> orthoprojmx K2 ->
    mxdot (K1 *m X *m K2) (K1 *m Y *m K2) = mxdot X (K1 *m Y *m K2).
  move=> [/symmetricmxP K1T K11] [/symmetricmxP K2T K22].
  rewrite mxdot_mulmxr K2T mxdot_mulmxl K1T.
  by rewrite !mulmxA K11 -!mulmxA K22.
have Po : orthoprojmx P by [].
have Q'o : orthoprojmx Q' by [].
have dec : \tr (A *m B) = mxdot (P *m A *m P) (P *m B *m P) +
    mxdot (P *m A *m Q') (P *m B *m Q') +
    mxdot (Q' *m A *m P) (Q' *m B *m P) +
    mxdot (Q' *m A *m Q') (Q' *m B *m Q').
  clearbody Q'.
  rewrite !comp // -!mxdotDr -(mxdot_sym_tr A Bp.1).
  congr mxdot; rewrite -{1}QBQ -QPQ' mulmxDl !mulmxDr !mulmxDl.
  by rewrite addrACA !addrA.
have offd1 : P *m A *m Q' = P *m B *m Q'.
  by apply/eqP; rewrite -subr_eq0 -mulmxBl -mulmxBr -/M PMQ'.
have offd2 : Q' *m A *m P = Q' *m B *m P.
  by apply/eqP; rewrite -subr_eq0 -mulmxBl -mulmxBr -/M Q'MP.
have h1 : frobenius (P *m B *m P) ^+ 2 <= mxdot (P *m A *m P) (P *m B *m P).
  rewrite frobenius_sqr -subr_ge0 -mxdotBl -mulmxBl -mulmxBr -/M.
  apply: mxdot_psd_ge0; last exact: psdmx_conj Ps Bp.
  by rewrite PMP; exact: psdmx_conj Qs EMEp.
have h2 : frobenius (Q' *m A *m Q') ^+ 2 <=
    mxdot (Q' *m A *m Q') (Q' *m B *m Q').
  rewrite frobenius_sqr -subr_ge0 -mxdotBr -mulmxBl -mulmxBr.
  apply: mxdot_psd_ge0; first exact: psdmx_conj Q's Ap.
  rewrite -opprB -/M mulmxN mulNmx Q'MQ' -mulNmx -mulmxN.
  exact: psdmx_conj Qs NEp.
rewrite dec offd1 offd2; apply: le_trans (lerD h1 h2) _.
rewrite -!addrA lerD2l addrA; apply: ler_wpDl (lexx _).
by rewrite addr_ge0 // mxdot_ge0.
Qed.

End two_matrix.

Section splitting.
Variable R : realType.
Implicit Types n : nat.

Lemma mxdot_compress n (K1 K2 X Y : 'M[R]_n) : orthoprojmx K1 -> orthoprojmx K2 ->
  mxdot (K1 *m X *m K2) (K1 *m Y *m K2) = mxdot X (K1 *m Y *m K2).
Proof.
move=> [/symmetricmxP K1T K11] [/symmetricmxP K2T K22].
rewrite mxdot_mulmxr K2T mxdot_mulmxl K1T.
by rewrite !mulmxA K11 -!mulmxA K22.
Qed.

(* Compressing by a family of orthogonal projections that sums to Q does not
   increase the Frobenius norm of a matrix supported by Q. *)
Lemma frobenius_compress_le n (I : finType) (P : I -> 'M[R]_n) (Q M : 'M[R]_n) :
  (forall s, orthoprojmx (P s)) -> \sum_s P s = Q -> Q *m M *m Q = M ->
  \sum_s frobenius (P s *m M *m P s) ^+ 2 <= frobenius M ^+ 2.
Proof.
move=> Po SP QMQ.
have -> : frobenius M ^+ 2 = \sum_s \sum_t frobenius (P s *m M *m P t) ^+ 2.
  rewrite frobenius_sqr -{2}QMQ -SP mulmx_suml mulmx_sumr mxdot_sumr.
  rewrite [RHS]exchange_big; apply: eq_bigr => t _.
  rewrite mulmx_suml mxdot_sumr; apply: eq_bigr => s _.
  by rewrite frobenius_sqr mxdot_compress.
apply: ler_sum => s _; rewrite (bigD1 s) //= lerDl.
by apply: sumr_ge0 => t _; exact: sqr_ge0.
Qed.

(* For positive semidefinite F i, the sum of the squared norms is at most the
   squared norm of the sum. *)
Lemma frobenius_sum_psd_le n (I : finType) (F : I -> 'M[R]_n) :
  (forall i, psdmx (F i)) ->
  \sum_i frobenius (F i) ^+ 2 <= frobenius (\sum_i F i) ^+ 2.
Proof.
move=> Fp; rewrite frobenius_sqr mxdot_suml.
apply: ler_sum => i _; rewrite mxdot_sumr (bigD1 i) //= frobenius_sqr lerDl.
by apply: sumr_ge0 => j _; exact: mxdot_psd_ge0.
Qed.

(* A sum over the ordered pairs of distinct indices of 'I_L.+2, split at the
   index ord0. *)
Lemma sum_offdiag_recl (V : nmodType) L (F : 'I_L.+2 -> 'I_L.+2 -> V) :
  \sum_z \sum_(s | s != z) F z s =
  \sum_j F ord0 (lift ord0 j) + \sum_j F (lift ord0 j) ord0 +
  \sum_j \sum_(i | i != j) F (lift ord0 j) (lift ord0 i).
Proof.
have l0 (j : 'I_L.+1) : (lift ord0 j != ord0) = true.
  by apply/idP; rewrite eq_sym neq_lift.
rewrite big_ord_recl -addrA; congr (_ + _).
  by rewrite big_mkcond big_ord_recl eqxx /= add0r.
rewrite -big_split /=; apply: eq_bigr => j _.
rewrite big_mkcond big_ord_recl eq_sym l0 /=; congr (_ + _).
rewrite [RHS]big_mkcond; apply: eq_bigr => i _.
by rewrite (inj_eq (@lift_inj _ ord0)).
Qed.

Lemma trace_quad_ge0 n (A B X : 'M[R]_n) : psdmx A -> psdmx B ->
  X \is symmetricmx -> 0 <= \tr (A *m X *m B *m X).
Proof.
move=> Ap Bp Xs; rewrite -!mulmxA [X *m (B *m X)]mulmxA.
exact: mxtrace_psd_ge0 Ap (psdmx_conj Xs Bp).
Qed.

(* The squared triangle inequality for the nonnegative quadratic form
   X |-> tr (A X B X) on symmetric matrices. *)
Lemma trace_quad_sub_le n (A B Q P : 'M[R]_n) : psdmx A -> psdmx B ->
  Q \is symmetricmx -> P \is symmetricmx ->
  \tr (A *m (Q - P) *m B *m (Q - P)) <=
  2 * \tr (A *m Q *m B *m Q) + 2 * \tr (A *m P *m B *m P).
Proof.
move=> Ap Bp Qs Ps.
have QPs : Q + P \is symmetricmx.
  apply/symmetricmxP; rewrite linearD /=.
  by rewrite (symmetricmxP _ Qs) (symmetricmxP _ Ps).
have h := trace_quad_ge0 Ap Bp QPs.
rewrite !mulmxDr ?mulmxDl ?mulmxDr ?mulmxDl ?mxtraceD in h.
rewrite !mulmxBr ?mulmxBl ?mulmxBr ?mulmxBl ?linearB /=.
move: h; set a := \tr (A *m Q *m B *m Q); set b := \tr (A *m P *m B *m Q).
set c := \tr (A *m Q *m B *m P); set d := \tr (A *m P *m B *m P).
move=> h; lra.
Qed.

(* The lemma 'Orthogonal splitting', relative to an orthogonal projection Q:
   for L + 1 positive semidefinite matrices, orthogonal projections P_s that
   sum to Q, with constant 2^L for the overlaps tr (A_z Q A_z' Q). *)
Theorem psd_splitting_rel n L (Q : 'M[R]_n) (A : 'I_L.+1 -> 'M[R]_n) :
  orthoprojmx Q -> (forall z, psdmx (A z)) ->
  exists P : 'I_L.+1 -> 'M[R]_n,
  [/\ forall s, orthoprojmx (P s),
      forall s t, s != t -> P s *m P t = 0,
      \sum_s P s = Q &
      \sum_z \sum_(s | s != z) frobenius (P s *m A z *m P s) ^+ 2 <=
        2 ^+ L * \sum_z \sum_(z' | z' != z) \tr (A z *m Q *m A z' *m Q)].
Proof.
elim: L Q A => [|L IH] Q A Qo Ap.
  exists (fun=> Q); split => //.
  - by move=> s t; rewrite !ord1 eqxx.
  - by rewrite big_ord1.
  by rewrite !big_ord1 !big_pred0 ?mulr0 // => s; rewrite !ord1 eqxx.
case: (Qo) => Qs QQ.
set A0 := A ord0.
set A' := fun j : 'I_L.+1 => A (lift ord0 j).
have A'p j : psdmx (A' j) := Ap _.
set At := Q *m A0 *m Q.
set Bt := \sum_j Q *m A' j *m Q.
have Atp : psdmx At := psdmx_conj Qs (Ap _).
have Btp : psdmx Bt by apply: psdmx_sum => j _; exact: psdmx_conj Qs (A'p j).
have QAtQ : Q *m At *m Q = At by rewrite /At !mulmxA QQ -(mulmxA _ Q Q) QQ.
have QBtQ : Q *m Bt *m Q = Bt.
  rewrite /Bt mulmx_sumr mulmx_suml; apply: eq_bigr => j _.
  by rewrite !mulmxA QQ -(mulmxA _ Q Q) QQ.
have [P [Po PQ QP Ptwo]] := two_matrix_split Qo Atp Btp QAtQ QBtQ.
set Q' := Q - P.
have Q'o : orthoprojmx Q' := orthoprojmxB Qo Po PQ QP.
have [P' [P'o P'orth P'sum P'bound]] := IH Q' A' Q'o A'p.
rewrite -/Q' in Ptwo.
case: (Po) => Ps PP; case: (Q'o) => Q's Q'Q'.
have Q'Q : Q' *m Q = Q' by rewrite /Q' mulmxBl QQ PQ.
have QQ' : Q *m Q' = Q' by rewrite /Q' mulmxBr QQ QP.
have PQ' : P *m Q' = 0 by rewrite /Q' mulmxBr PQ PP subrr.
have Q'P : Q' *m P = 0 by rewrite /Q' mulmxBl QP PP subrr.
have P'Q' j : P' j *m Q' = P' j.
  rewrite -P'sum mulmx_sumr (bigD1 j) //= (P'o j).2 big1 ?addr0 // => i ij.
  by apply: P'orth; rewrite eq_sym.
have Q'P' j : Q' *m P' j = P' j.
  rewrite -P'sum mulmx_suml (bigD1 j) //= (P'o j).2 big1 ?addr0 // => i ij.
  exact: P'orth.
have P'Q j : P' j *m Q = P' j by rewrite -{1}P'Q' -mulmxA Q'Q P'Q'.
have QP' j : Q *m P' j = P' j by rewrite -{1}Q'P' mulmxA QQ' Q'P'.
have PP' j : P *m P' j = 0 by rewrite -Q'P' mulmxA PQ' mul0mx.
have P'P j : P' j *m P = 0 by rewrite -P'Q' -mulmxA Q'P mulmx0.
pose Pn (s : 'I_L.+2) := if unlift ord0 s is Some j then P' j else P.
have Pn0 : Pn ord0 = P by rewrite /Pn unlift_none.
have PnS j : Pn (lift ord0 j) = P' j by rewrite /Pn liftK.
exists Pn; split.
- by move=> s; case: (unliftP ord0 s) => [j ->|->]; rewrite ?PnS ?Pn0.
- move=> s t; case: (unliftP ord0 s) => [i ->|->];
    case: (unliftP ord0 t) => [j ->|->].
  + by rewrite (inj_eq (@lift_inj _ ord0)) !PnS; exact: P'orth.
  + by rewrite PnS Pn0 P'P.
  + by rewrite PnS Pn0 PP'.
  + by rewrite eqxx.
- rewrite big_ord_recl Pn0; under eq_bigr do rewrite PnS.
  by rewrite P'sum /Q' addrC subrK.
rewrite (sum_offdiag_recl (fun z s => frobenius (Pn s *m A z *m Pn s) ^+ 2)) /=.
rewrite (sum_offdiag_recl (fun z z' => \tr (A z *m Q *m A z' *m Q))) /=.
rewrite [in X in _ + X + _]Pn0.
under [X in X + _ + _]eq_bigr do rewrite PnS.
under [X in _ + X <= _]eq_bigr do under eq_bigr do rewrite PnS.
rewrite -/A0.
set T := \sum_(j < L.+1) \tr (A0 *m Q *m A (lift ord0 j) *m Q).
set S' := \sum_(j < L.+1) \sum_(i < L.+1 | i != j)
  \tr (A (lift ord0 j) *m Q *m A (lift ord0 i) *m Q).
have TC : \sum_(j < L.+1) \tr (A (lift ord0 j) *m Q *m A0 *m Q) = T.
  by apply: eq_bigr => j _; rewrite -mulmxA mxtrace_mulC !mulmxA.
have TAB : \tr (At *m Bt) = T.
  rewrite /At /Bt mulmx_sumr linear_sum /=; apply: eq_bigr => j _.
  rewrite !mulmxA -(mulmxA _ Q Q) QQ mxtrace_mulC !mulmxA.
  by rewrite QQ -!mulmxA mxtrace_mulC !mulmxA.
rewrite TC; rewrite TAB in Ptwo.
have T0 : 0 <= T by rewrite -TAB; exact: mxtrace_psd_ge0.
have b1 : \sum_(i < L.+1) frobenius (P' i *m A0 *m P' i) ^+ 2 <=
    frobenius (Q' *m At *m Q') ^+ 2.
  have -> : \sum_(i < L.+1) frobenius (P' i *m A0 *m P' i) ^+ 2 =
      \sum_(i < L.+1) frobenius (P' i *m (Q' *m At *m Q') *m P' i) ^+ 2.
    apply: eq_bigr => i _; congr (frobenius _ ^+ 2).
    rewrite /At !mulmxA P'Q' P'Q -(mulmxA _ Q Q') QQ'.
    by rewrite -(mulmxA _ Q' (P' i)) Q'P'.
  apply: frobenius_compress_le => //.
  by rewrite P'sum !mulmxA Q'Q' -!mulmxA Q'Q'.
have b2 : \sum_(j < L.+1) frobenius (P *m A (lift ord0 j) *m P) ^+ 2 <=
    frobenius (P *m Bt *m P) ^+ 2.
  have -> : P *m Bt *m P = \sum_(j < L.+1) P *m A (lift ord0 j) *m P.
    rewrite /Bt mulmx_sumr mulmx_suml; apply: eq_bigr => j _.
    by rewrite !mulmxA PQ -mulmxA QP.
  by apply: frobenius_sum_psd_le => j; exact: psdmx_conj Ps (A'p j).
set SP := \sum_(j < L.+1) \sum_(i < L.+1 | i != j)
  \tr (A (lift ord0 j) *m P *m A (lift ord0 i) *m P).
have b3 : \sum_(j < L.+1) \sum_(i < L.+1 | i != j)
    frobenius (P' i *m A (lift ord0 j) *m P' i) ^+ 2 <=
    2 ^+ L * (2 * S' + 2 * SP).
  apply: (le_trans P'bound); apply: ler_wpM2l; first exact: exprn_ge0.
  rewrite /S' /SP !mulr_sumr -big_split /=; apply: ler_sum => j _.
  rewrite !mulr_sumr -big_split /=; apply: ler_sum => i _.
  exact: trace_quad_sub_le (A'p j) (A'p i) Qs Ps.
have PBP : P *m Bt *m P = \sum_(j < L.+1) P *m A (lift ord0 j) *m P.
  rewrite /Bt mulmx_sumr mulmx_suml; apply: eq_bigr => j _.
  by rewrite !mulmxA PQ -mulmxA QP.
have b5 : SP <= frobenius (P *m Bt *m P) ^+ 2.
  have -> : frobenius (P *m Bt *m P) ^+ 2 = \sum_(j < L.+1) \sum_(i < L.+1)
      \tr (A (lift ord0 j) *m P *m A (lift ord0 i) *m P).
    rewrite PBP frobenius_sqr mxdot_suml; apply: eq_bigr => j _.
    rewrite mxdot_sumr; apply: eq_bigr => i _.
    rewrite mxdot_compress // mxdot_sym_tr ?mulmxA //.
    exact: (psdmx_conj Ps (A'p i)).1.
  apply: ler_sum => j _; rewrite [X in _ <= X](bigD1 j) //=.
  by apply: ler_wpDl (lexx _); exact: trace_quad_ge0 (A'p j) (A'p j) Ps.
rewrite exprS; set c := 2 ^+ L.
have c1 : 1 <= c by rewrite /c exprn_ege1 // ler1n.
have f10 : 0 <= frobenius (Q' *m At *m Q') ^+ 2 := sqr_ge0 _.
have SPT : SP <= T.
  apply: (le_trans b5); apply: le_trans Ptwo; exact: ler_wpDr f10 (lexx _).
have cSP : c * SP <= c * T := ler_wpM2l (le_trans ler01 c1) SPT.
have cT : T <= c * T := ler_peMl T0 c1.
have cT0 : 0 <= c * T := mulr_ge0 (le_trans ler01 c1) T0.
have b3' : \sum_(j < L.+1) \sum_(i < L.+1 | i != j)
    frobenius (P' i *m A (lift ord0 j) *m P' i) ^+ 2 <=
    2 * (c * S') + 2 * (c * SP).
  by rewrite mulrCA [2 * (c * SP)]mulrCA -mulrDr; exact: b3.
rewrite -!mulrA !mulrDr.
move: b1 b2 b3' Ptwo b5 cSP cT cT0.
set x1 := \sum_(i < L.+1) frobenius (P' i *m A0 *m P' i) ^+ 2.
set x2 := \sum_(j < L.+1) frobenius (P *m A (lift ord0 j) *m P) ^+ 2.
set x3 := \sum_(j < L.+1) \sum_(i < L.+1 | i != j)
  frobenius (P' i *m A (lift ord0 j) *m P' i) ^+ 2.
set f1 := frobenius (Q' *m At *m Q') ^+ 2.
set f2 := frobenius (P *m Bt *m P) ^+ 2.
set cS := c * S'; set cSP' := c * SP; set cT' := c * T.
move=> b1 b2 b3' Ptwo b5 cSP cT cT0; lra.
Qed.

(* The lemma 'Orthogonal splitting': for L + 1 positive semidefinite
   matrices A_z, orthogonal projections P_s, possibly zero, that are mutually
   orthogonal and sum to the identity, with the sum over z and s != z of
   |P_s A_z P_s|_F^2 at most 2^L times the sum over the ordered pairs z != z'
   of tr (A_z A_z'). *)
Theorem psd_splitting n L (A : 'I_L.+1 -> 'M[R]_n) : (forall z, psdmx (A z)) ->
  exists P : 'I_L.+1 -> 'M[R]_n,
  [/\ forall s, orthoprojmx (P s),
      forall s t, s != t -> P s *m P t = 0,
      \sum_s P s = 1%:M &
      \sum_z \sum_(s | s != z) frobenius (P s *m A z *m P s) ^+ 2 <=
        2 ^+ L * \sum_z \sum_(z' | z' != z) \tr (A z *m A z')].
Proof.
move=> Ap; have [P [Po Porth Psum Pb]] := psd_splitting_rel (@orthoprojmx1 R n) Ap.
exists P; split => //; move: Pb.
by under [X in _ <= _ * X -> _]eq_bigr do under eq_bigr do rewrite !mulmx1.
Qed.

End splitting.
