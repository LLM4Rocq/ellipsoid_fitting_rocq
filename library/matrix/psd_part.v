From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import poly polydiv mxpoly.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.matrix Require Import von_neumann.

(**md**************************************************************************)
(* # The positive part of a symmetric matrix                                  *)
(*                                                                            *)
(* For a real symmetric matrix A with a spectral decomposition                *)
(* A = P^T diag(d) P, P orthogonal, the positive part                         *)
(* psd_part A = P^T diag((d_i)_+) P is the nearest positive semidefinite      *)
(* matrix to A in the Frobenius norm. It is defined from the decomposition    *)
(* chosen by sym_spectralmx and sym_spectral_diag of real_spectral.v, and     *)
(* does not depend on that choice (psd_partE).                                *)
(*                                                                            *)
(* G8 (Koehler and Sohn, Lemma 5.14 and Proposition 5.15) handles spectral    *)
(* functions through psd_part, which is equivariant under orthogonal          *)
(* conjugation: Lemma 5.13 (random_matrix/goe_rotation.v) can be stated for   *)
(* any F with F (Q W Q^T) = Q F(W) Q^T for every orthogonal Q, such as        *)
(* W |-> psd_part (W - w(W) I) for a w(W) that depends only on the spectrum.  *)
(*                                                                            *)
(* - psd_conj: P^T diag(d) P >= 0 for d >= 0; mxdot_psd_ge0: <S, T> >= 0      *)
(*   for S, T >= 0.                                                           *)
(* - psd_nearest: for A = P^T diag(d) P and S >= 0,                           *)
(*   |A - S|^2 >= |A - A_+|^2 + |A_+ - S|^2; psd_part_nearest, psd_part A     *)
(*   is the nearest positive semidefinite matrix; psd_partE, psd_part A =     *)
(*   P^T diag((d_i)_+) P for every spectral decomposition; psd_part_psd.      *)
(* - psd_part_conj: psd_part (Q A Q^T) = Q (psd_part A) Q^T, Q orthogonal.    *)
(* - psd_part_moreau: A = psd_part A - psd_part (- A) with                    *)
(*   <psd_part A, psd_part (- A)> = 0.                                        *)
(* - psd_part_nonexpansive: |psd_part A - psd_part B|_F <= |A - B|_F.         *)
(* - spec_shift_decomposition, trace_psd_part_shift and                       *)
(*   frobenius_psd_part_shift: tr psd_part (A - w I) = sum_i (spec A i - w)_+ *)
(*   and |psd_part (A - w I)|_F^2 = sum_i (spec A i - w)_+^2, with spec of    *)
(*   matrix/von_neumann.v; mxdot_psd_part_shift:                              *)
(*   <A, psd_part (A - w I)> = sum_i spec A i (spec A i - w)_+.               *)
(* - char_poly_conj_diag, spec_conj_diag: P^T diag(v) P has the               *)
(*   characteristic polynomial prod_i (X - v_i), so its sorted spectrum is v  *)
(*   when v is decreasing; spec_scale: spec (c A) = c spec A for c >= 0.      *)
(* - spec_psd_ge0, sum_spec_trace: the eigenvalues of a positive              *)
(*   semidefinite matrix are nonnegative; they sum to the trace.              *)
(* - mxdot_spec_le: von Neumann's inequality for the Frobenius pairing,       *)
(*   <A, B> <= sum_i spec A i spec B i for A and B symmetric.                 *)
(*                                                                            *)
(* ```                                                                        *)
(*        psdmx A == A is symmetric with x^T A x >= 0 for every x             *)
(*      pos_row d == the row of the (d_i)_+                                   *)
(*     psd_part A == the positive part of A                                   *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section psd_part.
Variable R : realType.
Implicit Types n : nat.

(* A >= 0: symmetric with nonnegative quadratic forms. *)
Definition psdmx n (A : 'M[R]_n) : Prop :=
  A \is symmetricmx /\ forall x : 'cV[R]_n, 0 <= mxdot x (A *m x).

Definition pos_row n (d : 'rV[R]_n) : 'rV[R]_n := \row_i Num.max (d 0 i) 0.

Definition psd_part n (A : 'M[R]_n) : 'M[R]_n :=
  (sym_spectralmx A)^T *m diag_mx (pos_row (sym_spectral_diag A)) *m
  sym_spectralmx A.

Lemma psd_conj n (P : 'M[R]_n) (d : 'rV[R]_n) : P \is orthogonalmx ->
  (forall i, 0 <= d 0 i) -> psdmx (P^T *m diag_mx d *m P).
Proof.
move=> Po d0; split.
  rewrite -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
exact: (spectral_psd Po (erefl _)).2 d0.
Qed.

(* <S, T> >= 0 for S, T >= 0. *)
Lemma mxdot_psd_ge0 n (S T : 'M[R]_n) : psdmx S -> psdmx T -> 0 <= mxdot S T.
Proof.
move=> [_ Spsd] [Tsym Tpsd].
(* T = P^T diag(dv) P with dv >= 0, so <S, T> = sum_i (P S P^T)_ii dv_i *)
have [P Po [dv TE]] := symmetric_spectral Tsym.
have d0 i : 0 <= dv 0 i := (spectral_psd Po TE).1 Tpsd i.
have E : mxdot S T = \sum_i (P *m S *m P^T) i i * dv 0 i.
  rewrite mxdot_trace; have /symmetricmxP -> := Tsym.
  rewrite TE mulmxA mulmxA mxtrace_mulC !mulmxA.
  by apply: eq_bigr => i _; rewrite mul_mx_diag mxE.
rewrite E; apply: sumr_ge0 => i _; apply: mulr_ge0 => //.
have -> : (P *m S *m P^T) i i = mxdot (row i P)^T (S *m (row i P)^T).
  rewrite mxdot_colE trmxK -row_mul !mxE.
  have e1 : \sum_j (P *m S) i j * P^T j i =
      \sum_j \sum_k P i k * S k j * P i j.
    by apply: eq_bigr => j _; rewrite !mxE big_distrl.
  have e2 : \sum_j P i j * (S *m (row i P)^T) j 0 =
      \sum_j \sum_k P i j * S j k * P i k.
    apply: eq_bigr => j _; rewrite !mxE big_distrr.
    by apply: eq_bigr => k _ /=; rewrite !mxE mulrA.
  rewrite e1 e2 exchange_big; apply: eq_bigr => j _; apply: eq_bigr => k _.
  by rewrite mulrAC.
exact: Spsd.
Qed.

(* The decomposition A = A_+ - A_- for any spectral decomposition, with
   A_+, A_- >= 0 and <A_+, A_-> = 0, and the nearest-point inequality
   |A - S|^2 >= |A - A_+|^2 + |A_+ - S|^2 for S >= 0. *)
Lemma psd_nearest n (P : 'M[R]_n) (d : 'rV[R]_n) (S : 'M[R]_n) :
  P \is orthogonalmx -> psdmx S ->
  mxdot (P^T *m diag_mx d *m P - S) (P^T *m diag_mx d *m P - S) >=
  mxdot (P^T *m diag_mx d *m P - P^T *m diag_mx (pos_row d) *m P)
        (P^T *m diag_mx d *m P - P^T *m diag_mx (pos_row d) *m P) +
  mxdot (P^T *m diag_mx (pos_row d) *m P - S)
        (P^T *m diag_mx (pos_row d) *m P - S).
Proof.
move=> Po Spsd.
(* A = A_+ - A_- with A_- = P^T diag ((- d_i)_+) P *)
pose neg_row : 'rV[R]_n := \row_i Num.max (- d 0 i) 0.
set A := P^T *m diag_mx d *m P.
set Ap := P^T *m diag_mx (pos_row d) *m P.
pose Am := P^T *m diag_mx neg_row *m P.
have dE : d = pos_row d - neg_row.
  apply/rowP => i; rewrite !mxE; case: (lerP 0 (d 0 i)) => h.
    have h' : - d 0 i <= 0 by rewrite oppr_le0.
    by rewrite (max_idPr h') subr0.
  have h' : 0 <= - d 0 i by rewrite oppr_ge0 ltW.
  by rewrite (max_idPl h') sub0r opprK.
have AE : A = Ap - Am.
  by rewrite /A /Ap /Am {1}dE linearB /= mulmxBr mulmxBl.
have Am0 : psdmx Am.
  by apply: psd_conj => // i; rewrite mxE le_max lexx orbT.
have ApAm : mxdot Ap Am = 0.
  rewrite /Ap /Am mxdot_orthogonalmxr // mxdot_orthogonalmxl ?trmx_orthogonal //.
  rewrite mxdot_diag big1 // => i _; rewrite !mxE.
  case: (lerP 0 (d 0 i)) => h; last by rewrite mul0r.
  have h' : - d 0 i <= 0 by rewrite oppr_le0.
  by rewrite (max_idPr h') mulr0.
(* |A - S|^2 = |A_+ - S|^2 + |A_-|^2 + 2 <S, A_-> and <S, A_-> >= 0 *)
have key : mxdot (A - S) (A - S) =
    mxdot (Ap - S) (Ap - S) + mxdot Am Am + 2 * mxdot S Am.
  rewrite AE !mxdotBl !mxdotBr (mxdotC Am Ap) (mxdotC Am S) ApAm.
  by ring.
have AAp : A - Ap = - Am by rewrite AE addrAC subrr add0r.
rewrite AAp mxdotNl mxdotNr opprK key [X in X <= _]addrC lerDl.
by apply: mulr_ge0 => //; exact: mxdot_psd_ge0.
Qed.

(* psd_part does not depend on the spectral decomposition. *)
Lemma psd_partE n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  psd_part A = P^T *m diag_mx (pos_row d) *m P.
Proof.
move=> Po AE.
have Asym : A \is symmetricmx.
  rewrite AE -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
have P0o := sym_spectralmx_orthogonal A.
have A0E := sym_spectralE Asym.
rewrite /psd_part.
set P0 := sym_spectralmx A in P0o A0E *.
set d0 := sym_spectral_diag A in A0E *.
(* both candidates are nearest points of A, hence equal *)
set Q := P0^T *m diag_mx (pos_row d0) *m P0.
set Q' := P^T *m diag_mx (pos_row d) *m P.
have Qp : psdmx Q by apply: psd_conj => // i; rewrite mxE le_max lexx orbT.
have Q'p : psdmx Q' by apply: psd_conj => // i; rewrite mxE le_max lexx orbT.
have h1 := psd_nearest d0 P0o Q'p.
have h2 := psd_nearest d Po Qp.
rewrite -A0E -/Q in h1; rewrite -AE -/Q' in h2.
have e : mxdot (Q' - Q) (Q' - Q) = mxdot (Q - Q') (Q - Q').
  by rewrite -opprB mxdotNl mxdotNr opprK.
rewrite e in h2.
apply/eqP; rewrite -subr_eq0 -mxdot_eq0 eq_le mxdot_ge0 andbT.
lra.
Qed.

Lemma psd_part_psd n (A : 'M[R]_n) : psdmx (psd_part A).
Proof.
by apply: psd_conj; [exact: sym_spectralmx_orthogonal | move=> i; rewrite mxE le_max lexx orbT].
Qed.

(* The nearest positive semidefinite matrix. *)
Theorem psd_part_nearest n (A S : 'M[R]_n) : A \is symmetricmx -> psdmx S ->
  frobenius (A - psd_part A) <= frobenius (A - S).
Proof.
move=> Asym Sp.
have Po := sym_spectralmx_orthogonal A.
have AE := sym_spectralE Asym.
have h := psd_nearest (sym_spectral_diag A) Po Sp.
rewrite -AE -/(psd_part A) in h.
rewrite /frobenius ler_sqrt ?mxdot_ge0 //.
by apply: le_trans h; rewrite lerDl; exact: mxdot_ge0.
Qed.

Lemma psd_part_conj n (A Q : 'M[R]_n) : A \is symmetricmx -> Q \is orthogonalmx ->
  psd_part (Q *m A *m Q^T) = Q *m psd_part A *m Q^T.
Proof.
move=> Asym Qo.
have Po := sym_spectralmx_orthogonal A.
have AE := sym_spectralE Asym.
set P := sym_spectralmx A in Po AE *.
set d := sym_spectral_diag A in AE *.
(* Q A Q^T = (P Q^T)^T diag(d) (P Q^T) *)
have PQo : P *m Q^T \is orthogonalmx.
  by apply: mul_orthogonalmx => //; rewrite trmx_orthogonal.
rewrite (@psd_partE _ _ (P *m Q^T) d PQo).
  by rewrite {1}AE trmx_mul trmxK !mulmxA.
by rewrite /psd_part -/P -/d trmx_mul trmxK !mulmxA.
Qed.

(* Moreau's decomposition. *)
Lemma psd_part_moreau n (A : 'M[R]_n) : A \is symmetricmx ->
  A = psd_part A - psd_part (- A) /\ mxdot (psd_part A) (psd_part (- A)) = 0.
Proof.
move=> Asym.
have Po := sym_spectralmx_orthogonal A.
have AE := sym_spectralE Asym.
set P := sym_spectralmx A in Po AE *.
set d := sym_spectral_diag A in AE *.
have NE : - A = P^T *m diag_mx (- d) *m P.
  by rewrite {1}AE linearN /= mulmxN mulNmx.
have Ap : psd_part A = P^T *m diag_mx (pos_row d) *m P by [].
rewrite (psd_partE Po NE) Ap; split.
  (* d = (d)_+ - (- d)_+ *)
  rewrite {1}AE -mulmxBl -mulmxBr -linearB /=; congr (_ *m diag_mx _ *m _).
  apply/rowP => i; rewrite !mxE; case: (lerP 0 (d 0 i)) => h.
    have h' : - d 0 i <= 0 by rewrite oppr_le0.
    by rewrite (max_idPr h') subr0.
  have h' : 0 <= - d 0 i by rewrite oppr_ge0 ltW.
  by rewrite (max_idPl h') sub0r opprK.
(* (d_i)_+ (- d_i)_+ = 0 *)
rewrite mxdot_orthogonalmxr // mxdot_orthogonalmxl ?trmx_orthogonal //.
rewrite mxdot_diag big1 // => i _; rewrite !mxE.
case: (lerP 0 (d 0 i)) => h; last by rewrite mul0r.
have h' : - d 0 i <= 0 by rewrite oppr_le0.
by rewrite (max_idPr h') mulr0.
Qed.

Lemma psd_part_nonexpansive n (A B : 'M[R]_n) :
  A \is symmetricmx -> B \is symmetricmx ->
  frobenius (psd_part A - psd_part B) <= frobenius (A - B).
Proof.
move=> As Bs.
(* the variational inequality <X - X_+, S - X_+> <= 0 for S >= 0 *)
have var (X S : 'M[R]_n) : X \is symmetricmx -> psdmx S ->
    mxdot (X - psd_part X) (S - psd_part X) <= 0.
  move=> Xs Sp; have [XE orth] := psd_part_moreau Xs.
  have -> : X - psd_part X = - psd_part (- X).
    by rewrite {1}XE addrAC subrr add0r.
  rewrite mxdotNl mxdotBr [mxdot _ (psd_part X)]mxdotC orth subr0 oppr_le0.
  by rewrite mxdotC; exact: mxdot_psd_ge0 Sp (psd_part_psd _).
have h1 := var A (psd_part B) As (psd_part_psd B).
have h2 := var B (psd_part A) Bs (psd_part_psd A).
set Ap := psd_part A in h1 h2 *; set Bp := psd_part B in h1 h2 *.
have key : mxdot (Ap - Bp) (Ap - Bp) <= mxdot (A - B) (Ap - Bp).
  move: h1 h2; rewrite !mxdotBl !mxdotBr ?(mxdotC Bp Ap) ?(mxdotC Ap A).
  by rewrite ?(mxdotC Bp A) ?(mxdotC Ap B) ?(mxdotC Bp B); lra.
have cs := ler_mxdot (A - B) (Ap - Bp).
have [->|f0] := eqVneq (frobenius (Ap - Bp)) 0; first exact: frobenius_ge0.
have fp : 0 < frobenius (Ap - Bp) by rewrite lt_def f0 frobenius_ge0.
rewrite -(ler_pM2r fp) -expr2 frobenius_sqr.
exact: le_trans key cs.
Qed.

(* A - w I = P^T diag (spec A - w) P. *)
Lemma spec_shift_decomposition n (A : 'M[R]_n) (w : R) : A \is symmetricmx ->
  exists2 P : 'M[R]_n, P \is orthogonalmx &
    A - w%:M = P^T *m diag_mx (spec A - const_mx w) *m P.
Proof.
move=> As; have [P Po AE] := spec_decomposition As.
exists P => //; rewrite {1}AE linearB /= mulmxBr mulmxBl; congr (_ - _).
rewrite diag_const_mx mul_mx_scalar -scalemxAl.
have : P^T \is orthogonalmx by rewrite trmx_orthogonal.
by move/orthogonalmxP; rewrite trmxK => ->; rewrite scalemx1.
Qed.

(* The trace and the squared Frobenius norm of the shifted positive part, as
   spectral statistics. *)
Lemma trace_psd_part_shift n (A : 'M[R]_n) (w : R) : A \is symmetricmx ->
  \tr (psd_part (A - w%:M)) = \sum_i Num.max (spec A 0 i - w) 0.
Proof.
move=> As; have [P Po E] := spec_shift_decomposition w As.
rewrite (psd_partE Po E) (spectral_trace Po (erefl _)).
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

Lemma frobenius_psd_part_shift n (A : 'M[R]_n) (w : R) : A \is symmetricmx ->
  frobenius (psd_part (A - w%:M)) ^+ 2 = \sum_i Num.max (spec A 0 i - w) 0 ^+ 2.
Proof.
move=> As; have [P Po E] := spec_shift_decomposition w As.
rewrite (psd_partE Po E) frobenius_sqr (spectral_mxdot Po (erefl _)).
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

End psd_part.

(* The spectrum of conjugates of diagonal matrices. *)

Section spec_conj.
Variable R : realType.
Implicit Types n : nat.

(* The characteristic polynomial of P^T diag(v) P, P orthogonal. *)
Lemma char_poly_conj_diag n (P : 'M[R]_n) (v : 'rV[R]_n) :
  P \is orthogonalmx ->
  char_poly (P^T *m diag_mx v *m P) = \prod_i ('X - (v 0 i)%:P).
Proof.
move=> Po; pose f := @polyC R.
have PTP : P^T *m P = 1%:M.
  by have := trmx_orthogonal P; rewrite Po => /orthogonalmxP; rewrite trmxK.
have M1 : map_mx f P^T *m map_mx f P = 1%:M by rewrite -map_mxM PTP map_mx1.
have cE : char_poly_mx (P^T *m diag_mx v *m P) =
    map_mx f P^T *m char_poly_mx (diag_mx v) *m map_mx f P.
  rewrite /char_poly_mx mulmxBr mulmxBl -!map_mxM.
  rewrite (scalar_mxC 'X (map_mx f P^T)).
  by rewrite -[_ *m map_mx f P]mulmxA M1 mulmx1.
have D1 : \det (map_mx f P^T) * \det (map_mx f P) = 1.
  by rewrite -det_mulmx M1 det1.
rewrite /char_poly cE !det_mulmx mulrAC D1 mul1r.
rewrite -/(char_poly (diag_mx v)) char_poly_trig ?diag_mx_is_trig //.
by apply: eq_bigr => i _; rewrite mxE eqxx mulr1n.
Qed.

(* The spectrum of P^T diag(v) P is v when v is decreasing: the
   characteristic polynomial determines the eigenvalues with their
   multiplicities. *)
Lemma spec_conj_diag n (P : 'M[R]_n) (v : 'rV[R]_n) : P \is orthogonalmx ->
  (forall i j : 'I_n, (i <= j)%N -> v 0 j <= v 0 i) ->
  spec (P^T *m diag_mx v *m P) = v.
Proof.
move=> Po vdecr; set A := P^T *m diag_mx v *m P.
have Asym : A \is symmetricmx.
  rewrite /A -{2}[P]trmxK symmetricmx_conj //.
  by apply/symmetricmxP; rewrite tr_diag_mx.
have AE := sym_spectralE Asym.
have Qo := sym_spectralmx_orthogonal A.
set Q := sym_spectralmx A in AE Qo; set D := sym_spectral_diag A in AE.
have cp : \prod_(x <- [seq D 0 i | i <- enum 'I_n]) ('X - x%:P) =
    \prod_(x <- [seq v 0 i | i <- enum 'I_n]) ('X - x%:P).
  rewrite !big_map.
  by rewrite -(char_poly_conj_diag D Qo) -(char_poly_conj_diag v Po) -AE.
have pe := prod_XsubC_eq cp.
have sv : sorted (fun x y : R => y <= x) [seq v 0 i | i <- enum 'I_n].
  rewrite sorted_map; apply: (@sub_sorted _ (relpre val leq)).
    by move=> i j /= ij; exact: vdecr.
  by rewrite -sorted_map val_enum_ord iota_sorted.
have ge_tr : transitive (fun x y : R => y <= x).
  by move=> y x z yx zy; exact: le_trans zy yx.
have ge_tot : total (fun x y : R => y <= x) by move=> x y; exact: le_total.
have ge_anti : antisymmetric (fun x y : R => y <= x).
  by move=> x y /andP[yx xy]; apply/eqP; rewrite eq_le xy yx.
have sE : spec_seq A = [seq v 0 i | i <- enum 'I_n].
  rewrite /spec_seq -/D (perm_sortP ge_tot ge_tr ge_anti _ _ pe).
  exact: sorted_sort.
apply/rowP => i; rewrite mxE sE (nth_map i) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Lemma spec_scale n (A : 'M[R]_n) (c : R) : A \is symmetricmx -> 0 <= c ->
  spec (c *: A) = c *: spec A.
Proof.
move=> As c0; have [P Po AE] := spec_decomposition As.
have -> : c *: A = P^T *m diag_mx (c *: spec A) *m P.
  by rewrite {1}AE linearZ /= -scalemxAr -scalemxAl.
apply: spec_conj_diag => // i j ij; rewrite !mxE.
by apply: ler_wpM2l => //; have := spec_decr A ij; rewrite !mxE.
Qed.

Lemma spec_psd_ge0 n (A : 'M[R]_n) i : psdmx A -> 0 <= spec A 0 i.
Proof.
move=> [As Ap]; have [P Po AE] := spec_decomposition As.
exact: (spectral_psd Po AE).1 Ap i.
Qed.

Lemma sum_spec_trace n (A : 'M[R]_n) : A \is symmetricmx ->
  \sum_i spec A 0 i = \tr A.
Proof.
move=> As; have [P Po AE] := spec_decomposition As.
by rewrite (spectral_trace Po AE).
Qed.

(* von Neumann's inequality for the Frobenius pairing. *)
Lemma mxdot_spec_le n (A B : 'M[R]_n) :
  A \is symmetricmx -> B \is symmetricmx ->
  mxdot A B <= \sum_i spec A 0 i * spec B 0 i.
Proof.
move=> As Bs; rewrite mxdot_trace.
have -> : B^T = B by apply/symmetricmxP.
exact: von_neumann_trace.
Qed.

Lemma mxdot_psd_part_shift n (A : 'M[R]_n) (w : R) : A \is symmetricmx ->
  mxdot A (psd_part (A - w%:M)) =
  \sum_i spec A 0 i * Num.max (spec A 0 i - w) 0.
Proof.
move=> As; have [P Po AE] := spec_decomposition As.
have E : A - w%:M = P^T *m diag_mx (spec A - const_mx w) *m P.
  rewrite {1}AE linearB /= mulmxBr mulmxBl; congr (_ - _).
  rewrite diag_const_mx mul_mx_scalar -scalemxAl.
  have : P^T \is orthogonalmx by rewrite trmx_orthogonal.
  by move/orthogonalmxP; rewrite trmxK => ->; rewrite scalemx1.
rewrite (psd_partE Po E) {1}AE mxdot_orthogonalmxr //.
rewrite mxdot_orthogonalmxl ?trmx_orthogonal // mxdot_diag.
by apply: eq_bigr => i _; rewrite !mxE.
Qed.

End spec_conj.
