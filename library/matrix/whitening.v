From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.

(**md**************************************************************************)
(* # Whitening                                                                *)
(*                                                                            *)
(* Let S be a real symmetric matrix whose quadratic form is bounded below:    *)
(* b |x|^2 <= x S x^T for every row vector x, with b > 0. If                  *)
(* S = P^T diag (d) P is its spectral decomposition, the matrix               *)
(* W = diag (d)^(-1/2) P whitens S: W S W^T = 1 (whitening_mxP), and          *)
(* |x W| <= |x| / sqrt b for every row vector x (frobenius_whitening_mx).     *)
(* For b = 1, W does not increase norms (whitening_exists).                   *)
(*                                                                            *)
(* ```                                                                        *)
(*   whitening_mx S == diag_mx (\row_i (Num.sqrt (d 0 i))^-1) *m P for the    *)
(*                     chosen spectral decomposition S = P^T diag_mx d P      *)
(*                     (sym_spectralmx, sym_spectral_diag)                    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section whitening_matrix.
Variable R : realType.
Implicit Types n : nat.

Definition whitening_mx n (S : 'M[R]_n) : 'M[R]_n :=
  diag_mx (\row_i (Num.sqrt (sym_spectral_diag S 0 i))^-1) *m sym_spectralmx S.

(* A lower bound on the quadratic form bounds the eigenvalues below. *)
Lemma sym_spectral_diag_ge n (S : 'M[R]_n) (b : R) : S \is symmetricmx ->
  (forall x : 'rV[R]_n, b * mxdot x x <= mxdot (x *m S) x) ->
  forall i, b <= sym_spectral_diag S 0 i.
Proof.
move=> Ssym hb.
have Po := sym_spectralmx_orthogonal S.
apply: (spectral_form_ge b Po (sym_spectralE Ssym)).1.
move=> x; have ST : S^T = S by apply/symmetricmxP.
have e : mxdot (x^T *m S) x^T = mxdot x (S *m x).
  by rewrite -[LHS]mxdot_trmx trmx_mul !trmxK ST mxdotC.
by have := hb x^T; rewrite mxdot_trmx e.
Qed.

Lemma whitening_mxP n (S : 'M[R]_n) (b : R) : 0 < b -> S \is symmetricmx ->
  (forall x : 'rV[R]_n, b * mxdot x x <= mxdot (x *m S) x) ->
  whitening_mx S *m S *m (whitening_mx S)^T = 1%:M.
Proof.
move=> b0 Ssym hb; have hd := sym_spectral_diag_ge Ssym hb.
have SE := sym_spectralE Ssym.
have Po := sym_spectralmx_orthogonal S.
set P := sym_spectralmx S in SE Po *; set d := sym_spectral_diag S in SE hd *.
have PPt : P *m P^T = 1%:M by apply/orthogonalmxP.
rewrite /whitening_mx -/P -/d.
set D := diag_mx _.
rewrite SE trmx_mul.
have -> : D *m P *m (P^T *m diag_mx d *m P) *m (P^T *m D^T) =
    D *m (P *m P^T) *m diag_mx d *m (P *m P^T) *m D^T by rewrite !mulmxA.
rewrite PPt !mulmx1 /D tr_diag_mx.
apply/matrixP => i j; rewrite mul_mx_diag mul_diag_mx !mxE.
have [<-|ij] := eqVneq i j; last by rewrite !mulr0n mulr0 mul0r.
have di : 0 < d 0 i := lt_le_trans b0 (hd i).
rewrite !mulr1n mulrAC -expr2 exprVn (sqr_sqrtr (ltW di)).
by rewrite mulVf// gt_eqF.
Qed.

Lemma frobenius_whitening_mx n (S : 'M[R]_n) (b : R) :
    0 < b -> S \is symmetricmx ->
  (forall x : 'rV[R]_n, b * mxdot x x <= mxdot (x *m S) x) ->
  forall x : 'rV[R]_n,
    frobenius (x *m whitening_mx S) <= (Num.sqrt b)^-1 * frobenius x.
Proof.
move=> b0 Ssym hb x; have hd := sym_spectral_diag_ge Ssym hb.
have Po := sym_spectralmx_orthogonal S.
set P := sym_spectralmx S in Po *; set d := sym_spectral_diag S in hd *.
rewrite /whitening_mx -/P -/d mulmxA frobenius_orthogonalmxr//.
have -> : (Num.sqrt b)^-1 * frobenius x = Num.sqrt (b^-1 * mxdot x x).
  by rewrite sqrtrM ?invr_ge0 ?(ltW b0)// sqrtrV ?(ltW b0).
rewrite /frobenius ler_sqrt.
  by rewrite mulr_ge0 ?invr_ge0 ?(ltW b0) ?mxdot_ge0.
rewrite /mxdot !big_ord1 mulr_sumr; apply: ler_sum => j _.
rewrite mul_mx_diag !mxE.
have dj : 0 < d 0 j := lt_le_trans b0 (hd j).
have -> : x 0 j * (Num.sqrt (d 0 j))^-1 * (x 0 j * (Num.sqrt (d 0 j))^-1) =
    (Num.sqrt (d 0 j))^-1 ^+ 2 * (x 0 j * x 0 j) by ring.
rewrite exprVn (sqr_sqrtr (ltW dj)).
apply: ler_wpM2r; first by rewrite -expr2 sqr_ge0.
by rewrite lef_pV2 ?posrE// hd.
Qed.

(* The whitening of a matrix that dominates the identity. *)
Theorem whitening_exists n (S : 'M[R]_n) : S \is symmetricmx ->
  (forall x : 'rV[R]_n, mxdot x x <= mxdot (x *m S) x) ->
  exists W : 'M[R]_n,
    W *m S *m W^T = 1%:M /\
    forall x : 'rV[R]_n, frobenius (x *m W) <= frobenius x.
Proof.
move=> Ssym h1.
have hb (x : 'rV[R]_n) : 1 * mxdot x x <= mxdot (x *m S) x.
  by rewrite mul1r.
exists (whitening_mx S); split; first exact: (whitening_mxP ltr01 Ssym hb).
move=> x; have := frobenius_whitening_mx ltr01 Ssym hb x.
by rewrite sqrtr1 invr1 mul1r.
Qed.

End whitening_matrix.
