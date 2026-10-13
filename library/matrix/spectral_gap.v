From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear reals.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.

(**md**************************************************************************)
(* # Two bounds for real symmetric matrices                                   *)
(*                                                                            *)
(* - psd_square_gap, a gap from the square: if B is symmetric and positive    *)
(*   semidefinite and k x^T B x <= |B x|^2 for every column x, then k |x|^2   *)
(*   <= x^T B x for every x orthogonal to the kernel of B. In an eigenbasis   *)
(*   of B (symmetric_spectral) the hypothesis says that every eigenvalue is 0 *)
(*   or at least k.                                                           *)
(* - opnorm_row_sum, the Schur test for symmetric matrices: if B is           *)
(*   symmetric, rho >= 0 and sum_j |B_ij| <= rho for every row i, then opnorm *)
(*   B <= rho.                                                                *)
(* - mulmx_col_mxdot and mxdot_mulmx_sum write (P x)_i and x^T B x as sums.   *)
(*                                                                            *)
(* This file is a Rocq formalization, in general form, of two steps of the    *)
(* credited argument of the proposition 'Gap and covariance under scaled      *)
(* interactions and fields' of 'Cutoff throughout the high-temperature        *)
(* Sherrington-Kirkpatrick phase' (family 227 of the OpenAI math collection,  *)
(* revision 1581d4cbd, appendices/entropy.tex): the row-sum bound for the     *)
(* operator norm of a symmetric matrix, and the gap read from the inequality  *)
(* |A f|^2 >= kappa <f, A f>. Target T4 of phase 12 (AGENTS.md, section Phase *)
(* 12) uses both. The file follows no Lean module.                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section spectral_gap.
Variable R : realType.

Lemma mulmx_col_mxdot n (P : 'M[R]_n) (x : 'cV[R]_n) i :
  (P *m x) i 0 = mxdot (row i P)^T x.
Proof.
rewrite mxE /mxdot; apply: eq_bigr => j _.
by rewrite big_ord1 !mxE.
Qed.

Lemma psd_square_gap n (B : 'M[R]_n) (k : R) (x : 'cV[R]_n) :
  B \is symmetricmx ->
  (forall y : 'cV[R]_n, 0 <= mxdot y (B *m y)) ->
  (forall y : 'cV[R]_n, k * mxdot y (B *m y) <= mxdot (B *m y) (B *m y)) ->
  (forall y : 'cV[R]_n, B *m y = 0 -> mxdot y x = 0) ->
  k * mxdot x x <= mxdot x (B *m x).
Proof.
move=> Bs Bpsd Bsq Bker.
have [P Po [d BE]] := symmetric_spectral Bs.
have d0 i : 0 <= d 0 i := proj1 (spectral_psd Po BE) Bpsd i.
have ev i : B *m (row i P)^T = d 0 i *: (row i P)^T := spectral_eigenvector i Po BE.
have u1 i : mxdot (row i P)^T (row i P)^T = 1 := orthogonalmx_row_unit i Po.
have hi i : k * (P *m x) i 0 ^+ 2 <= d 0 i * (P *m x) i 0 ^+ 2.
  have [di0'|dn0] := eqVneq (d 0 i) 0.
    have di0 : d 0 i = 0 :> R := di0'.
    have e : d 0 i *: (row i P)^T = 0 by rewrite di0 scale0r.
    have hx := Bker (row i P)^T (etrans (ev i) e).
    by rewrite di0 mulmx_col_mxdot hx expr0n /= !mulr0.
  apply: ler_wpM2r; first exact: sqr_ge0.
  have := Bsq (row i P)^T; rewrite ev mxdotZr mxdotZl mxdotZr u1 !mulr1.
  have dp : 0 < d 0 i by rewrite lt_def dn0 d0.
  by rewrite ler_pM2r.
rewrite (spectral_form x BE).
rewrite -(mxdot_orthogonalmxl x x Po) {1}/mxdot mulr_sumr; apply: ler_sum => i _.
by rewrite big_ord1 -expr2.
Qed.

Lemma mxdot_mulmx_sum n (B : 'M[R]_n) (x : 'cV[R]_n) :
  mxdot x (B *m x) = \sum_i \sum_j x i 0 * B i j * x j 0.
Proof.
rewrite /mxdot; apply: eq_bigr => i _; rewrite big_ord1 mxE mulr_sumr.
by apply: eq_bigr => j _; rewrite mulrA.
Qed.

Lemma opnorm_row_sum n (B : 'M[R]_n) (rho : R) : B \is symmetricmx -> 0 <= rho ->
  (forall i, \sum_j `|B i j| <= rho) -> opnorm B <= rho.
Proof.
move=> Bs rho0 hr; apply/(opnorm_symP Bs rho0) => x.
have BT : forall i j, B j i = B i j.
  by move/symmetricmxP: Bs => BT i j; rewrite -[in LHS]BT mxE.
rewrite mxdot_mulmx_sum.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: (le_trans (y := \sum_i \sum_j `|B i j| * ((x i 0 ^+ 2 + x j 0 ^+ 2) / 2))).
  apply: ler_sum => i _; apply: le_trans (ler_norm_sum _ _ _) _.
  apply: ler_sum => j _; rewrite !normrM [`|x i 0| * _]mulrC -mulrA.
  apply: ler_wpM2l; first exact: normr_ge0.
  have := sqr_ge0 (`|x i 0| - `|x j 0|).
  rewrite -[x i 0 ^+ 2]real_normK ?num_real // -[x j 0 ^+ 2]real_normK ?num_real //.
  by move=> h; nra.
have -> : \sum_i \sum_j `|B i j| * ((x i 0 ^+ 2 + x j 0 ^+ 2) / 2) =
    (\sum_i \sum_j x i 0 ^+ 2 * `|B i j| + \sum_i \sum_j x j 0 ^+ 2 * `|B i j|) / 2.
  rewrite -big_split mulr_suml /=; apply: eq_bigr => i _.
  by rewrite -big_split mulr_suml /=; apply: eq_bigr => j _; ring.
have hc j : \sum_i `|B i j| <= rho.
  by rewrite (eq_bigr (fun i => `|B j i|)) ?hr // => i _; rewrite BT.
have hx : mxdot x x = \sum_i x i 0 ^+ 2.
  by rewrite /mxdot; apply: eq_bigr => i _; rewrite big_ord1 expr2.
rewrite hx.
have h1 : \sum_i \sum_j x i 0 ^+ 2 * `|B i j| <= rho * \sum_i x i 0 ^+ 2.
  rewrite mulr_sumr; apply: ler_sum => i _; rewrite -mulr_sumr mulrC.
  by apply: ler_wpM2r; [exact: sqr_ge0 | exact: hr].
have h2 : \sum_i \sum_j x j 0 ^+ 2 * `|B i j| <= rho * \sum_i x i 0 ^+ 2.
  rewrite exchange_big mulr_sumr; apply: ler_sum => j _; rewrite -mulr_sumr mulrC.
  by apply: ler_wpM2r; [exact: sqr_ge0 | exact: hc].
lra.
Qed.

End spectral_gap.
