From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import reals ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.
From GaussianAnalysis.matrix Require Import psd_duality.

(**md**************************************************************************)
(* # Certificates excluding positive semidefinite quadrics                    *)
(*                                                                            *)
(* The sample vectors are columns, so their outer products are x x^T.       *)
(* No probabilistic assertion or existence of a certificate is assumed: the  *)
(* results below are deterministic implications from explicit weights.       *)
(*                                                                            *)
(* ```                                                                        *)
(* weighted_outer w x == sum_i w i *: (x i *m (x i)^T)                       *)
(* quadric_eval Q v c x == <x, Q x> + <v, x> + c                             *)
(* ```                                                                        *)
(*                                                                            *)
(* Weights annihilating constants and coordinates leave weighted_outer       *)
(* unchanged under every common translation. If this matrix is at least     *)
(* t I with t > 0, no quadric with nonzero PSD quadratic part can contain    *)
(* every sample point, regardless of its linear and constant terms.          *)
(* quadric_certificate_residual gives the quantitative squared-residual      *)
(* bound for t >= 0; its linear and constant terms are arbitrary.            *)
(* The translated-fit corollary retains the same certificate for all        *)
(* translations. The independent example uses the three points -1, 0, 1.    *)
(*                                                                            *)
(* Source: the deterministic cancellation and quadric argument in            *)
(* doc/shifted-gaussian.tex, the section on nonexistence above 1/4 uniformly  *)
(* over translations. The matrix statements are independent of that model.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section definitions.
Variable R : realType.

Definition weighted_outer (I : finType) n (w : I -> R)
    (x : I -> 'cV[R]_n) : 'M[R]_n :=
  \sum_i w i *: (x i *m (x i)^T).

Definition quadric_eval n (Q : 'M[R]_n) (v : 'cV[R]_n)
    (c : R) (x : 'cV[R]_n) : R :=
  mxdot x (Q *m x) + mxdot v x + c.

End definitions.

Section certificates.
Variables (R : realType) (I : finType) (n : nat).
Variables (w : I -> R) (x : I -> 'cV[R]_n).

Lemma weighted_outer_translate (m : 'cV[R]_n) :
  \sum_i w i = 0 -> \sum_i w i *: x i = 0 ->
  weighted_outer w (fun i => x i + m) = weighted_outer w x.
Proof.
move=> w0 wx0.
have wcoord j : \sum_i w i * x i j 0 = 0.
  have e : (\sum_i w i *: x i) j 0 = \sum_i w i * x i j 0.
    by rewrite summxE; apply: eq_bigr => i _; rewrite mxE.
  by rewrite -e wx0 mxE.
apply/matrixP => j k.
rewrite /weighted_outer !summxE.
have -> : (\sum_i (w i *: ((x i + m) *m (x i + m)^T)) j k) =
    (\sum_i w i * (x i j 0 * x i k 0)) +
    (\sum_i w i * x i j 0) * m k 0 +
    m j 0 * (\sum_i w i * x i k 0) +
    (\sum_i w i) * (m j 0 * m k 0).
  rewrite !mulr_suml !mulr_sumr -!big_split /=.
  apply: eq_bigr => i _; rewrite !mxE big_ord1 !mxE; ring.
rewrite w0 !wcoord !mul0r mulr0 !addr0.
by apply: eq_bigr => i _; rewrite !mxE big_ord1 mxE.
Qed.

Lemma weighted_quadric_eval (Q : 'M[R]_n) (v : 'cV[R]_n) (c : R) :
  \sum_i w i * quadric_eval Q v c (x i) =
    \tr (Q *m weighted_outer w x) +
    mxdot v (\sum_i w i *: x i) + c * (\sum_i w i).
Proof.
rewrite /weighted_outer mulmx_sumr raddf_sum /= mxdot_sumr.
rewrite mulr_sumr -!big_split /=.
apply: eq_bigr => i _.
rewrite -scalemxAr mxtraceZ mxtrace_mulC mxtrace_outer mxdotZr.
by rewrite /quadric_eval; ring.
Qed.

Lemma weighted_quadric_eval_cancel (Q : 'M[R]_n) (v : 'cV[R]_n) (c : R) :
  \sum_i w i = 0 -> \sum_i w i *: x i = 0 ->
  \sum_i w i * quadric_eval Q v c (x i) =
    \tr (Q *m weighted_outer w x).
Proof.
by move=> w0 wx0; rewrite weighted_quadric_eval w0 wx0 mxdot0r mulr0 !addr0.
Qed.

Lemma quadric_certificate_trace (t : R) (Q : 'M[R]_n) :
  psdmx Q -> psdmx (weighted_outer w x - t%:M) ->
  t * \tr Q <= \tr (Q *m weighted_outer w x).
Proof.
move=> Qp Hp; have := mxtrace_psd_ge0 Qp Hp.
by rewrite mulmxBr raddfB /= mul_mx_scalar mxtraceZ subr_ge0.
Qed.

Theorem quadric_certificate_residual (t : R) (Q : 'M[R]_n)
    (v : 'cV[R]_n) (c : R) :
  \sum_i w i = 0 -> \sum_i w i *: x i = 0 ->
  0 <= t -> psdmx Q -> psdmx (weighted_outer w x - t%:M) ->
  (t * \tr Q) ^+ 2 <= (\sum_i (w i) ^+ 2) *
    (\sum_i (quadric_eval Q v c (x i)) ^+ 2).
Proof.
move=> w0 wx0 t0 Qp Hp.
have enum_sum (f : I -> R) :
    \sum_(j < #|I|) f (enum_val j) = \sum_i f i.
  rewrite [RHS](reindex (enum_val : 'I_#|I| -> I)) //.
  by exists enum_rank => [j _|i _]; [exact: enum_valK | exact: enum_rankK].
have squares (f : I -> R) : \sum_i f i * f i = \sum_i (f i) ^+ 2.
  by apply: eq_bigr => i _; rewrite expr2.
have cs := sum_cauchy_schwarz
  (fun j : 'I_#|I| => w (enum_val j))
  (fun j : 'I_#|I| => quadric_eval Q v c (x (enum_val j))).
rewrite (enum_sum (fun i => w i * quadric_eval Q v c (x i)))
  (enum_sum (fun i => w i * w i))
  (enum_sum (fun i => quadric_eval Q v c (x i) *
    quadric_eval Q v c (x i))) !squares
  weighted_quadric_eval_cancel // in cs.
have trQ0 : 0 <= \tr Q :=
  le_trans (frobenius_ge0 Q) (psdmx_frobenius_le_trace Qp).
have lhs0 := mulr_ge0 t0 trQ0.
have h := quadric_certificate_trace Qp Hp.
apply: le_trans _ cs.
by rewrite lerXn2r ?nnegrE //; exact: le_trans lhs0 h.
Qed.

Theorem quadric_certificate_excludes (t : R) :
  \sum_i w i = 0 -> \sum_i w i *: x i = 0 ->
  0 < t -> psdmx (weighted_outer w x - t%:M) ->
  forall (Q : 'M[R]_n) (v : 'cV[R]_n) (c : R),
    psdmx Q -> Q != 0 -> ~ (forall i, quadric_eval Q v c (x i) = 0).
Proof.
move=> w0 wx0 t0 Hp Q v c Qp Q0 fit.
have trQ : 0 < \tr Q.
  apply: lt_le_trans (psdmx_frobenius_le_trace Qp).
  by rewrite frobenius_gt0.
have h := quadric_certificate_trace Qp Hp.
have e : \tr (Q *m weighted_outer w x) = 0.
  rewrite -(weighted_quadric_eval_cancel Q v c w0 wx0).
  by apply: big1 => i _; rewrite fit mulr0.
rewrite e in h.
have : 0 < t * \tr Q := mulr_gt0 t0 trQ.
by move=> /lt_le_trans /(_ h); rewrite ltxx.
Qed.

End certificates.

Section translated_fits.
Variables (R : realType) (I : finType) (n : nat).
Variables (w : I -> R) (x : I -> 'cV[R]_n).

(* A centered fit at any translated sample is a special case. *)
Corollary quadric_certificate_no_translated_fit (t : R) :
  \sum_i w i = 0 -> \sum_i w i *: x i = 0 ->
  0 < t -> psdmx (weighted_outer w x - t%:M) ->
  forall (m : 'cV[R]_n) (Q : 'M[R]_n) (c : R),
    psdmx Q -> Q != 0 ->
    ~ (forall i, mxdot (x i + m) (Q *m (x i + m)) = c).
Proof.
move=> w0 wx0 t0 Hp m Q c Qp Q0 fit.
have wxm0 : \sum_i w i *: (x i + m) = 0.
  under eq_bigr do rewrite scalerDr.
  by rewrite big_split /= -scaler_suml w0 wx0 scale0r addr0.
have Hmp : psdmx (weighted_outer w (fun i => x i + m) - t%:M).
  by rewrite weighted_outer_translate.
have := @quadric_certificate_excludes R I n w (fun i => x i + m)
  t w0 wxm0 t0 Hmp Q 0 (- c) Qp Q0.
apply; move=> i.
by rewrite /quadric_eval fit mxdot0l addr0 subrr.
Qed.

End translated_fits.

Section example.
Variable R : realType.

(* In dimension one, the points -1, 0, 1 have certificate weights 1, -2, 1.
   Their weighted outer product is exactly 2 I. *)
Example three_points_no_psd_quadric (Q : 'M[R]_1) (v : 'cV[R]_1) (c : R) :
  psdmx Q -> Q != 0 ->
  ~ (forall i : 'I_3, quadric_eval Q v c (\col_j (i%:R - 1)) = 0).
Proof.
move=> Qp Q0.
pose w (i : 'I_3) : R := if val i == 1%N then -2 else 1.
pose x (i : 'I_3) : 'cV[R]_1 := \col_j (i%:R - 1).
have w0 : \sum_i w i = 0.
  by rewrite /w !big_ord_recr big_ord0 /=; ring.
have wx0 : \sum_i w i *: x i = 0.
  apply/matrixP => j k.
  by rewrite summxE /w /x !big_ord_recr big_ord0 /= !mxE; ring.
have outer : weighted_outer w x = 2%:M.
  apply/matrixP => j k; rewrite !ord1 /weighted_outer summxE.
  by rewrite /w /x !big_ord_recr big_ord0 /= !mxE !big_ord1 !mxE
    eqxx /=; ring.
have Hp : psdmx (weighted_outer w x - 2%:M).
  by rewrite outer subrr; exact: psdmx0.
have t0 : (0 : R) < 2 by rewrite ltr0n.
exact: (quadric_certificate_excludes w0 wx0 t0 Hp Qp Q0).
Qed.

End example.
