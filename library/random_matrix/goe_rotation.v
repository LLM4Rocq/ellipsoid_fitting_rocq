From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.comparison Require Import gauss_law.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # Uniform directions and the rotation invariance of the GOE                *)
(*                                                                            *)
(* Let g have law gauss n and v = g / |g|, a uniform point of the unit        *)
(* sphere. Item G6 of phase 5 replaces the Haar measure on the orthogonal     *)
(* group, which MathComp-Analysis does not have, in Lemma 5.13 of Koehler and *)
(* Sohn (arXiv 2608.27372, lines 5820-5860) by the moments of v and the       *)
(* invariance of the law of the GOE under conjugation by orthogonal matrices. *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - goe_conj_integral: the law of W = goe_mx a, a of law gauss (d * d), is   *)
(*   invariant under W |-> Q^T W Q for every orthogonal Q. The map a |->      *)
(*   mxvec (Q^T (vec_mx a) Q) is linear with an orthogonal matrix conj_mx Q   *)
(*   (conj_mx_orthogonal: it preserves the Frobenius product, mxdot_conj),    *)
(*   Q^T goe_mx a Q = goe_mx (a conj_mx Q) (goe_mx_conj), and gauss (d * d)   *)
(*   is invariant under orthogonal maps (integral_gauss_mulmx).               *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - E v_i^2 = 1 / n, E v_i^4 = 3 / (n (n + 2)) and E v_i^2 v_j^2 = 1 / (n (n *)
(*   + 2)) for i != j, from the invariance of gauss n under orthogonal maps   *)
(*   (gauss_orthogonal_law of comparison/gauss_law.v): permutations and sign  *)
(*   changes, and the rotation by pi / 4 in the plane (i, j), which gives E   *)
(*   v_i^4 = 3 E v_i^2 v_j^2; with \sum_i v_i^2 = 1 this fixes both moments.  *)
(* - For A symmetric: E (v A v^T) = \tr A / n and E (v A v^T)^2 = ((\tr A)^2  *)
(*   + 2 \tr (A^2)) / (n (n + 2)).                                            *)
(* - For F from the symmetric matrices to the matrices with F (Q W Q^T) = Q F *)
(*   (W) Q^T for every orthogonal Q (for instance a continuous function of W  *)
(*   in the sense of the spectral calculus): E[(1 / d) \sum_j (F (W)_jj - \tr *)
(*   F (W) / d)^2] = (2 / (d + 2)) E[\tr (F (W)^2) / d - (\tr F (W) / d)^2],  *)
(*   so the diagonal of F (W) is nearly constant (Lemma 5.13 with a uniform   *)
(*   direction instead of a Haar matrix).                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section goe_invariance.
Context {R : realType} (d : nat).

(* The matrix of a |-> mxvec (Q^T (vec_mx a) Q). *)
Definition conj_mx (Q : 'M[R]_d) : 'M[R]_(d * d) :=
  lin_mx (mulmxr Q \o mulmx Q^T).

Lemma conj_mxE (Q : 'M[R]_d) (a : 'rV[R]_(d * d)) :
  a *m conj_mx Q = mxvec (Q^T *m vec_mx a *m Q).
Proof. by rewrite /conj_mx mul_rV_lin. Qed.

(* mxvec is an isometry for the Frobenius product. *)
Let mxdot_vec (A B : 'M[R]_d) : mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 (reindex _ (curry_mxvec_bij d d)) /=.
rewrite pair_big /=; apply: eq_bigr => -[i j] _ /=.
by rewrite !mxvecE.
Qed.

(* Conjugation by an orthogonal matrix preserves the Frobenius product. *)
Lemma mxdot_conj (Q A B : 'M[R]_d) : Q \is orthogonalmx ->
  mxdot (Q^T *m A *m Q) (Q^T *m B *m Q) = mxdot A B.
Proof.
move=> /orthogonalmxP QQ; rewrite !mxdot_trace !trmx_mul !trmxK.
rewrite -!mulmxA [Q *m (Q^T *m _)]mulmxA QQ mul1mx mxtrace_mulC -!mulmxA.
by rewrite QQ mulmx1.
Qed.

Lemma conj_mx_orthogonal (Q : 'M[R]_d) : Q \is orthogonalmx ->
  conj_mx Q \is orthogonalmx.
Proof.
move=> Qo; apply/orthogonalmxP/matrixP => p q; rewrite mxE.
have -> : \sum_j conj_mx Q p j * (conj_mx Q)^T j q =
    mxdot (row p (conj_mx Q)) (row q (conj_mx Q)).
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE.
rewrite !rowE !conj_mxE mxdot_vec mxdot_conj // -mxdot_vec !vec_mxK mxdot_delta.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Lemma goe_mx_conj (Q : 'M[R]_d) (a : 'rV[R]_(d * d)) :
  Q^T *m goe_mx a *m Q = goe_mx (a *m conj_mx Q).
Proof.
rewrite /goe_mx conj_mxE mxvecK -scalemxAr -scalemxAl; congr (_ *: _).
by rewrite mulmxDr mulmxDl !trmx_mul trmxK mulmxA.
Qed.

Lemma measurable_goe_mx : measurable_fun [set: 'rV[R]_(d * d)] (@goe_mx R d).
Proof.
apply/measurable_fun_mxP => i j.
exact: continuous_measurable_mx ((@mx_polyfun_goe R d i j).1).
Qed.

(* The law of the GOE is invariant under conjugation by an orthogonal
   matrix: Q^T W Q has the law of W. *)
Theorem goe_conj_integral (Q : 'M[R]_d) (F : 'M[R]_d -> \bar R) :
  Q \is orthogonalmx -> measurable_fun [set: 'M[R]_d] F ->
  (\int[gauss (d * d)]_a F (Q^T *m goe_mx a *m Q) =
   \int[gauss (d * d)]_a F (goe_mx a))%E.
Proof.
move=> Qo mF; under eq_integral do rewrite goe_mx_conj.
have MM : (conj_mx Q)^T *m conj_mx Q = (1%:M : 'M[R]_(d * d))^T *m 1%:M.
  by rewrite trmx1 mulmx1; exact: orthogonalmxT (conj_mx_orthogonal Qo).
have mFg : measurable_fun [set: 'rV[R]_(d * d)] (fun y => F (goe_mx y)).
  exact: measurableT_comp mF measurable_goe_mx.
rewrite (integral_gauss_mulmx MM mFg).
by under eq_integral do rewrite mulmx1.
Qed.

End goe_invariance.
