From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear interval.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun.
From mathcomp Require Import probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.comparison Require Import gauss_law.
From GaussianAnalysis.random_matrix Require Import goe.

(**md**************************************************************************)
(* # The rotation invariance of the GOE                                       *)
(*                                                                            *)
(* Let W = goe_mx a, with a of law gauss (n * n). Lemma 5.13 of Koehler and   *)
(* Sohn (arXiv 2608.27372, lines 5820-5860) averages the diagonal of U D U^T  *)
(* over a Haar matrix U, and MathComp-Analysis has no Haar measure on the     *)
(* orthogonal group. Item G6 of phase 5 proves what the paper uses the lemma  *)
(* for, that the diagonal of F(W) is nearly constant for an equivariant F,    *)
(* from the invariance of the law of W under orthogonal conjugation, with     *)
(* Householder reflections in place of the Haar matrix. Every result holds    *)
(* for every n.                                                               *)
(*                                                                            *)
(* - goe_conj_integral: the law of W is invariant under W |-> Q^T W Q for     *)
(*   every orthogonal Q. The map a |-> mxvec (Q^T (vec_mx a) Q) is linear     *)
(*   with an orthogonal matrix conj_mx Q (conj_mx_orthogonal: it preserves    *)
(*   the Frobenius product, mxdot_conj), Q^T goe_mx a Q = goe_mx (a conj_mx   *)
(*   Q) (goe_mx_conj), and gauss (n * n) is invariant under orthogonal maps   *)
(*   (integral_gauss_mulmx).                                                  *)
(* - goe_equiv_form: for F equivariant (conj_equivariant) and every unit row  *)
(*   vector u, u F(W) u^T has the law of F(W)_00, because the Householder     *)
(*   reflection that maps the first basis vector to u^T (householder_swap)    *)
(*   conjugates W into a matrix of the same law. Hence each diagonal entry of *)
(*   F(W) has the law of F(W)_00 (goe_equiv_diag), and so has (F(W)_ii +      *)
(*   F(W)_jj) / 2 + s F(W)_ij for i != j and s = 1 or -1 when F(W) is         *)
(*   symmetric (goe_equiv_pair, with u = (e_i + s e_j) / sqrt 2).             *)
(* - goe_diag_var_identity: if moreover F(W) is symmetric and E F(W)_ij^2 is  *)
(*   finite, then E[F(W)_ii F(W)_jj] + 2 E[F(W)_ij^2] = E[F(W)_00^2] for i != *)
(*   j (goe_equiv_pair2), hence E[diag_var F(W)] = 2 / (n + 2) E[|F(W)|_F^2 / *)
(*   n - (tr F(W) / n)^2]. This is the identity of the proof of Lemma 5.13    *)
(*   (lines 5853-5860), where the rho_i are the eigenvalues of F(W).          *)
(* - goe_diag_var_tail: for C >= 0 and eps > 0, P(diag_var F(W) >= eps) <= 2  *)
(*   C / ((n + 2) eps) + P(|F(W)|_F^2 > C n), by the identity for the map W   *)
(*   |-> F(W) when |F(W)|_F^2 <= C n and 0 otherwise, which is still          *)
(*   equivariant, and Markov's inequality (gauss_markov). So diag_var F(W)    *)
(*   tends to 0 in probability when |F(W)|_F^2 / n is bounded in probability, *)
(*   as for F(W) the positive part (psd_part of matrix/psd_part.v) of W - w I *)
(*   with w bounded, which is how Proposition 5.15 uses Lemma 5.13.           *)
(*                                                                            *)
(* ```                                                                        *)
(*  conj_equivariant F == F (Q W Q^T) = Q F(W) Q^T for every orthogonal Q     *)
(*                        and every symmetric W                               *)
(*          diag_var A == (1 / n) \sum_j (A_jj - tr A / n)^2, the empirical   *)
(*                        variance of the diagonal of A : 'M_n                *)
(* ```                                                                        *)
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
  Q \is orthogonalmx ->
  measurable_fun [set: 'rV[R]_(d * d)] (fun a => F (goe_mx a)) ->
  (\int[gauss (d * d)]_a F (Q^T *m goe_mx a *m Q) =
   \int[gauss (d * d)]_a F (goe_mx a))%E.
Proof.
move=> Qo mFg; under eq_integral do rewrite goe_mx_conj.
have MM : (conj_mx Q)^T *m conj_mx Q = (1%:M : 'M[R]_(d * d))^T *m 1%:M.
  by rewrite trmx1 mulmx1; exact: orthogonalmxT (conj_mx_orthogonal Qo).
rewrite (integral_gauss_mulmx MM mFg).
by under eq_integral do rewrite mulmx1.
Qed.

End goe_invariance.


Section diag_var.
Context {R : realType}.
Implicit Types n : nat.

(* F commutes with the conjugations by orthogonal matrices on the symmetric
   matrices, as the spectral functions P^T diag(d) P |-> P^T diag(f (d_i)) P
   do. *)
Definition conj_equivariant n (F : 'M[R]_n -> 'M[R]_n) : Prop :=
  forall Q W : 'M[R]_n, Q \is orthogonalmx -> W \is symmetricmx ->
  F (Q *m W *m Q^T) = Q *m F W *m Q^T.

(* The empirical variance of the diagonal entries of A. *)
Definition diag_var n (A : 'M[R]_n) : R :=
  n%:R^-1 * \sum_j (A j j - \tr A / n%:R) ^+ 2.

Lemma diag_var_ge0 n (A : 'M[R]_n) : 0 <= diag_var A.
Proof.
rewrite /diag_var mulr_ge0 ?invr_ge0 ?ler0n // sumr_ge0 // => j _.
exact: sqr_ge0.
Qed.

Lemma diag_varE n (A : 'M[R]_n) :
  diag_var A = n%:R^-1 * \sum_j A j j ^+ 2 - (\tr A / n%:R) ^+ 2.
Proof.
case: n A => [|n] A.
  by rewrite /diag_var /mxtrace !big_ord0 invr0 !mul0r expr2 mul0r subr0.
rewrite /diag_var; set m := \tr A / _.
have -> : \sum_j (A j j - m) ^+ 2 =
    \sum_j A j j ^+ 2 - \tr A * m *+ 2 + m ^+ 2 *+ n.+1.
  under eq_bigr do rewrite sqrrB.
  by rewrite !big_split /= sumrN sumr_const card_ord sumrMnl -mulr_suml.
have n0 : n.+1%:R != 0 :> R by rewrite pnatr_eq0.
by rewrite /m; field.
Qed.

Lemma diag_sqr_le n (A : 'M[R]_n) : \sum_j A j j ^+ 2 <= mxdot A A.
Proof.
rewrite /mxdot; apply: ler_sum => i _; rewrite (bigD1 i) //= -expr2 lerDl.
by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
Qed.

(* (tr A / n)^2 <= |A|_F^2 / n. *)
Lemma trace_sqr_le n (A : 'M[R]_n) : (\tr A / n%:R) ^+ 2 <= mxdot A A / n%:R.
Proof.
have := diag_var_ge0 A; rewrite diag_varE subr_ge0 => h; apply: le_trans h _.
by rewrite mulrC ler_wpM2r ?invr_ge0 ?ler0n // diag_sqr_le.
Qed.

End diag_var.

Section gauss_markov.
Context {R : realType} (m : nat).

(* Markov's inequality: P(f >= c) <= E f / c for f >= 0 and c > 0. *)
Lemma gauss_markov (f : 'rV[R]_m -> R) (c : R) : 0 < c ->
  measurable_fun [set: 'rV[R]_m] f -> (forall x, 0 <= f x) ->
  (gauss m).-integrable [set: 'rV[R]_m] (EFin \o f) ->
  (gauss m [set x | (c <= f x)%R] <= (c^-1 * \int[gauss m]_x f x)%:E)%E.
Proof.
move=> c0 mf f0 fi.
have mA : measurable [set x | c <= f x].
  have := mf measurableT _ (measurable_itv `[c, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => x /=; rewrite in_itv /= andbT.
rewrite -(setIT [set x | c <= f x]) -integral_indic //.
apply: le_trans (_ : (\int[gauss m]_x (c^-1 * f x)%:E <= _)%E).
  apply: ge0_le_integral => //.
  - by apply/measurable_EFinP; exact: measurable_indic.
  - by apply/measurable_EFinP; apply: measurable_funM.
  move=> x _; rewrite lee_fin indicE.
  have [/set_mem /= cx|_] := boolP (x \in [set x0 | c <= f x0]).
    rewrite -[true%:R]/(1 : R) -(mulVf (lt0r_neq0 c0)).
    by apply: ler_wpM2l => //; rewrite invr_ge0 ltW.
  by rewrite -[false%:R]/(0 : R) mulr_ge0 // invr_ge0 ltW.
have iG : (gauss m).-integrable [set: 'rV[R]_m] (EFin \o (fun x => c^-1 * f x)).
  rewrite (_ : _ \o _ = (fun x => (c^-1)%:E * (f x)%:E)%E);
    first by apply/funext => x.
  exact: integrableZl.
have fin := integrable_fin_num measurableT iG.
by rewrite -RintegralZl // /Rintegral fineK.
Qed.

End gauss_markov.

Section goe_equivariant.
Context {R : realType} (d : nat).
Local Notation N := d.+1.
Variable F : 'M[R]_N -> 'M[R]_N.
Hypothesis Feq : conj_equivariant F.
Hypothesis Fm : measurable_fun [set: 'rV[R]_(N * N)] (fun a => F (goe_mx a)).

Lemma mulmx_delta_entry0 (X : 'M[R]_N) (i j : 'I_N) :
  (delta_mx 0 i *m X *m delta_mx j 0 : 'M[R]_1) 0 0 = X i j.
Proof. by rewrite -rowE -colE !mxE. Qed.

(* For every unit vector u, u F(W) u^T has the law of F(W)_00: a Householder
   reflection maps the first basis vector to u. *)
Lemma goe_equiv_form (u : 'rV[R]_N) (phi : R -> \bar R) :
  mxdot u u = 1 -> measurable_fun [set: R] phi ->
  (\int[gauss (N * N)%N]_a phi ((u *m F (goe_mx a) *m u^T) ord0 ord0) =
   \int[gauss (N * N)%N]_a phi (F (goe_mx a) ord0 ord0))%E.
Proof.
move=> u1 mphi.
pose e : 'cV[R]_N := delta_mx 0 0.
pose H := householder (e - u^T).
have Ho : H \is orthogonalmx := householder_orthogonal _.
have HT : H^T = H := householder_tr _.
have He : H *m e = u^T.
  by apply: householder_swap; rewrite mxdot_delta mxE /= mxdot_trmx u1.
have mG : measurable_fun [set: 'rV[R]_(N * N)]
    (fun a => phi (F (goe_mx a) ord0 ord0)).
  apply: measurableT_comp mphi _.
  exact: (measurable_fun_mxP _).1 Fm ord0 ord0.
rewrite -(@goe_conj_integral _ _ H (fun W => phi (F W ord0 ord0)) Ho mG).
apply: eq_integral => a _ /=.
rewrite HT -[X in F (_ *m _ *m X)]HT Feq ?goe_mx_symmetric //.
congr phi.
have uE : u = (delta_mx 0 0 : 'M[R]_(1, N)) *m H.
  by rewrite -[u]trmxK -He trmx_mul /e trmx_delta HT.
rewrite -[in RHS](mulmx_delta_entry0 (H *m F (goe_mx a) *m H^T)) -/e HT.
by rewrite !mulmxA -(mulmxA _ H e) He -uE.
Qed.

Lemma goe_equiv_formR (u : 'rV[R]_N) (phi : R -> R) :
  mxdot u u = 1 -> measurable_fun [set: R] phi ->
  \int[gauss (N * N)%N]_a phi ((u *m F (goe_mx a) *m u^T) ord0 ord0) =
  \int[gauss (N * N)%N]_a phi (F (goe_mx a) ord0 ord0).
Proof.
move=> u1 mphi; rewrite /Rintegral; congr fine.
by apply: (goe_equiv_form (phi := EFin \o phi) u1); apply/measurable_EFinP.
Qed.

(* The diagonal entries of F(W) have the law of F(W)_00. *)
Lemma goe_equiv_diag (i : 'I_N) (phi : R -> R) : measurable_fun [set: R] phi ->
  \int[gauss (N * N)%N]_a phi (F (goe_mx a) i i) =
  \int[gauss (N * N)%N]_a phi (F (goe_mx a) ord0 ord0).
Proof.
move=> mphi; have u1 : mxdot (delta_mx 0 i : 'rV[R]_N) (delta_mx 0 i) = 1.
  by rewrite mxdot_delta mxE !eqxx.
rewrite -(goe_equiv_formR u1 mphi); apply: eq_Rintegral => a _.
by rewrite trmx_delta mulmx_delta_entry0.
Qed.

Hypothesis Fsym : forall W : 'M[R]_N, W \is symmetricmx -> F W \is symmetricmx.

(* For i != j and s = 1 or s = -1, (F(W)_ii + F(W)_jj) / 2 + s F(W)_ij has
   the law of F(W)_00: take u = (e_i + s e_j) / sqrt 2. *)
Lemma goe_equiv_pair (i j : 'I_N) (s : R) (phi : R -> R) :
  i != j -> s ^+ 2 = 1 -> measurable_fun [set: R] phi ->
  \int[gauss (N * N)%N]_a
    phi ((F (goe_mx a) i i + F (goe_mx a) j j) / 2 + s * F (goe_mx a) i j) =
  \int[gauss (N * N)%N]_a phi (F (goe_mx a) ord0 ord0).
Proof.
move=> ij s2 mphi.
pose c := (Num.sqrt 2 : R)^-1.
have c2 : c * c = 2^-1 by rewrite -expr2 exprVn sqr_sqrtr // ler0n.
pose u : 'rV[R]_N := c *: (delta_mx 0 i + s *: delta_mx 0 j).
have u1 : mxdot u u = 1.
  rewrite /u mxdotZl mxdotZr mxdotDl !mxdotDr !mxdotZl !mxdotZr !mxdot_delta.
  rewrite !mxE !eqxx (negbTE ij) eq_sym (negbTE ij) /= mulrA c2.
  by rewrite !mulr0 !mulr1 addr0 add0r -expr2 s2 mulVf // pnatr_eq0.
rewrite -(goe_equiv_formR u1 mphi); apply: eq_Rintegral => a _; congr phi.
set X := F (goe_mx a).
have Xji : X j i = X i j.
  have /symmetricmxP XT : X \is symmetricmx := Fsym (goe_mx_symmetric a).
  by rewrite -[in LHS]XT mxE.
rewrite -mxdot_rowE /u -scalemxAl mxdotZl mxdotZr mulmxDl -scalemxAl.
rewrite mxdotDl !mxdotDr !mxdotZl !mxdotZr !mxdot_delta -!rowE !mxE Xji.
rewrite mulrA c2; have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
have [->|->] : s = 1 \/ s = -1.
  by move/eqP: s2; rewrite sqrf_eq1 => /orP[] /eqP; [left|right].
- by field.
- by field.
Qed.

Hypothesis Fi : forall i j : 'I_N,
  (gauss (N * N)).-integrable [set: 'rV[R]_(N * N)]
    (EFin \o (fun a => F (goe_mx a) i j ^+ 2)).

Local Notation qint f :=
  ((gauss (N * N)).-integrable [set: 'rV[R]_(N * N)] (EFin \o f)).

Let mX (i j : 'I_N) :
  measurable_fun [set: 'rV[R]_(N * N)] (fun a => F (goe_mx a) i j).
Proof. exact: (measurable_fun_mxP _).1 Fm i j. Qed.

Let qintD (f g : 'rV[R]_(N * N) -> R) : qint f -> qint g ->
  qint (fun a => f a + g a).
Proof.
move=> fi gi; apply: (eq_integrable measurableT ((EFin \o f) \+ (EFin \o g))%E).
  by move=> a _; rewrite /= EFinD.
exact: integrableD.
Qed.

Let qintZ (k : R) (f : 'rV[R]_(N * N) -> R) : qint f -> qint (fun a => k * f a).
Proof.
move=> fi; apply: (eq_integrable measurableT (fun a => k%:E * (EFin \o f) a)%E).
  by move=> a _; rewrite /= EFinM.
exact: integrableZl.
Qed.

Let qintB (f g : 'rV[R]_(N * N) -> R) : qint f -> qint g ->
  qint (fun a => f a - g a).
Proof.
move=> fi gi; apply: (eq_integrable measurableT
  (fun a => (EFin \o f) a - (EFin \o g) a)%E).
  by move=> a _; rewrite /= EFinB.
exact: integrableB.
Qed.

Let qint_sum (I : Type) (s : seq I) (f : I -> 'rV[R]_(N * N) -> R) :
  (forall i, qint (f i)) -> qint (fun a => \sum_(i <- s) f i a).
Proof.
move=> fi; elim: s => [|i s IH].
  apply: (eq_integrable measurableT (EFin \o cst 0)).
    by move=> a _; rewrite /= big_nil.
  exact: finite_measure_integrable_cst.
apply: (eq_integrable measurableT
  (EFin \o (fun a => f i a + \sum_(j <- s) f j a))).
  by move=> a _; rewrite /= big_cons.
exact: qintD.
Qed.

Let qintXX (i j k l : 'I_N) :
  qint (fun a => F (goe_mx a) i j * F (goe_mx a) k l).
Proof.
apply: (le_integrable measurableT _ _ (qintD (Fi i j) (Fi k l))).
  by apply/measurable_EFinP; apply: measurable_funM.
move=> a _; rewrite /= lee_fin [`|_ + _|]ger0_norm ?addr_ge0 ?sqr_ge0 //.
set x := F (goe_mx a) i j; set y := F (goe_mx a) k l.
have hx : x ^+ 2 = `|x| ^+ 2 by rewrite -normrX ger0_norm // sqr_ge0.
have hy : y ^+ 2 = `|y| ^+ 2 by rewrite -normrX ger0_norm // sqr_ge0.
rewrite normrM hx hy; have := sqr_ge0 (`|x| - `|y|).
have := normr_ge0 x; have := normr_ge0 y; nra.
Qed.

Let Rint_sum2 (f : 'I_N -> 'I_N -> 'rV[R]_(N * N) -> R) :
  (forall i j, qint (f i j)) ->
  \int[gauss (N * N)%N]_a (\sum_i \sum_j f i j a) =
  \sum_i \sum_j \int[gauss (N * N)%N]_a f i j a.
Proof.
move=> fi; rewrite Rintegral_sum //; first by move=> i; apply: qint_sum => j.
apply: eq_bigr => i _; rewrite Rintegral_sum //.
Qed.

Local Ltac qint_tac := repeat first
  [ exact: qintXX | apply: qintD | apply: qintB | apply: qintZ
  | apply: qint_sum => ? ].

Let RintD (f g : 'rV[R]_(N * N) -> R) : qint f -> qint g ->
  \int[gauss (N * N)%N]_a (f a + g a) =
  \int[gauss (N * N)%N]_a f a + \int[gauss (N * N)%N]_a g a.
Proof. by move=> fi gi; rewrite RintegralD. Qed.

Let RintB (f g : 'rV[R]_(N * N) -> R) : qint f -> qint g ->
  \int[gauss (N * N)%N]_a (f a - g a) =
  \int[gauss (N * N)%N]_a f a - \int[gauss (N * N)%N]_a g a.
Proof. by move=> fi gi; rewrite RintegralB. Qed.

Let RintZ (k : R) (f : 'rV[R]_(N * N) -> R) : qint f ->
  \int[gauss (N * N)%N]_a (k * f a) = k * \int[gauss (N * N)%N]_a f a.
Proof. by move=> fi; rewrite RintegralZl. Qed.

Let msq : measurable_fun [set: R] (fun x : R => x ^+ 2).
Proof. exact: exprn_measurable. Qed.

(* E[F(W)_ij^2] and E[F(W)_ii F(W)_jj] in terms of c0 = E[F(W)_00^2]. *)
Lemma goe_equiv_diag2 (i : 'I_N) :
  \int[gauss (N * N)%N]_a (F (goe_mx a) i i * F (goe_mx a) i i) =
  \int[gauss (N * N)%N]_a F (goe_mx a) ord0 ord0 ^+ 2.
Proof.
rewrite -(goe_equiv_diag i msq).
by apply: eq_Rintegral => a _; rewrite expr2.
Qed.

Lemma goe_equiv_pair2 (i j : 'I_N) : i != j ->
  \int[gauss (N * N)%N]_a (F (goe_mx a) i i * F (goe_mx a) j j) +
  2 * \int[gauss (N * N)%N]_a (F (goe_mx a) i j * F (goe_mx a) i j) =
  \int[gauss (N * N)%N]_a F (goe_mx a) ord0 ord0 ^+ 2.
Proof.
move=> ij; set c0 := \int[gauss (N * N)%N]_a F (goe_mx a) ord0 ord0 ^+ 2.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
have h4 : (4 : R) != 0 by rewrite pnatr_eq0.
pose f (s : R) a := ((F (goe_mx a) i i + F (goe_mx a) j j) / 2 +
  s * F (goe_mx a) i j) ^+ 2.
have hf (s : R) : s ^+ 2 = 1 -> \int[gauss (N * N)%N]_a f s a = c0.
  by move=> s2; rewrite /c0 -(goe_equiv_pair ij s2 msq).
have qf (s : R) : qint (f s).
  apply: (eq_integrable measurableT (EFin \o (fun a =>
    4^-1 * (F (goe_mx a) i i * F (goe_mx a) i i) +
    4^-1 * (F (goe_mx a) j j * F (goe_mx a) j j) +
    2^-1 * (F (goe_mx a) i i * F (goe_mx a) j j) +
    s * (F (goe_mx a) i i * F (goe_mx a) i j) +
    s * (F (goe_mx a) j j * F (goe_mx a) i j) +
    s ^+ 2 * (F (goe_mx a) i j * F (goe_mx a) i j)))).
    by move=> a _ /=; congr EFin; rewrite /f; field.
  by qint_tac.
have h1 : (1 : R) ^+ 2 = 1 by rewrite expr1n.
have hN1 : (-1 : R) ^+ 2 = 1 by rewrite sqrrN expr1n.
have qA := qintZ (2^-1) (qintXX i i i i).
have qB := qintZ (2^-1) (qintXX j j j j).
have qC := qintXX i i j j.
have qD := qintZ 2 (qintXX i j i j).
have e1 : c0 + c0 = \int[gauss (N * N)%N]_a (f 1 a + f (-1) a).
  by rewrite (RintD (qf 1) (qf (-1))) (hf 1 h1) (hf (-1) hN1).
have e2 : \int[gauss (N * N)%N]_a (f 1 a + f (-1) a) =
    \int[gauss (N * N)%N]_a
      ((2^-1 * (F (goe_mx a) i i * F (goe_mx a) i i) +
        2^-1 * (F (goe_mx a) j j * F (goe_mx a) j j)) +
       (F (goe_mx a) i i * F (goe_mx a) j j +
        2 * (F (goe_mx a) i j * F (goe_mx a) i j))).
  by apply: eq_Rintegral => a _; rewrite /f; field.
rewrite e2 (RintD (qintD qA qB) (qintD qC qD)) in e1.
rewrite (RintD qA qB) (RintD qC qD) in e1.
rewrite (RintZ _ (qintXX i i i i)) (RintZ _ (qintXX j j j j)) in e1.
rewrite (RintZ _ (qintXX i j i j)) !goe_equiv_diag2 -/c0 in e1.
have hc : 2^-1 * c0 + 2^-1 * c0 = c0 by field.
by move: e1; rewrite hc => /addrI ->.
Qed.

(* Lemma 5.13 of Koehler and Sohn without the Haar measure, for N = d + 1. *)
Theorem goe_diag_var_identityS :
  \int[gauss (N * N)%N]_a diag_var (F (goe_mx a)) =
  2 / (N%:R + 2) * \int[gauss (N * N)%N]_a
    (mxdot (F (goe_mx a)) (F (goe_mx a)) / N%:R -
     (\tr (F (goe_mx a)) / N%:R) ^+ 2).
Proof.
set c0 := \int[gauss (N * N)%N]_a F (goe_mx a) ord0 ord0 ^+ 2.
set A := \sum_i \sum_j
  \int[gauss (N * N)%N]_a (F (goe_mx a) i i * F (goe_mx a) j j).
set B := \sum_i \sum_j
  \int[gauss (N * N)%N]_a (F (goe_mx a) i j * F (goe_mx a) i j).
have n0 : N%:R != 0 :> R by rewrite pnatr_eq0.
have n2 : N%:R + 2 != 0 :> R by rewrite -natrD pnatr_eq0.
have trE (X : 'M[R]_N) : (\tr X / N%:R) ^+ 2 =
    (N%:R ^+ 2)^-1 * \sum_i \sum_j (X i i * X j j).
  by rewrite expr_div_n mulrC /mxtrace [(\sum_i _) ^+ 2]expr2 big_distrlr.
have qS1 : qint (fun a =>
    N%:R^-1 * \sum_j (F (goe_mx a) j j * F (goe_mx a) j j)).
  by qint_tac.
have qS2 : qint (fun a => (N%:R ^+ 2)^-1 *
    \sum_i \sum_j (F (goe_mx a) i i * F (goe_mx a) j j)).
  by qint_tac.
have qS3 : qint (fun a => N%:R^-1 *
    \sum_i \sum_j (F (goe_mx a) i j * F (goe_mx a) i j)).
  by qint_tac.
have hL : \int[gauss (N * N)%N]_a diag_var (F (goe_mx a)) =
    c0 - (N%:R ^+ 2)^-1 * A.
  transitivity (\int[gauss (N * N)%N]_a
    (N%:R^-1 * \sum_j (F (goe_mx a) j j * F (goe_mx a) j j) -
     (N%:R ^+ 2)^-1 * \sum_i \sum_j (F (goe_mx a) i i * F (goe_mx a) j j))).
    apply: eq_Rintegral => a _; rewrite diag_varE trE.
    by under eq_bigr do rewrite expr2.
  rewrite (RintB qS1 qS2) (RintZ _ (qint_sum _ (fun j => qintXX j j j j))).
  rewrite (RintZ _ (qint_sum _ (fun i =>
    qint_sum _ (fun j => qintXX i i j j)))).
  rewrite (Rint_sum2 (fun i j => qintXX i i j j)).
  rewrite (Rintegral_sum _ measurableT (fun j => qintXX j j j j)).
  under eq_bigr do rewrite goe_equiv_diag2.
  rewrite sumr_const card_ord -/c0 -/A -[c0 *+ _]mulr_natl.
  by rewrite mulrA mulVf // mul1r.
have hR : \int[gauss (N * N)%N]_a
    (mxdot (F (goe_mx a)) (F (goe_mx a)) / N%:R -
     (\tr (F (goe_mx a)) / N%:R) ^+ 2) =
    N%:R^-1 * B - (N%:R ^+ 2)^-1 * A.
  transitivity (\int[gauss (N * N)%N]_a
    (N%:R^-1 * \sum_i \sum_j (F (goe_mx a) i j * F (goe_mx a) i j) -
     (N%:R ^+ 2)^-1 * \sum_i \sum_j (F (goe_mx a) i i * F (goe_mx a) j j))).
    by apply: eq_Rintegral => a _; rewrite trE /mxdot mulrC.
  rewrite (RintB qS3 qS2).
  rewrite (RintZ _ (qint_sum _ (fun i =>
    qint_sum _ (fun j => qintXX i j i j)))).
  rewrite (RintZ _ (qint_sum _ (fun i =>
    qint_sum _ (fun j => qintXX i i j j)))).
  rewrite (Rint_sum2 (fun i j => qintXX i j i j)).
  by rewrite (Rint_sum2 (fun i j => qintXX i i j j)).
have hg (i j : 'I_N) :
    \int[gauss (N * N)%N]_a (F (goe_mx a) i i * F (goe_mx a) j j) +
    2 * \int[gauss (N * N)%N]_a (F (goe_mx a) i j * F (goe_mx a) i j) =
    c0 + (i == j)%:R * (2 * c0).
  have [<-|ij] := eqVneq i j.
    by rewrite goe_equiv_diag2 -/c0 -[true%:R]/(1 : R) mul1r.
  by rewrite -[false%:R]/(0 : R) mul0r addr0 goe_equiv_pair2.
have hs (i : 'I_N) :
    \sum_(j < N) (c0 + (i == j)%:R * (2 * c0)) = (N%:R + 2) * c0.
  have h0 : \sum_(j < N | j != i) (i == j)%:R * (2 * c0) = 0.
    by apply: big1 => j; rewrite eq_sym => /negbTE ->; rewrite mul0r.
  rewrite big_split /= sumr_const card_ord -[c0 *+ _]mulr_natl.
  rewrite (bigD1 i) //= eqxx mul1r.
  rewrite h0 addr0; ring.
have hAB : A + 2 * B = N%:R * (N%:R + 2) * c0.
  rewrite /A /B mulr_sumr -big_split /=.
  transitivity (\sum_(i < N) (N%:R + 2) * c0); last first.
    by rewrite sumr_const card_ord -[(_ * c0) *+ _]mulr_natl mulrA.
  apply: eq_bigr => i _; rewrite mulr_sumr -big_split /= -(hs i).
  by apply: eq_bigr => j _; exact: hg.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
rewrite hL hR.
have -> : B = (N%:R * (N%:R + 2) * c0 - A) / 2.
  by rewrite -hAB; field.
by field.
Qed.

End goe_equivariant.

Section goe_diag.
Context {R : realType} (n : nat).
Variable F : 'M[R]_n -> 'M[R]_n.
Hypothesis Feq : conj_equivariant F.
Hypothesis Fsym : forall W : 'M[R]_n, W \is symmetricmx -> F W \is symmetricmx.
Hypothesis Fm : measurable_fun [set: 'rV[R]_(n * n)] (fun a => F (goe_mx a)).

(* Lemma 5.13 of Koehler and Sohn, with the GOE instead of a Haar matrix:
   for F equivariant and E |F(W)|_F^2 finite, the diagonal of F(W) has
   E[diag_var F(W)] = 2 / (n + 2) E[|F(W)|_F^2 / n - (tr F(W) / n)^2]. *)
Theorem goe_diag_var_identity :
  (forall i j : 'I_n, (gauss (n * n)).-integrable [set: 'rV[R]_(n * n)]
     (EFin \o (fun a => F (goe_mx a) i j ^+ 2))) ->
  \int[gauss (n * n)%N]_a diag_var (F (goe_mx a)) =
  2 / (n%:R + 2) * \int[gauss (n * n)%N]_a
    (mxdot (F (goe_mx a)) (F (goe_mx a)) / n%:R -
     (\tr (F (goe_mx a)) / n%:R) ^+ 2).
Proof.
move: F Feq Fsym Fm; case: n => [|d] G Geq Gsym Gm Gi; last first.
  by apply: goe_diag_var_identityS.
have h0 (A : 'M[R]_0) : diag_var A = 0 by rewrite /diag_var big_ord0 mulr0.
have h1 (A : 'M[R]_0) : mxdot A A / 0%:R - (\tr A / 0%:R) ^+ 2 = 0.
  by rewrite mulr0n invr0 !mulr0 expr2 mul0r subr0.
under eq_Rintegral do rewrite h0.
under [X in _ = _ * X]eq_Rintegral do rewrite h1.
by rewrite Rintegral_cst // mul0r mulr0.
Qed.

End goe_diag.

Section goe_diag_tail.
Context {R : realType} (n : nat).
Variable F : 'M[R]_n -> 'M[R]_n.
Hypothesis Feq : conj_equivariant F.
Hypothesis Fsym : forall W : 'M[R]_n, W \is symmetricmx -> F W \is symmetricmx.
Hypothesis Fm : measurable_fun [set: 'rV[R]_(n * n)] (fun a => F (goe_mx a)).

(* The diagonal of F(W) is nearly constant: for C >= 0 and eps > 0,
   P(diag_var F(W) >= eps) <= 2 C / ((n + 2) eps) + P(|F(W)|_F^2 > C n).
   The second term is small when |F(W)|_F^2 / n is bounded in probability,
   as for the positive part of W - w I with w bounded. *)
Theorem goe_diag_var_tail (C eps : R) : 0 <= C -> 0 < eps ->
  (gauss (n * n) [set a | (eps <= diag_var (F (goe_mx a)))%R] <=
   (2 * C / ((n%:R + 2) * eps))%:E +
   gauss (n * n)
     [set a | (C * n%:R < mxdot (F (goe_mx a)) (F (goe_mx a)))%R])%E.
Proof.
move=> C0 eps0.
pose G (W : 'M[R]_n) := if mxdot (F W) (F W) <= C * n%:R then F W else 0.
have mX (i j : 'I_n) : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => F (goe_mx a) i j) := (measurable_fun_mxP _).1 Fm i j.
have mN : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => mxdot (F (goe_mx a)) (F (goe_mx a))).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  exact: measurable_funM.
have mc := measurable_fun_ler mN (measurable_cst (C * n%:R)).
have Geq : conj_equivariant G.
  move=> Q W Qo Ws; rewrite /G Feq //.
  rewrite mxdot_orthogonalmxr ?trmx_orthogonal // mxdot_orthogonalmxl //.
  by case: ifP => // _; rewrite mulmx0 mul0mx.
have Gsym (W : 'M[R]_n) : W \is symmetricmx -> G W \is symmetricmx.
  move=> Ws; rewrite /G; case: ifP => _; first exact: Fsym.
  by apply/symmetricmxP; rewrite trmx0.
have Gm : measurable_fun [set: 'rV[R]_(n * n)] (fun a => G (goe_mx a)).
  exact: measurable_fun_ifT mc Fm (measurable_cst _).
have GC (W : 'M[R]_n) : mxdot (G W) (G W) <= C * n%:R.
  by rewrite /G; case: ifP => // _; rewrite mxdot0l mulr_ge0 // ler0n.
have hdiv (x : R) : x <= C * n%:R -> x / n%:R <= C.
  have [->|n0] := eqVneq (n%:R : R) 0; first by move=> _; rewrite invr0 mulr0.
  have nP : 0 < n%:R :> R by rewrite lt0r n0 ler0n.
  by move=> h; rewrite ler_pdivrMr.
have mGe (i j : 'I_n) : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => G (goe_mx a) i j) := (measurable_fun_mxP _).1 Gm i j.
have Gi (i j : 'I_n) : (gauss (n * n)).-integrable [set: 'rV[R]_(n * n)]
    (EFin \o (fun a => G (goe_mx a) i j ^+ 2)).
  apply: (le_integrable measurableT _ _
    (finite_measure_integrable_cst _ (C * n%:R) measurableT)).
    by apply/measurable_EFinP; apply: measurableT_comp (exprn_measurable 2) _.
  move=> a _; rewrite /= lee_fin ger0_norm ?sqr_ge0 //.
  rewrite [`|C * _|]ger0_norm ?mulr_ge0 ?ler0n //.
  exact: le_trans (mxdot_entry _ i j) (GC _).
have key := goe_diag_var_identity Geq Gsym Gm Gi.
have mtr : measurable_fun [set: 'rV[R]_(n * n)] (fun a => \tr (G (goe_mx a))).
  by rewrite /mxtrace; apply: measurable_sum => i.
have mdv : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => diag_var (G (goe_mx a))).
  rewrite /diag_var; apply: measurable_funM => //; apply: measurable_sum => j.
  apply: measurableT_comp (exprn_measurable 2) _; apply: measurable_funB => //.
  by apply: measurable_funM.
have dvC a : diag_var (G (goe_mx a)) <= C.
  rewrite diag_varE.
  apply: (@le_trans _ _ (n%:R^-1 * \sum_j G (goe_mx a) j j ^+ 2)).
    by rewrite gerBl sqr_ge0.
  by rewrite mulrC; apply: hdiv; exact: le_trans (diag_sqr_le _) (GC _).
have idv : (gauss (n * n)).-integrable [set: 'rV[R]_(n * n)]
    (EFin \o (fun a => diag_var (G (goe_mx a)))).
  apply: (le_integrable measurableT _ _
    (finite_measure_integrable_cst _ C measurableT)).
    exact/measurable_EFinP.
  move=> a _; rewrite /= lee_fin ger0_norm ?diag_var_ge0 //.
  exact: le_trans (dvC a) (ler_norm _).
have mGG : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => mxdot (G (goe_mx a)) (G (goe_mx a))).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  exact: measurable_funM.
have mh : measurable_fun [set: 'rV[R]_(n * n)] (fun a =>
    mxdot (G (goe_mx a)) (G (goe_mx a)) / n%:R -
    (\tr (G (goe_mx a)) / n%:R) ^+ 2).
  apply: measurable_funB; first exact: measurable_funM.
  by apply: measurableT_comp (exprn_measurable 2) _; exact: measurable_funM.
have hC a : mxdot (G (goe_mx a)) (G (goe_mx a)) / n%:R -
    (\tr (G (goe_mx a)) / n%:R) ^+ 2 <= C.
  apply: (@le_trans _ _ (mxdot (G (goe_mx a)) (G (goe_mx a)) / n%:R)).
    by rewrite gerBl sqr_ge0.
  exact: hdiv (GC _).
have ih : (gauss (n * n)).-integrable [set: 'rV[R]_(n * n)] (EFin \o (fun a =>
    mxdot (G (goe_mx a)) (G (goe_mx a)) / n%:R -
    (\tr (G (goe_mx a)) / n%:R) ^+ 2)).
  apply: (le_integrable measurableT _ _
    (finite_measure_integrable_cst _ C measurableT)).
    exact/measurable_EFinP.
  move=> a _; rewrite /= lee_fin ger0_norm ?subr_ge0 ?trace_sqr_le //.
  exact: le_trans (hC a) (ler_norm _).
have hI : \int[gauss (n * n)%N]_a
    (mxdot (G (goe_mx a)) (G (goe_mx a)) / n%:R -
     (\tr (G (goe_mx a)) / n%:R) ^+ 2) <= C.
  apply: le_trans (le_Rintegral measurableT ih
    (finite_measure_integrable_cst _ C measurableT) (fun a _ => hC a)) _.
  rewrite Rintegral_cst // -[X in fine X]/(@gauss R (n * n) setT).
  by rewrite probability_setT /= mulr1.
have n2 : 0 < n%:R + 2 :> R by rewrite ltr_wpDl ?ler0n.
have hE : \int[gauss (n * n)%N]_a diag_var (G (goe_mx a)) <=
    2 * C / (n%:R + 2).
  rewrite key [2 * C / _]mulrAC; apply: ler_wpM2l hI.
  by rewrite divr_ge0 // ltW.
have mset (f : 'rV[R]_(n * n) -> R) (c : R) :
    measurable_fun [set: 'rV[R]_(n * n)] f -> measurable [set a | c <= f a].
  move=> mf; have := mf measurableT _ (measurable_itv `[c, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => x /=; rewrite in_itv /= andbT.
have mset_lt (f : 'rV[R]_(n * n) -> R) (c : R) :
    measurable_fun [set: 'rV[R]_(n * n)] f -> measurable [set a | c < f a].
  move=> mf; have := mf measurableT _ (measurable_itv `]c, +oo[).
  rewrite setTI; congr measurable; apply/seteqP.
  by split => x /=; rewrite in_itv /= andbT.
have mdvF : measurable_fun [set: 'rV[R]_(n * n)]
    (fun a => diag_var (F (goe_mx a))).
  have mtrF : measurable_fun [set: 'rV[R]_(n * n)]
      (fun a => \tr (F (goe_mx a))).
    by rewrite /mxtrace; apply: measurable_sum => i.
  rewrite /diag_var; apply: measurable_funM => //; apply: measurable_sum => j.
  apply: measurableT_comp (exprn_measurable 2) _; apply: measurable_funB => //.
  by apply: measurable_funM.
have mA := mset _ eps mdvF.
have mA' := mset _ eps mdv.
have mB := mset_lt _ (C * n%:R) mN.
have hsub : [set a | eps <= diag_var (F (goe_mx a))] `<=`
    [set a | eps <= diag_var (G (goe_mx a))] `|`
    [set a | C * n%:R < mxdot (F (goe_mx a)) (F (goe_mx a))].
  move=> a /= ha.
  have [hc|hc] := leP (mxdot (F (goe_mx a)) (F (goe_mx a))) (C * n%:R).
    by left; rewrite /= /G hc.
  by right.
apply: le_trans (le_measure _ _ _ hsub) _.
- by rewrite inE.
- by rewrite inE; exact: measurableU.
apply: le_trans (measureU2 _ mA' mB) _.
apply: leeD => //.
apply: le_trans (gauss_markov eps0 mdv (fun a => diag_var_ge0 _) idv) _.
rewrite lee_fin.
have e0 : eps != 0 := lt0r_neq0 eps0.
have n2' : n%:R + 2 != 0 :> R := lt0r_neq0 n2.
have -> : 2 * C / ((n%:R + 2) * eps) = eps^-1 * (2 * C / (n%:R + 2)).
  by field.
by apply: ler_wpM2l hE; rewrite invr_ge0 ltW.
Qed.

End goe_diag_tail.
