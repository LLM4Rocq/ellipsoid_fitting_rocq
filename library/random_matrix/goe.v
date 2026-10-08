From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability arithmetic_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_ibp.

(**md**************************************************************************)
(* # The Gaussian orthogonal ensemble                                         *)
(*                                                                            *)
(* For a of law gauss (d * d), goe_mx a is the symmetric matrix W = (A + A^T) *)
(* / sqrt (2 d) with A = vec_mx a: the entries W_ij, i <= j, are independent  *)
(* centered normal with variance 1 / d off the diagonal and 2 / d on it. This *)
(* normalization has the semicircle law of radius 2 (semicircle_prob 2 of     *)
(* probability/semicircle_law.v) as limit of its spectrum. The Gaussian       *)
(* features of Koehler and Sohn at kappa = 3 (arXiv 2608.27372, lines         *)
(* 1004-1086) have the same law up to mxvec. This file is part of item G7 of  *)
(* phase 5.                                                                   *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - polyfun F: F is continuous on 'rV[R]_m and of polynomial growth, the     *)
(*   hypothesis of Gaussian integration by parts (gauss_ibp); it holds for    *)
(*   constants and coordinates and is stable under sums and products          *)
(*   (polyfunD, polyfunM, polyfun_sum), hence for the entries of sums,        *)
(*   products and powers of matrices with such entries (mx_polyfun) and for   *)
(*   their traces.                                                            *)
(* - is_derive_mxpow: the derivative of M |-> (M ^+ k) i j at W along E is    *)
(*   the entry (i, j) of mxpow_deriv W E k = \sum_(r < k) W^r E W^(k-1-r).    *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - Gaussian integration by parts for W: E[W_ij F (W)] = (1 / d) E[d_ij F    *)
(*   (W) + d_ji F (W)] for F of class C^1 with derivatives of polynomial      *)
(*   growth (from gauss_ibp).                                                 *)
(* - The Schwinger-Dyson equation for the moments t_k = \tr (W^k) / d: E      *)
(*   t_(k+1) = (k / d) E t_(k-1) + \sum_(r < k) E[t_r t_(k-1-r)].             *)
(* - Var t_k = O(1 / d^2), by the Gaussian Poincare inequality.               *)
(* - E t_k tends to the k-th moment of semicircle_prob 2 (a Catalan number    *)
(*   for k even, 0 for k odd).                                                *)
(* - A crude bound on the operator norm: the probability that opnorm W >= 3   *)
(*   is at most exp (- c d) for some c > 0 (gauss_opnorm_tail of              *)
(*   comparison/escape.v).                                                    *)
(*                                                                            *)
(* ```                                                                        *)
(*          goe_mx a == the GOE matrix (A + A^T) / sqrt (2 d) of a row        *)
(*                      vector a of size d * d, A = vec_mx a                  *)
(*         polyfun F == F is continuous with |F x| <= C (1 + |x|^k)           *)
(*      mx_polyfun A == every entry of the matrix function A is a polyfun     *)
(* mxpow_deriv W E k == \sum_(r < k) W ^+ r *m E *m W ^+ (k.-1 - r)           *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section polyfun.
Context {R : realType}.

Lemma continuous_mxentry m n (i : 'I_m) (j : 'I_n) :
  continuous (fun M : 'M[R]_(m, n) => M i j).
Proof.
move=> M; apply/(cvgrPdist_lt (F := nbhs M)) => e e0.
have := @cvgr_dist_lt _ _ _ (nbhs M) (nbhs_filter M) id M cvg_id _ e0.
apply: filterS => N hN; apply: le_lt_trans hN.
have -> : M i j - N i j = (M - N) i j by rewrite !mxE.
exact: mx_norm_entry_le.
Qed.

Lemma exprn_le1D (t : R) a b : 0 <= t -> t ^+ a <= 1 + t ^+ (a + b).
Proof.
move=> t0; have [t1|t1] := leP t 1.
  by apply: le_trans (exprn_ile1 _ t0 t1) _; rewrite lerDl exprn_ge0.
apply: le_trans (_ : t ^+ (a + b) <= _); last by rewrite lerDr.
by rewrite ler_eXn2l // leq_addr.
Qed.

Lemma poly_bound_le (t C : R) a b : 0 <= t -> 0 <= C ->
  C * (1 + t ^+ a) <= (2 * C) * (1 + t ^+ (a + b)).
Proof.
move=> t0 C0; have e := exprn_le1D a b t0; have p := exprn_ge0 (a + b) t0.
have q := exprn_ge0 a t0; nra.
Qed.

Context {m : nat}.
Implicit Types F G : 'rV[R]_m -> R.

(* Continuous functions of polynomial growth on 'rV[R]_m, the integrands of
   Gaussian integration by parts (gauss_ibp). *)
Definition polyfun F :=
  continuous F /\ exists (C : R) (k : nat), forall x, `|F x| <= C * (1 + `|x| ^+ k).

(* Two functions of polynomial growth have a common bound. *)
Lemma polyfun_bound2 F G : polyfun F -> polyfun G ->
  exists (C : R) (k : nat), (forall x, `|F x| <= C * (1 + `|x| ^+ k)) /\
              (forall x, `|G x| <= C * (1 + `|x| ^+ k)).
Proof.
move=> [_ [C1 [k1 h1]]] [_ [C2 [k2 h2]]].
have C10 := poly_bound_ge0 h1; have C20 := poly_bound_ge0 h2.
exists (2 * (C1 + C2)), (k1 + k2)%N.
split => x; have t0 := normr_ge0 x; have p := exprn_ge0 (k1 + k2) t0.
  apply: le_trans (h1 x) _; apply: le_trans (poly_bound_le k1 k2 t0 C10) _.
  by apply: ler_wpM2r; [rewrite addr_ge0 | lra].
apply: le_trans (h2 x) _; rewrite addnC.
apply: le_trans (poly_bound_le k2 k1 t0 C20) _.
by apply: ler_wpM2r; [rewrite addr_ge0 | lra].
Qed.

Lemma polyfun_cst c : polyfun (fun=> c).
Proof.
split; first exact: cst_continuous.
exists `|c|, 0%N => x; rewrite expr0 ler_peMr //; lra.
Qed.

Lemma polyfun_coord (p : 'I_m) : polyfun (fun x => x 0 p).
Proof.
split; first exact: continuous_mxentry.
exists 1, 1%N => x; rewrite mul1r expr1.
by apply: le_trans (mx_norm_entry_le x 0 p) _; rewrite lerDr.
Qed.

Lemma polyfunD F G : polyfun F -> polyfun G -> polyfun (fun x => F x + G x).
Proof.
move=> hF hG; have [C [k [h1 h2]]] := polyfun_bound2 hF hG.
split; first by move=> x; exact: continuousD (hF.1 x) (hG.1 x).
exists (2 * C), k => x; apply: le_trans (ler_normD _ _) _.
by have := h1 x; have := h2 x; lra.
Qed.

Lemma polyfunM F G : polyfun F -> polyfun G -> polyfun (fun x => F x * G x).
Proof.
move=> [cF [C1 [k1 h1]]] [cG [C2 [k2 h2]]].
have C10 := poly_bound_ge0 h1; have C20 := poly_bound_ge0 h2.
split; first by move=> x; exact: continuousM (cF x) (cG x).
exists (4 * (C1 * C2)), (k1 + k2) => x; rewrite normrM.
have t0 := normr_ge0 x.
apply: le_trans (ler_pM (normr_ge0 _) (normr_ge0 _) (h1 x) (h2 x)) _.
have e1 := exprn_le1D k1 k2 t0; have e2 := exprn_le1D k2 k1 t0.
rewrite addnC in e2.
have p1 := exprn_ge0 k1 t0; have p2 := exprn_ge0 k2 t0.
have p12 := exprn_ge0 (k1 + k2) t0.
rewrite exprD in p12 e1 e2 *.
have C12 := mulr_ge0 C10 C20; nra.
Qed.

Lemma polyfun_sum (I : Type) (s : seq I) (F : I -> 'rV[R]_m -> R) :
  (forall i, polyfun (F i)) -> polyfun (fun x => \sum_(i <- s) F i x).
Proof.
move=> hF; elim: s => [|i s ih].
  by under eq_fun do rewrite big_nil; exact: polyfun_cst.
by under eq_fun do rewrite big_cons; exact: polyfunD.
Qed.

(* Matrices whose entries are continuous functions of polynomial growth. *)
Definition mx_polyfun p q (A : 'rV[R]_m -> 'M[R]_(p, q)) :=
  forall i j, polyfun (fun x => A x i j).

Lemma mx_polyfun_cst p q (B : 'M[R]_(p, q)) : mx_polyfun (fun=> B).
Proof. by move=> i j; exact: polyfun_cst. Qed.

Lemma mx_polyfunD p q (A B : 'rV[R]_m -> 'M[R]_(p, q)) :
  mx_polyfun A -> mx_polyfun B -> mx_polyfun (fun x => A x + B x).
Proof.
move=> hA hB i j; under eq_fun do rewrite mxE; exact: polyfunD.
Qed.

Lemma mx_polyfunZ p q c (A : 'rV[R]_m -> 'M[R]_(p, q)) :
  mx_polyfun A -> mx_polyfun (fun x => c *: A x).
Proof.
move=> hA i j; under eq_fun do rewrite mxE.
exact: polyfunM (polyfun_cst c) (hA i j).
Qed.

Lemma mx_polyfun_mul p q r (A : 'rV[R]_m -> 'M[R]_(p, q))
    (B : 'rV[R]_m -> 'M[R]_(q, r)) :
  mx_polyfun A -> mx_polyfun B -> mx_polyfun (fun x => A x *m B x).
Proof.
move=> hA hB i j; under eq_fun do rewrite mxE.
by apply: polyfun_sum => l; exact: polyfunM.
Qed.

Lemma mx_polyfun_sum (I : Type) (s : seq I) p q
    (A : I -> 'rV[R]_m -> 'M[R]_(p, q)) :
  (forall i, mx_polyfun (A i)) -> mx_polyfun (fun x => \sum_(i <- s) A i x).
Proof.
move=> hA i j; under eq_fun do rewrite summxE.
by apply: polyfun_sum => l; exact: hA.
Qed.

Lemma mx_polyfun_exp p (A : 'rV[R]_m -> 'M[R]_p) k :
  mx_polyfun A -> mx_polyfun (fun x => A x ^+ k).
Proof.
move=> hA; elim: k => [|k ih].
  by under eq_fun do rewrite expr0; exact: mx_polyfun_cst.
under eq_fun do rewrite exprSr -mulmxE; exact: mx_polyfun_mul.
Qed.

Lemma polyfun_trace p (A : 'rV[R]_m -> 'M[R]_p) :
  mx_polyfun A -> polyfun (fun x => \tr (A x)).
Proof. by move=> hA; apply: polyfun_sum => i; exact: hA. Qed.

End polyfun.

Section mxpow_derive.
Context {R : realType} {n : nat}.
Implicit Types W E : 'M[R]_n.

(* The derivative of M |-> M ^+ k at W along E. *)
Definition mxpow_deriv W E k : 'M[R]_n :=
  \sum_(r < k) W ^+ r *m E *m W ^+ (k.-1 - r).

Lemma mxpow_derivS W E k :
  mxpow_deriv W E k.+1 = mxpow_deriv W E k *m W + W ^+ k *m E.
Proof.
rewrite /mxpow_deriv big_ord_recr /= subnn expr0 mulmx1; congr (_ + _).
rewrite mulmx_suml; apply: eq_bigr => r _; rewrite -[RHS]mulmxA.
congr (_ *m _); have k0 : (0 < k)%N := leq_ltn_trans (leq0n r) (ltn_ord r).
have -> : (k - r = (k.-1 - r).+1)%N.
  by rewrite -subSn ?prednK // -ltnS prednK.
by rewrite exprSr mulmxE.
Qed.

Lemma is_derive_mxentry W E (i j : 'I_n) :
  is_derive W E (fun M : 'M[R]_n => M i j) (E i j).
Proof.
apply: (is_derive_transfer (G := fun t : R => E i j *: t + W i j) (b := 0)
  (w := 1)).
  by move=> h; rewrite !mxE addr0 /GRing.scale /= mulr1 mulrC.
have -> : (fun t : R => E i j *: t + W i j) = *:%R (E i j) + cst (W i j).
  by [].
by apply: is_derive_eq; rewrite addr0 /GRing.scale /= mulr1.
Qed.

Lemma is_derive_mxpow W E k (i j : 'I_n) :
  is_derive W E (fun M : 'M[R]_n => (M ^+ k) i j) (mxpow_deriv W E k i j).
Proof.
elim: k i j => [|k ih] i j.
  rewrite /mxpow_deriv big_ord0 [X in is_derive _ _ _ X]mxE.
  have -> : (fun M : 'M[R]_n => (M ^+ 0) i j) = cst ((1%:M : 'M[R]_n) i j).
    by apply/funext => M; rewrite expr0.
  exact: is_derive_cst.
have -> : (fun M : 'M[R]_n => (M ^+ k.+1) i j) =
    \sum_(l < n) ((fun M : 'M[R]_n => (M ^+ k) i l) * (fun M => M l j)).
  apply/funext => M; rewrite exprSr -mulmxE mxE fct_sumE.
  by apply: eq_bigr => l _.
apply: is_derive_eq.
  apply: is_derive_sum => l.
  exact: is_deriveM (ih i l) (is_derive_mxentry W E l j).
rewrite mxpow_derivS [RHS]mxE !mxE -big_split /=; apply: eq_bigr => l _.
by rewrite /GRing.scale /= addrC mulrC.
Qed.

End mxpow_derive.

Section goe.
Context {R : realType}.

(* The GOE matrix (A + A^T) / sqrt (2 d) of a row vector of size d * d. *)
Definition goe_mx d (a : 'rV[R]_(d * d)) : 'M[R]_d :=
  (Num.sqrt (2 * d%:R))^-1 *: (vec_mx a + (vec_mx a)^T).

Lemma goe_mx_sym d (a : 'rV[R]_(d * d)) : (goe_mx a)^T = goe_mx a.
Proof. by rewrite /goe_mx linearZ /= linearD /= trmxK addrC. Qed.

End goe.
