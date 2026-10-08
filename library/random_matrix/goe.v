From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From GaussianAnalysis.comparison Require Import gauss_concentration escape.
From GaussianAnalysis.fourier Require Import charfun_rV.

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
(*   the entry (i, j) of mxpow_deriv W E k = \sum_(r < k) W^r E W^(k-1-r);    *)
(*   mxpow_deriv_trace: for W symmetric, \sum_(i, j) of the entries (j, i) of *)
(*   mxpow_deriv W (E_ij + E_ji) k is k tr W^(k-1) + \sum_(r < k) tr W^r tr   *)
(*   W^(k-1-r).                                                               *)
(* - gauss_ibp_polyfun: Gaussian integration by parts E[x_p F x] = E[d_p F x] *)
(*   for F and d_p F of polynomial growth.                                    *)
(* - goe_schwinger_dyson: the Schwinger-Dyson equation for the moments of W,  *)
(*   E tr W^(k+1) = (k E tr W^(k-1) + \sum_(r < k) E[tr W^r tr W^(k-1-r)])    *)
(*   / d, by integration by parts in each coordinate a_ij of a; with t_k = tr *)
(*   W^k / d it reads E t_(k+1) = (k / d) E t_(k-1) + \sum_(r < k) E[t_r      *)
(*   t_(k-1-r)].                                                              *)
(* - The operator norm: frobenius W <= sqrt (2 / d) |a| (frobenius_goe_mx),   *)
(*   so opnorm W is sqrt (2 / d)-Lipschitz in a (goe_opnorm_lipschitz);       *)
(*   E opnorm W <= 2 sqrt 2 for d >= 1 (goe_opnorm_mean, from                 *)
(*   gauss_opnorm_mean and E |g| <= sqrt n, gauss_frobenius_mean); and        *)
(*   E exp (s opnorm W) <= exp (2 sqrt 2 s + s^2 / d) for s >= 0              *)
(*   (goe_opnorm_mgf, by Gaussian concentration).                             *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
(* - Var t_k -> 0 as d -> oo: t_k is the statistic of clip_3(x)^k, which is   *)
(*   Lipschitz in a with constant O(1 / d), up to an error bounded by         *)
(*   opnorm W^k exp (u (opnorm W - 3)), small by goe_opnorm_mgf.              *)
(* - E t_k tends to the k-th moment of semicircle_prob 2 (a Catalan number    *)
(*   for k even, 0 for k odd), by goe_schwinger_dyson and semicircle_catalan  *)
(*   of wigner.v.                                                             *)
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

Lemma mxpow_derivD W E F k :
  mxpow_deriv W (E + F) k = mxpow_deriv W E k + mxpow_deriv W F k.
Proof.
rewrite /mxpow_deriv -big_split; apply: eq_bigr => r _.
by rewrite mulmxDr mulmxDl.
Qed.

Lemma mxpow_derivZ W E c k : mxpow_deriv W (c *: E) k = c *: mxpow_deriv W E k.
Proof.
rewrite /mxpow_deriv scaler_sumr; apply: eq_bigr => r _.
by rewrite -scalemxAr -scalemxAl.
Qed.

Lemma mulmx_delta_entry p q (A : 'M[R]_(p, n)) (B : 'M[R]_(n, q)) i j a b :
  (A *m delta_mx i j *m B) a b = A a i * B j b.
Proof.
rewrite mxE (bigD1 j) //= big1 ?addr0.
  move=> l lj; rewrite mxE big1 ?mul0r // => m _.
  by rewrite mxE (negbTE lj) andbF mulr0.
rewrite mxE (bigD1 i) //= big1 ?addr0.
  by move=> m mi; rewrite mxE (negbTE mi) mulr0.
by rewrite mxE !eqxx mulr1.
Qed.

Lemma trmx_exp W k : (W ^+ k)^T = W^T ^+ k.
Proof.
elim: k => [|k ih]; first by rewrite !expr0 trmx1.
by rewrite exprSr -mulmxE trmx_mul ih mulmxE -exprS.
Qed.

(* The sum over (i, j) of the entries (j, i) of the derivative of W^k along
   E_ij + E_ji: k tr W^(k-1) + \sum_(r < k) tr W^r tr W^(k-1-r) for W
   symmetric. *)
Lemma mxpow_deriv_trace W k : W^T = W ->
  \sum_i \sum_j mxpow_deriv W (delta_mx i j + delta_mx j i) k j i =
  k%:R * \tr (W ^+ k.-1) + \sum_(r < k) \tr (W ^+ r) * \tr (W ^+ (k.-1 - r)).
Proof.
move=> WT; have sym r : (W ^+ r)^T = W ^+ r by rewrite trmx_exp WT.
have -> : \sum_i \sum_j mxpow_deriv W (delta_mx i j + delta_mx j i) k j i =
    \sum_(r < k) \sum_i \sum_j ((W ^+ r) j i * (W ^+ (k.-1 - r)) j i +
      (W ^+ r) j j * (W ^+ (k.-1 - r)) i i).
  rewrite [RHS]exchange_big; apply: eq_bigr => i _.
  rewrite [RHS]exchange_big; apply: eq_bigr => j _.
  rewrite /mxpow_deriv summxE; apply: eq_bigr => r _.
  by rewrite mulmxDr mulmxDl mxE !mulmx_delta_entry.
have -> : k%:R * \tr (W ^+ k.-1) = \sum_(r < k) \tr (W ^+ k.-1).
  by rewrite sumr_const card_ord mulr_natl.
rewrite -big_split; apply: eq_bigr => r _ /=.
under eq_bigr do rewrite big_split; rewrite big_split /=.
congr (_ + _).
  have rk : (r <= k.-1)%N.
    by rewrite -ltnS prednK // (leq_ltn_trans _ (ltn_ord r)).
  rewrite -[in RHS](subnKC rk) exprD -mulmxE -[X in _ *m X]sym.
  rewrite exchange_big /mxtrace; apply: eq_bigr => j _; rewrite mxE.
  by apply: eq_bigr => i _; rewrite mxE.
rewrite /mxtrace mulr_sumr; apply: eq_bigr => i _.
by rewrite mulr_suml.
Qed.

End mxpow_derive.

Section mxpow_polyfun.
Context {R : realType} {m n : nat}.

Lemma mx_polyfun_mxpow_deriv (A : 'rV[R]_m -> 'M[R]_n) (E : 'M[R]_n) k :
  mx_polyfun A -> mx_polyfun (fun x => mxpow_deriv (A x) E k).
Proof.
move=> hA; apply: mx_polyfun_sum => r.
apply: mx_polyfun_mul; last exact: mx_polyfun_exp.
by apply: mx_polyfun_mul; [exact: mx_polyfun_exp | exact: mx_polyfun_cst].
Qed.

(* Integrals of functions of polynomial growth against gauss m. *)
Lemma integrable_polyfun (F : 'rV[R]_m -> R) : polyfun F ->
  (gauss m).-integrable [set: 'rV[R]_m] (EFin \o F).
Proof.
move=> [cF [C [k hC]]].
exact: integrable_gauss_poly (continuous_measurable_mx cF) hC.
Qed.

Lemma Rintegral_polyfunD (F G : 'rV[R]_m -> R) : polyfun F -> polyfun G ->
  \int[gauss m]_x (F x + G x) = \int[gauss m]_x F x + \int[gauss m]_x G x.
Proof. by move=> hF hG; rewrite RintegralD //; exact: integrable_polyfun. Qed.

Lemma Rintegral_polyfunZ c (F : 'rV[R]_m -> R) : polyfun F ->
  \int[gauss m]_x (c * F x) = c * \int[gauss m]_x F x.
Proof. by move=> hF; rewrite RintegralZl //; exact: integrable_polyfun. Qed.

Lemma Rintegral_polyfun_sum (I : Type) (s : seq I) (F : I -> 'rV[R]_m -> R) :
  (forall i, polyfun (F i)) ->
  \int[gauss m]_x (\sum_(i <- s) F i x) = \sum_(i <- s) \int[gauss m]_x F i x.
Proof. by move=> hF; apply: Rintegral_sum => // i; exact: integrable_polyfun. Qed.

(* Gaussian integration by parts for functions of polynomial growth. *)
Lemma gauss_ibp_polyfun (p : 'I_m) (F dF : 'rV[R]_m -> R) :
  (forall x, is_derive x (delta_mx 0 p) F (dF x)) -> polyfun F -> polyfun dF ->
  \int[gauss m]_x (x 0 p * F x) = \int[gauss m]_x dF x.
Proof.
move=> hd hF hdF; have [C [k [h1 h2]]] := polyfun_bound2 hF hdF.
by rewrite /Rintegral (gauss_ibp hd hF.1 hdF.1 h1 h2).
Qed.

End mxpow_polyfun.

Section goe.
Context {R : realType}.

(* The GOE matrix (A + A^T) / sqrt (2 d) of a row vector of size d * d. *)
Definition goe_mx d (a : 'rV[R]_(d * d)) : 'M[R]_d :=
  (Num.sqrt (2 * d%:R))^-1 *: (vec_mx a + (vec_mx a)^T).

Lemma goe_mx_sym d (a : 'rV[R]_(d * d)) : (goe_mx a)^T = goe_mx a.
Proof. by rewrite /goe_mx linearZ /= linearD /= trmxK addrC. Qed.

Lemma goe_mxE d (a : 'rV[R]_(d * d)) i j :
  goe_mx a i j =
  (Num.sqrt (2 * d%:R))^-1 * (a 0 (mxvec_index i j) + a 0 (mxvec_index j i)).
Proof. by rewrite /goe_mx !mxE. Qed.

Lemma goe_mxD d (a b : 'rV[R]_(d * d)) : goe_mx (a + b) = goe_mx a + goe_mx b.
Proof. by apply/matrixP => i j; rewrite [RHS]mxE !goe_mxE !mxE addrACA mulrDr. Qed.

Lemma goe_mxZ d (h : R) (a : 'rV[R]_(d * d)) : goe_mx (h *: a) = h *: goe_mx a.
Proof. by apply/matrixP => i j; rewrite [RHS]mxE !goe_mxE !mxE -mulrDr mulrCA. Qed.

Lemma goe_mx_delta d (i j : 'I_d) :
  goe_mx (delta_mx 0 (mxvec_index i j)) =
  (Num.sqrt (2 * d%:R))^-1 *: (delta_mx i j + delta_mx j i).
Proof. by rewrite /goe_mx vec_mx_delta trmx_delta. Qed.

Lemma mx_polyfun_goe d : mx_polyfun (@goe_mx d).
Proof.
move=> i j; under eq_fun do rewrite goe_mxE.
by apply: polyfunM; [exact: polyfun_cst | apply: polyfunD; exact: polyfun_coord].
Qed.

Lemma is_derive_goe_pow d k (i j : 'I_d) (x v : 'rV[R]_(d * d)) :
  is_derive x v (fun a => (goe_mx a ^+ k) i j)
    (mxpow_deriv (goe_mx x) (goe_mx v) k i j).
Proof.
apply: (is_derive_transfer (G := fun M : 'M[R]_d => (M ^+ k) i j)
  (b := goe_mx x) (w := goe_mx v)); last exact: is_derive_mxpow.
by move=> h; rewrite goe_mxD goe_mxZ.
Qed.

End goe.

Section gauss_frobenius_mean.
Context {R : realType} (n : nat).

(* E |g| <= sqrt n for g of law gauss n, by 2 |g| sqrt n <= |g|^2 + n. *)
Lemma gauss_frobenius_mean :
  \int[@gauss R n]_g frobenius g <= Num.sqrt n%:R.
Proof.
have [n0|n0] := posnP n.
  subst n; rewrite sqrtr0.
  have -> : \int[@gauss R 0]_g frobenius g = \int[@gauss R 0]_g (0 : R).
    apply: eq_Rintegral => g _.
    by rewrite (_ : g = 0) ?frobenius0 //; apply/rowP => -[].
  by rewrite Rintegral_cst // mul0r.
set t := Num.sqrt n%:R.
have t0 : 0 < t by rewrite sqrtr_gt0 ltr0n.
have tt : t * t = n%:R by rewrite -expr2 sqr_sqrtr ?ler0n.
have pq : polyfun (fun g : 'rV[R]_n => mxdot g g).
  have -> : (fun g : 'rV[R]_n => mxdot g g) = (fun g => \sum_j g 0 j * g 0 j).
    by apply/funext => g; rewrite /mxdot big_ord1.
  by apply: polyfun_sum => j; apply: polyfunM; exact: polyfun_coord.
have E2 : \int[@gauss R n]_g mxdot g g = n%:R.
  by rewrite /Rintegral integral_gauss_mxdot_self.
(* |g| <= t / 2 + |g|^2 / (2 t), since (|g| - t)^2 >= 0 *)
have hp (g : 'rV[R]_n) : frobenius g <= t / 2 + (2 * t)^-1 * mxdot g g.
  rewrite -frobenius_sqr; set f := frobenius g.
  have e : t / 2 + (2 * t)^-1 * f ^+ 2 = (t * t + f ^+ 2) / (2 * t).
    rewrite [RHS]mulrDl [f ^+ 2 / _]mulrC; congr (_ + _).
    by rewrite invfM [2^-1 * _]mulrC mulrA mulfK ?gt_eqF.
  have h := sqr_ge0 (f - t).
  by rewrite e ler_pdivlMr ?mulr_gt0 //; rewrite sqrrB in h; nra.
have pc : polyfun (fun g : 'rV[R]_n => t / 2 + (2 * t)^-1 * mxdot g g).
  apply: polyfunD; first exact: polyfun_cst.
  by apply: polyfunM; [exact: polyfun_cst | exact: pq].
apply: le_trans (_ : \int[@gauss R n]_g (t / 2 + (2 * t)^-1 * mxdot g g) <= _).
  apply: le_Rintegral => //.
  - exact: gauss_smoothing.integrable_gauss_frobenius.
  - exact: integrable_polyfun.
rewrite Rintegral_polyfunD; first exact: polyfun_cst.
  by apply: polyfunM; [exact: polyfun_cst | exact: pq].
rewrite [X in _ + X]Rintegral_polyfunZ // E2 Rintegral_cst //.
rewrite -[X in fine X]/(@gauss R n setT) probability_setT /= mulr1.
rewrite -tt invfM -mulrA [t^-1 * (t * t)]mulrA mulVf ?gt_eqF // mul1r.
lra.
Qed.

End gauss_frobenius_mean.

Section goe_opnorm.
Context {R : realType} (d : nat).
Local Notation gauss := (@gauss R).

Lemma goe_mxB (a b : 'rV[R]_(d * d)) : goe_mx (a - b) = goe_mx a - goe_mx b.
Proof. by rewrite goe_mxD -scaleN1r goe_mxZ scaleN1r. Qed.

Lemma two_div_sqrt : 2 * (Num.sqrt (2 * d%:R))^-1 = Num.sqrt (2 / d%:R) :> R.
Proof.
have [->|d0] := posnP d; first by rewrite mulr0 sqrtr0 !invr0 mulr0 sqrtr0.
have p0 : 0 < 2 * d%:R :> R by rewrite mulr_gt0 // ltr0n.
have s0 : 0 < Num.sqrt (2 * d%:R) :> R by rewrite sqrtr_gt0.
apply: (mulIf (_ : Num.sqrt (2 * d%:R) != 0)); first by rewrite gt_eqF.
rewrite divfK ?gt_eqF // -sqrtrM ?divr_ge0 ?ler0n //.
rewrite mulrACA mulVf ?pnatr_eq0 -?lt0n // mulr1.
by rewrite -expr2 sqrtr_sqr ger0_norm.
Qed.

Lemma frobenius_goe_mx (a : 'rV[R]_(d * d)) :
  frobenius (goe_mx a) <= Num.sqrt (2 / d%:R) * frobenius a.
Proof.
rewrite /goe_mx frobeniusZ ger0_norm ?invr_ge0 ?sqrtr_ge0 // -two_div_sqrt.
rewrite [2 / _]mulrC -mulrA; apply: ler_wpM2l.
  by rewrite invr_ge0 sqrtr_ge0.
apply: le_trans (frobeniusD _ _) _.
by rewrite frobenius_trmx frobenius_vec_mx mulr_natl mulr2n.
Qed.

Lemma goe_opnorm_lipschitz (a b : 'rV[R]_(d * d)) :
  `|opnorm (goe_mx a) - opnorm (goe_mx b)| <=
  Num.sqrt (2 / d%:R) * frobenius (a - b).
Proof.
apply: le_trans (opnorm_lipschitz _ _) _.
by rewrite -goe_mxB frobenius_goe_mx.
Qed.

Lemma integrable_goe_opnorm :
  (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a => opnorm (goe_mx a))).
Proof. exact: integrable_gauss_lipschitz goe_opnorm_lipschitz. Qed.

Lemma opnorm_goe_mx (a : 'rV[R]_(d * d)) :
  opnorm (goe_mx a) <= Num.sqrt (2 / d%:R) * opnorm (vec_mx a : 'M[R]_(d, d)).
Proof.
rewrite /goe_mx opnormZ ger0_norm ?invr_ge0 ?sqrtr_ge0 // -two_div_sqrt.
rewrite [2 / _]mulrC -mulrA; apply: ler_wpM2l.
  by rewrite invr_ge0 sqrtr_ge0.
apply: le_trans (opnormD _ _) _.
by rewrite opnorm_trmx mulr_natl mulr2n.
Qed.

(* E opnorm W <= 2 sqrt 2: opnorm W <= sqrt (2 / d) opnorm A, and E opnorm A
   <= E |g| + E |h| <= 2 sqrt d by Gordon's inequality (gauss_opnorm_mean). *)
Lemma goe_opnorm_mean : (0 < d)%N ->
  \int[gauss (d * d)]_a opnorm (goe_mx a) <= 2 * Num.sqrt 2.
Proof.
move=> d0.
have iA := @integrable_gauss_opnorm R d d.
have iZ : (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a => Num.sqrt (2 / d%:R) * opnorm (vec_mx a : 'M[R]_(d, d)))).
  rewrite (_ : _ \o _ = (fun a => (Num.sqrt (2 / d%:R))%:E *
    (opnorm (vec_mx a : 'M[R]_(d, d)))%:E)%E); first by apply/funext => a.
  exact: integrableZl.
apply: le_trans (_ : \int[gauss (d * d)]_a
    (Num.sqrt (2 / d%:R) * opnorm (vec_mx a : 'M[R]_(d, d))) <= _).
  apply: le_Rintegral => //; first exact: integrable_goe_opnorm.
  by move=> a _; exact: opnorm_goe_mx.
rewrite RintegralZl //.
apply: le_trans (_ : Num.sqrt (2 / d%:R) * (Num.sqrt d%:R + Num.sqrt d%:R) <= _).
  apply: ler_wpM2l; first exact: sqrtr_ge0.
  apply: le_trans (gauss_opnorm_mean d0 d0) _.
  by apply: lerD; exact: gauss_frobenius_mean.
rewrite -mulr2n mulrnAr -sqrtrM ?divr_ge0 ?ler0n //.
by rewrite divfK ?pnatr_eq0 -?lt0n // -mulr_natl.
Qed.

Lemma integrable_goe_opnorm_expR (s : R) :
  (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a => expR (s * opnorm (goe_mx a)))).
Proof.
set EF := \int[gauss (d * d)]_a opnorm (goe_mx a).
have iC := integrable_gauss_concentration goe_opnorm_lipschitz s.
rewrite (_ : _ \o _ = (fun a => (expR (s * EF))%:E *
    (expR (s * (opnorm (goe_mx a) - EF)))%:E)%E).
  by apply/funext => a; rewrite /= -EFinM -expRD mulrBr addrC subrK.
exact: integrableZl.
Qed.

(* E exp (s opnorm W) <= exp (2 sqrt 2 s + s^2 / d) for s >= 0: Gaussian
   concentration of the sqrt (2 / d)-Lipschitz function opnorm W around its
   mean, which is at most 2 sqrt 2. *)
Lemma goe_opnorm_mgf (s : R) : (0 < d)%N -> 0 <= s ->
  \int[gauss (d * d)]_a expR (s * opnorm (goe_mx a)) <=
  expR (2 * Num.sqrt 2 * s + s ^+ 2 / d%:R).
Proof.
move=> d0 s0.
set EF := \int[gauss (d * d)]_a opnorm (goe_mx a).
have hc := gauss_concentration goe_opnorm_lipschitz s.
have iC := integrable_gauss_concentration goe_opnorm_lipschitz s.
have fin := integrable_fin_num measurableT iC.
rewrite -(fineK fin) lee_fin in hc.
have -> : \int[gauss (d * d)]_a expR (s * opnorm (goe_mx a)) =
    expR (s * EF) * \int[gauss (d * d)]_a expR (s * (opnorm (goe_mx a) - EF)).
  rewrite -RintegralZl //; apply: eq_Rintegral => a _.
  by rewrite -expRD mulrBr addrC subrK.
rewrite expRD; apply: ler_pM.
- exact: expR_ge0.
- by apply: Rintegral_ge0 => a _; exact: expR_ge0.
- rewrite ler_expR mulrC; apply: ler_wpM2r => //; exact: goe_opnorm_mean.
apply: le_trans hc _; rewrite sqr_sqrtr ?divr_ge0 ?ler0n //.
rewrite le_eqVlt; apply/orP; left; apply/eqP; congr expR.
have dn : d%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
by field.
Qed.

End goe_opnorm.

Section goe_moments.
Context {R : realType}.
Local Notation gauss := (@gauss R).

(* The Schwinger-Dyson equation for the moments of the GOE: E tr W^(k+1) =
   (k E tr W^(k-1) + \sum_(r < k) E[tr W^r tr W^(k-1-r)]) / d. *)
Theorem goe_schwinger_dyson d k :
  \int[gauss (d * d)]_a \tr (goe_mx a ^+ k.+1) =
  d%:R^-1 * (k%:R * \int[gauss (d * d)]_a \tr (goe_mx a ^+ k.-1) +
    \sum_(r < k) \int[gauss (d * d)]_a
      (\tr (goe_mx a ^+ r) * \tr (goe_mx a ^+ (k.-1 - r)))).
Proof.
set c : R := (Num.sqrt (2 * d%:R))^-1.
have hW := @mx_polyfun_goe R d.
have hWk r := mx_polyfun_exp r hW.
have sym (a : 'rV[R]_(d * d)) r : (goe_mx a ^+ r)^T = goe_mx a ^+ r.
  by rewrite trmx_exp goe_mx_sym.
(* tr W^(k+1) = 2 c \sum_(i, j) a_ij (W^k)_ji *)
have htr (a : 'rV[R]_(d * d)) : \tr (goe_mx a ^+ k.+1) =
    2 * c * \sum_i \sum_j (a 0 (mxvec_index i j) * (goe_mx a ^+ k) j i).
  rewrite exprS -mulmxE /mxtrace.
  have e2 : \sum_i \sum_j a 0 (mxvec_index j i) * (goe_mx a ^+ k) j i =
      \sum_i \sum_j a 0 (mxvec_index i j) * (goe_mx a ^+ k) j i.
    rewrite exchange_big; apply: eq_bigr => i _; apply: eq_bigr => j _.
    by rewrite -{1}(sym a k) mxE.
  have cS (S : R) : 2 * c * S = c * S + c * S.
    by rewrite -mulrA mulr_natl mulr2n.
  rewrite cS -[X in _ = _ + c * X]e2 !mulr_sumr -big_split.
  apply: eq_bigr => i _; rewrite mxE !mulr_sumr -big_split.
  apply: eq_bigr => j _.
  by rewrite goe_mxE -/c /= !mulrA -mulrDl -mulrDr.
have pD (i j : 'I_d) : polyfun (fun a : 'rV[R]_(d * d) =>
    mxpow_deriv (goe_mx a) (delta_mx i j + delta_mx j i) k j i).
  exact: mx_polyfun_mxpow_deriv.
have pT r : polyfun (fun a : 'rV[R]_(d * d) => \tr (goe_mx a ^+ r)).
  exact: polyfun_trace.
have pF (i j : 'I_d) : polyfun (fun a : 'rV[R]_(d * d) =>
    a 0 (mxvec_index i j) * (goe_mx a ^+ k) j i).
  by apply: polyfunM; [exact: polyfun_coord | exact: hWk].
(* integration by parts in a_ij: E[a_ij (W^k)_ji] = c E[D_ij] *)
have hibp (i j : 'I_d) :
    \int[gauss (d * d)]_a (a 0 (mxvec_index i j) * (goe_mx a ^+ k) j i) =
    c * \int[gauss (d * d)]_a
      (mxpow_deriv (goe_mx a) (delta_mx i j + delta_mx j i) k j i).
  have hd (x : 'rV[R]_(d * d)) := is_derive_goe_pow k j i x
    (delta_mx 0 (mxvec_index i j)).
  rewrite (gauss_ibp_polyfun hd (hWk k j i)
    (mx_polyfun_mxpow_deriv (goe_mx (delta_mx 0 (mxvec_index i j))) k hW j i)).
  rewrite -Rintegral_polyfunZ; first exact: pD.
  by apply: eq_Rintegral => a _; rewrite goe_mx_delta mxpow_derivZ mxE.
have hsum : \sum_i \int[gauss (d * d)]_x
      \sum_j x 0 (mxvec_index i j) * (goe_mx x ^+ k) j i =
    c * \int[gauss (d * d)]_a
      \sum_i \sum_j mxpow_deriv (goe_mx a) (delta_mx i j + delta_mx j i) k j i.
  rewrite Rintegral_polyfun_sum.
    by move=> i; apply: polyfun_sum => j; exact: pD.
  rewrite mulr_sumr; apply: eq_bigr => i _.
  rewrite Rintegral_polyfun_sum; first by move=> j; exact: pD.
  rewrite Rintegral_polyfun_sum; first by move=> j; exact: pF.
  by rewrite mulr_sumr; apply: eq_bigr => j _; exact: hibp.
under eq_Rintegral do rewrite htr.
rewrite Rintegral_polyfunZ.
  by apply: polyfun_sum => i; apply: polyfun_sum => j; exact: pF.
rewrite Rintegral_polyfun_sum.
  by move=> i; apply: polyfun_sum => j; exact: pF.
rewrite hsum.
under eq_Rintegral do rewrite mxpow_deriv_trace ?goe_mx_sym //.
rewrite Rintegral_polyfunD.
- by apply: polyfunM; [exact: polyfun_cst | exact: pT].
- by apply: polyfun_sum => r; apply: polyfunM; exact: pT.
rewrite Rintegral_polyfunZ; first exact: pT.
rewrite [X in _ + X]Rintegral_polyfun_sum.
  by move=> r; apply: polyfunM; exact: pT.
have cc : 2 * c * c = d%:R^-1.
  rewrite /c -mulrA -invfM -expr2 sqr_sqrtr; first by rewrite mulr_ge0 // ler0n.
  by rewrite invfM mulrA mulfV ?mul1r // pnatr_eq0.
by rewrite mulrA cc.
Qed.

End goe_moments.

