From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype sequences derive exp.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss gauss_ibp.
From GaussianAnalysis.gaussian Require Import gauss_interpolation.
From GaussianAnalysis.matrix Require Import euclidean opnorm real_spectral.
From GaussianAnalysis.matrix Require Import von_neumann.
From GaussianAnalysis.comparison Require Import gauss_smoothing gauss_concentration.
From GaussianAnalysis.comparison Require Import escape.
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
(* - goe_tr_var: with t_k = goe_tr k = tr W^k / d, for every u >= 0,          *)
(*   Var t_k <= 2 L^2 + 8 (2k)! exp (2 sqrt 2 (2u + 1) + (2u + 1)^2 / d - 6u) *)
(*   with L = sqrt 2 k 3^(k-1) / d. The statistic goe_clip k of the           *)
(*   eigenvalues clipped to [-3, 3] is L-Lipschitz in a                       *)
(*   (goe_clip_lipschitz, by the Hoffman-Wielandt inequality), so its         *)
(*   variance is at most L^2 (gauss_poincare_lipschitz), and |t_k - goe_clip  *)
(*   k| <= 2 opnorm W^k exp (u (opnorm W - 3)) (goe_clip_err). With u = sqrt  *)
(*   d, Var t_k tends to 0: goe_tr_var_small, Var t_k <= eps for every large  *)
(*   d.                                                                       *)
(* - goe_tr_sd: E t_(k+2) = (k + 1) / d E t_k + \sum_(r <= k) E[t_r t_(k-r)], *)
(*   and Rintegral_cov_le: |Cov (X, Y)| <= (Var X + Var Y) / 2.               *)
(*                                                                            *)
(* Planned results (phase 5, stage 2; names come with the proofs):            *)
(*                                                                            *)
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

Lemma polyfunB F G : polyfun F -> polyfun G -> polyfun (fun x => F x - G x).
Proof.
move=> hF hG; under eq_fun do rewrite -mulN1r.
by apply: polyfunD => //; apply: polyfunM => //; exact: polyfun_cst.
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

(* The variance is the least mean square deviation. *)
Lemma Rintegral_var_le (X : 'rV[R]_m -> R) (c : R) : polyfun X ->
  \int[gauss m]_x (X x - \int[gauss m]_y X y) ^+ 2 <=
  \int[gauss m]_x (X x - c) ^+ 2.
Proof.
move=> hX; set e := \int[gauss m]_y X y.
have pc (r : R) : polyfun (fun _ : 'rV[R]_m => r) := polyfun_cst r.
have pXe : polyfun (fun x => X x - e).
  by apply: polyfunD => //; exact: pc.
have -> : \int[gauss m]_x (X x - c) ^+ 2 = \int[gauss m]_x
    ((X x - e) ^+ 2 + (2 * (e - c) * (X x - e) + (e - c) ^+ 2)).
  by apply: eq_Rintegral => x _; rewrite -[X x - c](subrK e) -addrA; ring.
have pS : polyfun (fun x => (X x - e) ^+ 2).
  by under eq_fun do rewrite expr2; exact: polyfunM.
have p2 : polyfun (fun x => 2 * (e - c) * (X x - e)).
  by apply: polyfunM; [exact: pc | exact: pXe].
have i0 : \int[gauss m]_x (X x - e) = 0.
  rewrite Rintegral_polyfunD; [exact: hX | exact: polyfun_cst |].
  rewrite Rintegral_cst // -[X in fine X]/(@gauss R m setT) probability_setT.
  by rewrite /= mulr1 subrr.
rewrite Rintegral_polyfunD; first exact: pS.
  by apply: polyfunD => //; exact: polyfun_cst.
rewrite Rintegral_polyfunD; [exact: p2 | exact: polyfun_cst |].
rewrite Rintegral_polyfunZ; first exact: pXe.
rewrite i0 mulr0 add0r Rintegral_cst //.
rewrite -[X in fine X]/(@gauss R m setT) probability_setT /= mulr1.
by rewrite lerDl sqr_ge0.
Qed.

(* |Cov (X, Y)| <= (Var X + Var Y) / 2. *)
Lemma Rintegral_cov_le (X Y : 'rV[R]_m -> R) : polyfun X -> polyfun Y ->
  `|\int[gauss m]_x (X x * Y x) -
    \int[gauss m]_x X x * \int[gauss m]_x Y x| <=
  (\int[gauss m]_x (X x - \int[gauss m]_y X y) ^+ 2 +
   \int[gauss m]_x (Y x - \int[gauss m]_y Y y) ^+ 2) / 2.
Proof.
move=> hX hY; set a := \int[gauss m]_y X y; set b := \int[gauss m]_y Y y.
have pXa : polyfun (fun x => X x - a) by apply: polyfunB => //; exact: polyfun_cst.
have pYb : polyfun (fun x => Y x - b) by apply: polyfunB => //; exact: polyfun_cst.
have pP : polyfun (fun x => (X x - a) * (Y x - b)) by exact: polyfunM.
have iXa : \int[gauss m]_x (X x - a) = 0.
  rewrite Rintegral_polyfunD; [exact: hX | exact: polyfun_cst |].
  rewrite Rintegral_cst // -[X in fine X]/(@gauss R m setT) probability_setT.
  by rewrite /= mulr1 subrr.
(* Cov (X, Y) = E[(X - E X) (Y - E Y)] *)
have E1 : \int[gauss m]_x (X x * Y x) - a * b =
    \int[gauss m]_x ((X x - a) * (Y x - b)).
  have -> : \int[gauss m]_x (X x * Y x) =
      \int[gauss m]_x ((X x - a) * (Y x - b) + (b * (X x - a) + a * Y x)).
    by apply: eq_Rintegral => x _; ring.
  rewrite Rintegral_polyfunD //.
    by apply: polyfunD; apply: polyfunM => //; exact: polyfun_cst.
  rewrite Rintegral_polyfunD //; [by apply: polyfunM => //; exact: polyfun_cst |
    by apply: polyfunM => //; exact: polyfun_cst |].
  by rewrite !Rintegral_polyfunZ // iXa mulr0 add0r -/b addrK.
have pSq (F : 'rV[R]_m -> R) : polyfun F -> polyfun (fun x => F x ^+ 2).
  by move=> hF; under eq_fun do rewrite expr2; exact: polyfunM.
have pN : polyfun (fun x => `|(X x - a) * (Y x - b)|).
  split.
    by move=> x; apply: (continuous_comp (pP.1 x)); exact: norm_continuous.
  by have [_ [C [k hC]]] := pP; exists C, k => x; rewrite normr_id; exact: hC.
have pS2 : polyfun (fun x => 2^-1 * ((X x - a) ^+ 2 + (Y x - b) ^+ 2)).
  by apply: polyfunM; [exact: polyfun_cst | apply: polyfunD; exact: pSq].
(* |p q| <= (p^2 + q^2) / 2 *)
rewrite E1; apply: le_trans (le_normr_Rintegral _ _) _ => //.
  exact: integrable_polyfun.
apply: le_trans (_ : \int[gauss m]_x
    (2^-1 * ((X x - a) ^+ 2 + (Y x - b) ^+ 2)) <= _).
  apply: le_Rintegral => //; [exact: integrable_polyfun |
    exact: integrable_polyfun |].
  move=> x _; rewrite normrM; have h := sqr_ge0 (`|X x - a| - `|Y x - b|).
  by rewrite sqrrB !real_normK ?num_real // in h; nra.
rewrite Rintegral_polyfunZ; first by apply: polyfunD; exact: pSq.
by rewrite Rintegral_polyfunD; [exact: pSq | exact: pSq | rewrite mulrC].
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

Section clip_pow.
Context {R : realType}.

(* |x^k - y^k| <= k M^(k-1) |x - y| for |x|, |y| <= M. *)
Lemma exprB_le (M x y : R) k : `|x| <= M -> `|y| <= M ->
  `|x ^+ k - y ^+ k| <= k%:R * M ^+ k.-1 * `|x - y|.
Proof.
move=> xM yM; have M0 : 0 <= M := le_trans (normr_ge0 x) xM.
rewrite subrXX normrM mulrC; apply: ler_wpM2r; first exact: normr_ge0.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_(i < k) M ^+ k.-1 <= _).
  apply: ler_sum => i _; rewrite normrM !normrX.
  have ik : (i <= k.-1)%N by rewrite -ltnS prednK // (leq_ltn_trans _ (ltn_ord i)).
  rewrite -[in M ^+ k.-1](subnK ik) exprD.
  by apply: ler_pM; rewrite ?exprn_ge0 ?normr_ge0 // lerXn2r // nnegrE.
by rewrite sumr_const card_ord mulr_natl.
Qed.

Lemma clip_pow_lipschitz (c x y : R) k : 0 <= c ->
  `|clip c x ^+ k - clip c y ^+ k| <= k%:R * c ^+ k.-1 * `|x - y|.
Proof.
move=> c0; apply: le_trans (exprB_le _ (clip_bound _ c0) (clip_bound _ c0)) _.
by apply: ler_wpM2l; [rewrite mulr_ge0 ?exprn_ge0 | exact: clip_lipschitz].
Qed.

(* The error of clipping at c a point x with |x| <= w, weighted so as to
   vanish when w <= c. *)
Lemma clip_pow_err (c w x u : R) k : 0 <= c -> `|x| <= w -> 0 <= u ->
  `|x ^+ k - clip c x ^+ k| <= 2 * w ^+ k * expR (u * (w - c)).
Proof.
move=> c0 xw u0; have w0 : 0 <= w := le_trans (normr_ge0 x) xw.
have [xc|cx] := leP `|x| c.
  rewrite clip_id // subrr normr0.
  by rewrite mulr_ge0 ?expR_ge0 // mulr_ge0 ?exprn_ge0.
have cw : c <= w by apply: le_trans (ltW cx) xw.
apply: le_trans (ler_normB _ _) _.
apply: le_trans (_ : w ^+ k + w ^+ k <= _).
  apply: lerD; rewrite normrX lerXn2r // ?nnegrE //.
  by apply: le_trans (clip_bound _ c0) cw.
rewrite -mulr2n -mulr_natl -[X in X <= _]mulr1; apply: ler_wpM2l.
  by rewrite mulr_ge0 ?exprn_ge0.
by rewrite -expR0 ler_expR mulr_ge0 // subr_ge0.
Qed.

Lemma exprn_le_fact_expR (x : R) j : 0 <= x -> x ^+ j <= j`!%:R * expR x.
Proof.
move=> x0; case: j => [|j]; first by rewrite expr0 fact0 mul1r -expR0 ler_expR.
have h := expR_ge1Dxn j x0.
have f0 : 0 < (j.+1)`!%:R :> R by rewrite ltr0n fact_gt0.
rewrite -ler_pdivrMl // mulrC.
by apply: le_trans h; rewrite lerDr.
Qed.

End clip_pow.

Section spec_opnorm.
Context {R : realType} {n : nat}.

Lemma spec_le_opnorm (A : 'M[R]_n) i : A \is symmetricmx ->
  `|spec A 0 i| <= opnorm A.
Proof.
move=> As; have [P Po AE] := spec_decomposition As.
by rewrite (opnorm_spectral Po AE) (bigD1 i) //= le_max lexx.
Qed.

End spec_opnorm.

Section goe_stats.
Context {R : realType} (d : nat).
Local Notation gauss := (@gauss R).

Lemma goe_mx_symmetric (a : 'rV[R]_(d * d)) : goe_mx a \is symmetricmx.
Proof. by apply/symmetricmxP; exact: goe_mx_sym. Qed.

(* t_k = tr W^k / d and its version with the eigenvalues clipped to
   [-3, 3]. *)
Definition goe_tr k (a : 'rV[R]_(d * d)) : R := \tr (goe_mx a ^+ k) / d%:R.

Definition goe_clip k (a : 'rV[R]_(d * d)) : R :=
  (\sum_i clip 3 (spec (goe_mx a) 0 i) ^+ k) / d%:R.

Lemma goe_trE k a :
  goe_tr k a = (\sum_i spec (goe_mx a) 0 i ^+ k) / d%:R.
Proof. by rewrite /goe_tr sum_spec_exp // goe_mx_symmetric. Qed.

Lemma goe_clip_err k a (u : R) : 0 <= u ->
  `|goe_tr k a - goe_clip k a| <=
  2 * opnorm (goe_mx a) ^+ k * expR (u * (opnorm (goe_mx a) - 3)).
Proof.
move=> u0; rewrite goe_trE /goe_clip -mulrBl -sumrB normrM.
have [dz|dn] := eqVneq (d%:R : R) 0.
  rewrite dz invr0 normr0 mulr0.
  by rewrite mulr_ge0 ?expR_ge0 // mulr_ge0 ?exprn_ge0 ?opnorm_ge0.
have d0 : 0 < d%:R :> R by rewrite lt0r dn ler0n.
rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n // ler_pdivrMr //.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_(i < d) 2 * opnorm (goe_mx a) ^+ k *
    expR (u * (opnorm (goe_mx a) - 3)) <= _).
  apply: ler_sum => i _; apply: clip_pow_err => //.
  exact: spec_le_opnorm (goe_mx_symmetric a).
by rewrite sumr_const card_ord mulr_natr.
Qed.

Lemma goe_clip_lipschitz k (a b : 'rV[R]_(d * d)) :
  `|goe_clip k a - goe_clip k b| <=
  Num.sqrt 2 * k%:R * 3 ^+ k.-1 / d%:R * frobenius (a - b).
Proof.
rewrite /goe_clip -mulrBl normrM.
have [dz|dn] := eqVneq (d%:R : R) 0.
  by rewrite dz !invr0 normr0 !mulr0 mul0r.
have d0 : 0 < d%:R :> R by rewrite lt0r dn ler0n.
rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n //.
have L0 : 0 <= k%:R * 3 ^+ k.-1 :> R by rewrite mulr_ge0 ?exprn_ge0.
have h := spec_stat_lipschitz (L := k%:R * 3 ^+ k.-1) (goe_mx_symmetric a)
  (goe_mx_symmetric b) (fun x y => clip_pow_lipschitz x y k (ler0n _ 3)).
rewrite ler_pdivrMr //; apply: le_trans h _; rewrite -goe_mxB.
apply: le_trans (_ : k%:R * 3 ^+ k.-1 * Num.sqrt d%:R *
    (Num.sqrt (2 / d%:R) * frobenius (a - b)) <= _).
  by apply: ler_wpM2l; [rewrite mulr_ge0 ?sqrtr_ge0 | exact: frobenius_goe_mx].
rewrite le_eqVlt; apply/orP; left; apply/eqP.
have sd : Num.sqrt d%:R != 0 :> R by rewrite gt_eqF // sqrtr_gt0.
by rewrite sqrtrM ?ler0n // sqrtrV ?ler0n //; field.
Qed.

Lemma polyfun_goe_tr k : polyfun (goe_tr k).
Proof.
apply: polyfunM; last exact: polyfun_cst.
exact: polyfun_trace (mx_polyfun_exp k (@mx_polyfun_goe R d)).
Qed.

Lemma goe_clip_bound k a : `|goe_clip k a| <= 3 ^+ k.
Proof.
rewrite /goe_clip normrM.
have [dz|dn] := eqVneq (d%:R : R) 0.
  by rewrite dz invr0 normr0 mulr0 exprn_ge0.
have d0 : 0 < d%:R :> R by rewrite lt0r dn ler0n.
rewrite [`|_^-1|]ger0_norm ?invr_ge0 ?ler0n // ler_pdivrMr //.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_(i < d) (3 : R) ^+ k <= _).
  by apply: ler_sum => i _; rewrite normrX lerXn2r ?nnegrE ?clip_bound.
by rewrite sumr_const card_ord mulr_natr.
Qed.

Lemma polyfun_goe_clip k : polyfun (goe_clip k).
Proof.
split; first exact: lipschitz_frobenius_continuous (goe_clip_lipschitz k).
exists (3 ^+ k), 0%N => a; rewrite expr0.
apply: le_trans (goe_clip_bound k a) _.
by rewrite ler_peMr ?exprn_ge0 // lerDl.
Qed.

(* Var t_k <= 2 L^2 + 8 (2 k)! exp (2 sqrt 2 (2 u + 1) + (2 u + 1)^2 / d - 6 u)
   for every u >= 0, with L = sqrt 2 k 3^(k-1) / d the Lipschitz constant of
   the clipped statistic: Var t_k <= E (t_k - E S)^2 <= 2 E (t_k - S)^2
   + 2 Var S, Var S <= L^2 by the Gaussian Poincare inequality, and
   (t_k - S)^2 <= 4 (2 k)! exp ((2 u + 1) opnorm W - 6 u) by goe_clip_err. *)
Theorem goe_tr_var k (u : R) : (0 < d)%N -> 0 <= u ->
  \int[gauss (d * d)]_a (goe_tr k a - \int[gauss (d * d)]_b goe_tr k b) ^+ 2 <=
  2 * (Num.sqrt 2 * k%:R * 3 ^+ k.-1 / d%:R) ^+ 2 +
  8 * (k.*2)`!%:R *
    expR (2 * Num.sqrt 2 * (2 * u + 1) + (2 * u + 1) ^+ 2 / d%:R - 6 * u).
Proof.
move=> d0 u0.
set ES := \int[gauss (d * d)]_b goe_clip k b.
have pt := polyfun_goe_tr k; have pS := polyfun_goe_clip k.
have psq (F : 'rV[R]_(d * d) -> R) : polyfun F -> polyfun (fun a => F a ^+ 2).
  by move=> hF; under eq_fun do rewrite expr2; exact: polyfunM.
have ptS : polyfun (fun a => (goe_tr k a - goe_clip k a) ^+ 2).
  by apply: psq; exact: polyfunB.
have pSE : polyfun (fun a => (goe_clip k a - ES) ^+ 2).
  by apply: psq; apply: polyfunB => //; exact: polyfun_cst.
(* Var t_k <= E (t_k - E S)^2 <= 2 E (t_k - S)^2 + 2 E (S - E S)^2 *)
apply: le_trans (Rintegral_var_le ES pt) _.
apply: le_trans (_ : \int[gauss (d * d)]_a
    (2 * (goe_tr k a - goe_clip k a) ^+ 2 + 2 * (goe_clip k a - ES) ^+ 2) <= _).
  apply: le_Rintegral => //.
  - by apply: integrable_polyfun; apply: psq; apply: polyfunB => //;
      exact: polyfun_cst.
  - apply: integrable_polyfun; apply: polyfunD.
      by apply: polyfunM => //; exact: polyfun_cst.
    by apply: polyfunM => //; exact: polyfun_cst.
  move=> a _; set x := goe_tr k a - goe_clip k a; set y := goe_clip k a - ES.
  have -> : goe_tr k a - ES = x + y by rewrite /x /y addrA subrK.
  by clearbody x y; have h := sqr_ge0 (x - y); nra.
rewrite Rintegral_polyfunD; first by apply: polyfunM => //; exact: polyfun_cst.
  by apply: polyfunM => //; exact: polyfun_cst.
rewrite !Rintegral_polyfunZ // addrC; apply: lerD.
  apply: ler_wpM2l => //.
  exact: gauss_poincare_lipschitz (goe_clip_lipschitz k).
(* (t_k - S)^2 <= 4 (2 k)! exp (-6 u) exp ((2 u + 1) opnorm W) *)
have hpt a : (goe_tr k a - goe_clip k a) ^+ 2 <=
    4 * (k.*2)`!%:R * expR (- (6 * u)) * expR ((2 * u + 1) * opnorm (goe_mx a)).
  have w0 := opnorm_ge0 (goe_mx a); set w := opnorm (goe_mx a).
  have e := goe_clip_err k a u0; rewrite -/w in e.
  apply: le_trans (_ : (2 * w ^+ k * expR (u * (w - 3))) ^+ 2 <= _).
    rewrite -real_normK ?num_real // lerXn2r // ?nnegrE ?normr_ge0 //.
    by rewrite mulr_ge0 ?expR_ge0 // mulr_ge0 ?exprn_ge0.
  rewrite !exprMn -exprM -expRM_natr.
  have hw := exprn_le_fact_expR (k * 2) w0; rewrite mulnC mul2n in hw.
  apply: le_trans (_ : 2 ^+ 2 * ((k.*2)`!%:R * expR w) *
      expR (u * (w - 3) * 2%:R) <= _).
    apply: ler_wpM2r; first exact: expR_ge0.
    by apply: ler_wpM2l; [exact: exprn_ge0 | rewrite muln2; exact: hw].
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  rewrite (_ : 2 ^+ 2 = 4 :> R); first by rewrite expr2 -natrM.
  by rewrite -!mulrA -!expRD; congr (_ * (_ * expR _)); ring.
have iE : (gauss (d * d)).-integrable [set: 'rV[R]_(d * d)]
    (EFin \o (fun a => 4 * (k.*2)`!%:R * expR (- (6 * u)) *
      expR ((2 * u + 1) * opnorm (goe_mx a)))).
  rewrite (_ : _ \o _ = (fun a => (4 * (k.*2)`!%:R * expR (- (6 * u)))%:E *
    (expR ((2 * u + 1) * opnorm (goe_mx a)))%:E)%E); first by apply/funext => a.
  exact: integrableZl (integrable_goe_opnorm_expR _ _).
apply: le_trans (_ : 2 * \int[gauss (d * d)]_a (4 * (k.*2)`!%:R *
    expR (- (6 * u)) * expR ((2 * u + 1) * opnorm (goe_mx a))) <= _).
  by apply: ler_wpM2l => //; apply: le_Rintegral => //; exact: integrable_polyfun.
rewrite RintegralZl //; first exact: integrable_goe_opnorm_expR.
have u1 : 0 <= 2 * u + 1 by rewrite addr_ge0 // mulr_ge0.
have hm := @goe_opnorm_mgf R d (2 * u + 1) d0 u1.
apply: le_trans (_ : 2 * (4 * (k.*2)`!%:R * expR (- (6 * u)) *
    expR (2 * Num.sqrt 2 * (2 * u + 1) + (2 * u + 1) ^+ 2 / d%:R)) <= _).
  by apply: ler_wpM2l => //; apply: ler_wpM2l.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by rewrite [in RHS]expRD; ring.
Qed.

End goe_stats.

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

Section goe_tr_moments.
Context {R : realType} (d : nat).
Local Notation gauss := (@gauss R).

(* The Schwinger-Dyson equation for t_k = tr W^k / d:
   E t_(k+2) = (k + 1) / d E t_k + \sum_(r <= k) E[t_r t_(k-r)]. *)
Lemma goe_tr_sd k :
  \int[gauss (d * d)]_a goe_tr k.+2 a =
  k.+1%:R / d%:R * \int[gauss (d * d)]_a goe_tr k a +
  \sum_(r < k.+1) \int[gauss (d * d)]_a (goe_tr r a * goe_tr (k - r) a).
Proof.
have pT r := polyfun_trace (mx_polyfun_exp r (@mx_polyfun_goe R d)).
have e1 r : \int[gauss (d * d)]_a goe_tr r a =
    d%:R^-1 * \int[gauss (d * d)]_a \tr (goe_mx a ^+ r).
  by under eq_Rintegral do rewrite /goe_tr mulrC; rewrite Rintegral_polyfunZ.
have e2 r q : \int[gauss (d * d)]_a (goe_tr r a * goe_tr q a) =
    d%:R^-1 * d%:R^-1 *
      \int[gauss (d * d)]_a (\tr (goe_mx a ^+ r) * \tr (goe_mx a ^+ q)).
  rewrite -Rintegral_polyfunZ; first by apply: polyfunM.
  by apply: eq_Rintegral => a _; rewrite /goe_tr; ring.
rewrite e1 goe_schwinger_dyson e1 /=.
under [X in _ = _ + X]eq_bigr do rewrite e2.
by rewrite -mulr_sumr; ring.
Qed.

(* Var t_k tends to 0: for every eps > 0, Var t_k <= eps for every large d,
   by goe_tr_var with u chosen from eps and d >= (2 u + 1)^2. *)
Lemma goe_tr_var_small k (eps : R) : 0 < eps -> exists D : nat, forall d1,
  (D <= d1)%N ->
  \int[gauss (d1 * d1)]_a (goe_tr k a - \int[gauss (d1 * d1)]_b goe_tr k b) ^+ 2
    <= eps.
Proof.
move=> e0.
set K : R := 8 * (k.*2)`!%:R.
have K0 : 0 < K by rewrite mulr_gt0 // ltr0n fact_gt0.
set c : R := 6 - 4 * Num.sqrt 2.
have c0 : 0 < c.
  have s2 : Num.sqrt 2 < 3 / 2 :> R.
    rewrite -(@ltr_pXn2r _ 2) ?nnegrE ?sqrtr_ge0 ?divr_ge0 // sqr_sqrtr //.
    by rewrite expr_div_n; lra.
  by rewrite /c; lra.
set C1 : R := 2 * Num.sqrt 2 + 1.
have e2K : 0 < eps / (2 * K) by rewrite divr_gt0 // mulr_gt0.
set u : R := Num.max 0 ((C1 - ln (eps / (2 * K))) / c).
have u0 : 0 <= u by rewrite le_max lexx.
have hu : - (c * u) + C1 <= ln (eps / (2 * K)).
  have : (C1 - ln (eps / (2 * K))) / c <= u by rewrite le_max lexx orbT.
  by rewrite ler_pdivrMr // => h; rewrite mulrC; lra.
pose D1 := (archimedean.Num.truncn ((2 * u + 1) ^+ 2)).+1.
pose D2 := (archimedean.Num.truncn (8 * k%:R ^+ 2 * 9 ^+ k.-1 / eps)).+1.
exists (maxn D1 D2) => d1; rewrite geq_max => /andP[dD1 dD2].
have d0 : (0 < d1)%N by apply: leq_trans dD1.
have dR : 0 < d1%:R :> R by rewrite ltr0n.
have d1R : 1 <= d1%:R :> R by rewrite ler1n.
apply: le_trans (@goe_tr_var R d1 k u d0 u0) _.
rewrite (splitr eps); apply: lerD.
  (* 2 L^2 <= eps / 2 since d >= 8 k^2 9^(k-1) / eps *)
  have h2 : 8 * k%:R ^+ 2 * 9 ^+ k.-1 / eps < d1%:R.
    apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
    by rewrite ler_nat.
  rewrite ltr_pdivrMr // in h2.
  have e9 : (3 ^+ k.-1) ^+ 2 = 9 ^+ k.-1 :> R.
    by rewrite -exprM mulnC exprM expr2 -natrM.
  rewrite !exprMn sqr_sqrtr // e9.
  move: h2; set a := k%:R ^+ 2; set b := (9 : R) ^+ k.-1 => h2.
  have P0 : 0 <= a * b by rewrite mulr_ge0 ?exprn_ge0.
  have -> : 2 * (2 * a * b * d1%:R^-1 ^+ 2) = 4 * (a * b) * d1%:R^-1 ^+ 2.
    by ring.
  rewrite -mulrA in h2.
  move: (a * b) P0 h2 => P P0 h2.
  have y0 : 0 < d1%:R^-1 :> R by rewrite invr_gt0.
  have xy : d1%:R * d1%:R^-1 = 1 :> R by rewrite mulfV // gt_eqF.
  have y1 : d1%:R^-1 <= 1 :> R by rewrite invr_le1 // ?unitfE ?gt_eqF.
  move: (d1%:R : R) (d1%:R^-1 : R) dR d1R y0 xy y1 h2.
  move=> x y dR d1R y0 xy y1 h2.
  have h3 : 8 * P * y < x * eps * y by rewrite ltr_pM2r.
  rewrite [x * eps * y]mulrAC xy mul1r in h3.
  have h4 : P * y ^+ 2 <= P * y.
    apply: ler_wpM2l => //; rewrite expr2; apply: ler_piMr => //.
    exact: ltW.
  by lra.
(* K exp (...) <= K exp (- c u + C1) <= eps / 2 since d >= (2 u + 1)^2 *)
have h1 : (2 * u + 1) ^+ 2 < d1%:R.
  apply: lt_le_trans (archimedean.Num.Theory.truncnS_gt _) _.
  by rewrite ler_nat.
have hq : (2 * u + 1) ^+ 2 / d1%:R <= 1.
  by rewrite ler_pdivrMr // mul1r ltW.
rewrite -/K; apply: le_trans (_ : K * expR (ln (eps / (2 * K))) <= _).
  rewrite ler_pM2l // ler_expR; apply: le_trans hu.
  by rewrite /c /C1; lra.
rewrite lnK ?posrE // le_eqVlt; apply/orP; left; apply/eqP.
have Kn : K != 0 by rewrite gt_eqF.
by clearbody K; field.
Qed.

End goe_tr_moments.
