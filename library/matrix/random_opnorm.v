From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm nets.
From GaussianAnalysis.probability Require Import lindeberg symmetrization.
From GaussianAnalysis.probability Require Import subgaussian.

(**md**************************************************************************)
(* # The operator norm of a sum of independent random matrices                *)
(*                                                                            *)
(* A bound by nets and the moment generating function of sums of independent  *)
(* subexponential variables, used for Lemma 4.3 of Koehler and Sohn (arXiv    *)
(* 2608.27372, lines 4604-4615) in place of the matrix Bernstein inequality   *)
(* that the paper cites; it gives the bound without the logarithmic factor.   *)
(*                                                                            *)
(* Main results:                                                              *)
(* - Quadratic forms, mxdot_psd_le: for S symmetric positive semidefinite and *)
(*   any square A, |<A, S>| <= opnorm (sym_part A) tr S, where <., .> is the  *)
(*   Frobenius product mxdot; sym_part_form, mxdot_sym_part: v^T A v and      *)
(*   <A, S> only see the symmetric part.                                      *)
(* - Nets, unit_ball_quarter_net: the unit ball of 'cV[R]_n has a 1/4-net of  *)
(*   at most (18 e)^n of its points; opnorm_sym_part_net: for such a net V,   *)
(*   opnorm (sym_part A) <= 2 max_{v in V} |v^T A v|.                         *)
(* - Maximal inequality, subexponential_max_sum: for x of law                 *)
(*   tuple_prod mu n, a finite family of functions g_v, each centered and     *)
(*   subexponential with constant L under every mu i, and |a_i| <= 1,         *)
(*     E max_v |sum_i a_i g_v(x_i)| <= 8 L (sqrt (n Lam) + Lam)               *)
(*   with Lam = 1 + ln (1 + 2 N), N the size of the family. Proof: the moment *)
(*   generating function of each sum (subexponential_sum_mgf of               *)
(*   subgaussian.v), expR_bigmax_le (exp (l max_v |S_v|) is at most           *)
(*   1 + sum_v (exp (l S_v) + exp (- l S_v))), expectation_le_ln_mgf (if      *)
(*   E exp (l Z) <= B with ln B >= 1, then E Z <= ln B / l, from              *)
(*   e^y >= 1 + y), and a choice of l.                                        *)
(* - Random matrices, opnorm_sum_subexponential: for x of law                 *)
(*   tuple_prod mu n and Y : T -> 'M[R]_m whose quadratic forms v^T Y v       *)
(*   (|v| <= 1) are centered and subexponential with constant L under every   *)
(*   mu k, there are measurable functions N a such that, for all weights      *)
(*   with |a_k| <= 1, opnorm (sym_part (sum_k a_k Y(x_k))) <= N a x and       *)
(*     E N a <= 96 L (sqrt (n (m + 1)) + m + 1).                              *)
(*   N a x is 2 max_{v in V} |v^T (sum_k a_k Y(x_k)) v| on the net V;         *)
(*   net_log_le bounds the logarithm of the size of the net by 6 (m + 1).     *)
(*                                                                            *)
(* ```                                                                        *)
(*   sym_part A == (A + A^T) / 2, the symmetric part of a square matrix       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section quadratic_forms.
Context {R : realType}.

(* The symmetric part (A + A^T) / 2 of a square matrix. *)
Definition sym_part n (A : 'M[R]_n) : 'M[R]_n := 2^-1 *: (A + A^T).

Lemma sym_part_sym n (A : 'M[R]_n) : sym_part A \is symmetricmx.
Proof.
by apply/symmetricmxP; rewrite /sym_part linearZ /= linearD /= trmxK addrC.
Qed.

Lemma mxdot_trmx_form n (A : 'M[R]_n) (v : 'cV[R]_n) :
  mxdot v (A^T *m v) = mxdot v (A *m v).
Proof. by rewrite mxdotC mxdot_mulmxl trmxK. Qed.

Lemma sym_part_form n (A : 'M[R]_n) (v : 'cV[R]_n) :
  mxdot v (sym_part A *m v) = mxdot v (A *m v).
Proof.
rewrite /sym_part -scalemxAl mxdotZr mulmxDl mxdotDr mxdot_trmx_form.
by move: (mxdot v (A *m v)) => x; field.
Qed.

Lemma mxdot_sym_part n (A S : 'M[R]_n) : S \is symmetricmx ->
  mxdot (sym_part A) S = mxdot A S.
Proof.
move=> /symmetricmxP ST; rewrite /sym_part mxdotZl mxdotDl.
rewrite -[X in mxdot A^T X]ST mxdot_trmx.
by move: (mxdot A S) => x; field.
Qed.

(* The Frobenius product with a positive semidefinite matrix. *)
Lemma mxdot_psd_le n (A S : 'M[R]_n) : S \is symmetricmx ->
  (forall x : 'cV[R]_n, 0 <= mxdot x (S *m x)) ->
  `|mxdot A S| <= opnorm (sym_part A) * \tr S.
Proof.
move=> Ssym Spsd.
have [P Po [d SE]] := symmetric_spectral Ssym.
have d0 i : 0 <= d 0 i := (spectral_psd Po SE).1 Spsd i.
rewrite -(mxdot_sym_part A Ssym).
set B := sym_part A.
(* <B, S> = tr (P B P^T diag d) = sum_i (P B P^T)_ii d_i *)
have E : mxdot B S = \sum_i (P *m B *m P^T) i i * d 0 i.
  rewrite mxdot_trace; have /symmetricmxP -> := Ssym.
  rewrite SE mulmxA mulmxA mxtrace_mulC !mulmxA.
  by apply: eq_bigr => i _; rewrite mul_mx_diag mxE.
rewrite E (spectral_trace Po SE) mulr_sumr.
apply: le_trans (ler_norm_sum _ _ _) _; apply: ler_sum => i _.
rewrite normrM (ger0_norm (d0 i)); apply: ler_wpM2r; first exact: d0.
have e1 : frobenius (delta_mx i 0 : 'cV[R]_n) = 1.
  by rewrite /frobenius mxdot_delta mxE !eqxx sqrtr1.
have := mxdot_delta_opnorm (P *m B *m P^T) i i; rewrite e1 !mulr1.
by rewrite opnorm_orthogonalmxr ?trmx_orthogonal// opnorm_orthogonalmxl.
Qed.

(* On a net of the unit ball, the quadratic forms bound the operator norm
   of the symmetric part. *)
Lemma opnorm_sym_part_net n (A : 'M[R]_n) (V : seq 'cV[R]_n) :
  is_net (@unit_ball R n) V (4^-1) -> (forall v, v \in V -> frobenius v <= 1) ->
  opnorm (sym_part A) <= 2 * \big[Num.max/0]_(v <- V) `|mxdot v (A *m v)|.
Proof.
move=> VN V1.
set b := \big[Num.max/0]_(v <- V) `|mxdot v (A *m v)|.
have := @opnorm_net_sym R n (sym_part A) V (4^-1) b (sym_part_sym A).
have e : b / (1 - 2 / 4) = 2 * b :> R by field.
rewrite e; apply => //.
  by rewrite ltr_pdivrMr// mul1r ltr_nat.
move=> v vV; rewrite sym_part_form.
rewrite /b; move: vV; elim: (V) => //= w V' IH; rewrite inE big_cons.
by case/orP => [/eqP->|vV']; rewrite le_max ?lexx// IH ?orbT.
Qed.

Lemma unit_ball_quarter_net n : exists V : seq 'cV[R]_n,
  [/\ is_net (@unit_ball R n) V (4^-1),
    (forall v, v \in V -> frobenius v <= 1) &
    (size V)%:R <= (18 * expR 1) ^+ n :> R].
Proof.
have q0 : 0 < 4^-1 :> R by rewrite invr_gt0 ltr0n.
have [V [VS VN Vs]] := @net_exists R n (@unit_ball R n) 1 (4^-1) ler01 q0
  (fun x x1 => x1).
exists V; split => //.
have e : 2 * expR 1 * (1 + 2 * 1 / 4^-1) = 18 * expR 1 :> R.
  by rewrite invrK; move: (expR 1 : R) => x; ring.
by rewrite -e.
Qed.

End quadratic_forms.

Section maximal_inequality.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* Jensen's inequality for exp, from e^y >= 1 + y: if E e^(l Z) <= B with
   ln B >= 1, then l E Z <= ln B. *)
Lemma expectation_le_ln_mgf (P : probability T R) (Z : T -> R) (l B : R) :
  measurable_fun [set: T] Z -> (forall x, 0 <= Z x)%R -> (0 < l)%R ->
  (1 <= ln B)%R ->
  \int[P]_x (expR (l * Z x))%:E <= B%:E ->
  \int[P]_x (Z x)%:E <= (ln B / l)%:E.
Proof.
move=> mZ Z0 l0 c1 hB.
set c := ln B.
have B0 : (0 < B)%R.
  rewrite ltNge; apply/negP => B0; move: c1; rewrite /c.
  by have := ln_le0 (le_trans B0 ler01); rewrite -/c; lra.
have eB : expR c = B by rewrite lnK// posrE.
(* l Z <= e^(l Z - c) + c - 1 *)
have pt x : (Z x <= (expR (l * Z x - c) + (c - 1)) / l)%R.
  rewrite ler_pdivlMr// mulrC.
  by have := expR_ge1Dx (l * Z x - c); lra.
have c0 : (0 <= c - 1)%R by rewrite subr_ge0.
have il0 : (0 <= l^-1)%R by rewrite invr_ge0 ltW.
have mE : measurable_fun [set: T] (fun x => expR (l * Z x - c)).
  apply: measurableT_comp; first exact: measurable_expR.
  apply: measurable_funB; last exact: measurable_cst.
  by apply: measurable_funM => //; exact: measurable_cst.
have mlE : measurable_fun [set: T]
    (fun x => (l^-1 * expR (l * Z x - c))%:E).
  by apply/measurable_EFinP; apply: measurable_funM => //;
    exact: measurable_cst.
apply: (@le_trans _ _ (\int[P]_x ((l^-1 * expR (l * Z x - c))%:E +
    (l^-1 * (c - 1))%:E))).
  apply: ge0_le_integral => //.
  - by move=> x _; rewrite lee_fin.
  - exact/measurable_EFinP.
  - by apply: emeasurable_funD.
  by move=> x _; rewrite -EFinD lee_fin -mulrDr mulrC; exact: pt.
rewrite ge0_integralD//.
- by move=> x _; rewrite lee_fin mulr_ge0// expR_ge0.
- by move=> x _; rewrite lee_fin mulr_ge0.
rewrite integral_cst// [X in _ * X]probability_setT mule1.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin//; first exact/measurable_EFinP.
(* E e^(l Z - c) = e^-c E e^(l Z) <= 1 *)
have I1 : \int[P]_x (expR (l * Z x - c))%:E <= 1%:E.
  have -> : (fun x => (expR (l * Z x - c))%:E) =
      (fun x => (expR (- c))%:E * (expR (l * Z x))%:E).
    by apply/funext => x; rewrite -EFinM -expRD addrC.
  rewrite ge0_integralZl_EFin ?expR_ge0//.
    apply/measurable_EFinP.
    apply: measurableT_comp; first exact: measurable_expR.
    by apply: measurable_funM => //; exact: measurable_cst.
  apply: le_trans (lee_wpmul2l _ hB) _; first by rewrite lee_fin expR_ge0.
  by rewrite -EFinM -eB -expRD addNr expR0.
have I0 : 0 <= \int[P]_x (expR (l * Z x - c))%:E.
  by apply: integral_ge0 => x _; rewrite lee_fin expR_ge0.
move: I0 I1; case: (\int[P]_x _) => [i||]//= i0 i1.
rewrite -EFinM -EFinD lee_fin; rewrite !lee_fin in i0 i1.
by rewrite -mulrDr mulrC; apply: ler_wpM2r => //; rewrite -/c; lra.
Qed.

Lemma measurable_bigmax_seq (I : Type) (V : seq I) (F : I -> T -> R) :
  (forall v, measurable_fun [set: T] (F v)) ->
  measurable_fun [set: T] (fun x => \big[Num.max/0%R]_(v <- V) F v x).
Proof.
move=> mF; elim: V => [|v V IH].
  by under eq_fun do rewrite big_nil; exact: measurable_cst.
by under eq_fun do rewrite big_cons; exact: measurable_maxr.
Qed.

Lemma expR_bigmax_le (I : Type) (V : seq I) (l : R) (S : I -> R) :
  (0 <= l)%R ->
  (expR (l * \big[Num.max/0%R]_(v <- V) `|S v|) <=
   1 + \sum_(v <- V) (expR (l * S v) + expR (- (l * S v))))%R.
Proof.
move=> l0; elim: V => [|v V IH]; first by rewrite !big_nil mulr0 expR0 addr0.
rewrite big_cons [X in (_ <= 1 + X)%R]big_cons.
have e1 : (expR (l * `|S v|) <= expR (l * S v) + expR (- (l * S v)))%R.
  case: (lerP 0 (S v)) => sv.
    by rewrite ger0_norm// lerDl expR_ge0.
  by rewrite ltr0_norm// mulrN lerDr expR_ge0.
set M := (\big[Num.max/0]_(j <- V) `|S j|)%R.
case: (leP `|S v|%R M) => _.
  by apply: le_trans IH _; rewrite addrCA lerDr addr_ge0 ?expR_ge0.
apply: le_trans e1 _; rewrite addrCA lerDl addr_ge0//.
by apply: sumr_ge0 => j _; rewrite addr_ge0 ?expR_ge0.
Qed.

End maximal_inequality.

Section maximal_inequality_sum.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* A maximal inequality for sums of independent centered subexponential
   variables over a finite family. *)
Theorem subexponential_max_sum (mu : nat -> probability T R) n (I : Type)
    (V : seq I) (g : I -> T -> R) (a : nat -> R) (L : R) : (0 < L)%R ->
  (forall v i, (i < n)%N -> subexponential (mu i) (g v) L) ->
  (forall v i, (i < n)%N -> \int[mu i]_t g v t = 0)%R ->
  (forall i, (i < n)%N -> `|a i| <= 1)%R ->
  \int[tuple_prod mu n]_x
    (\big[Num.max/0]_(v <- V) `|\sum_(i < n) a i * g v (tnth x i)|)%:E <=
  (8 * L * (Num.sqrt (n%:R * (1 + ln (1 + 2 * (size V)%:R))) +
     (1 + ln (1 + 2 * (size V)%:R))))%:E.
Proof.
move=> L0 sg g0 a1.
set Lam := (1 + ln (1 + 2 * (size V)%:R))%R.
have Lam1 : (1 <= Lam)%R.
  by rewrite /Lam lerDl ln_ge0// lerDl mulr_ge0.
have RHS0 : (0 <= 8 * L * (Num.sqrt (n%:R * Lam) + Lam))%R.
  rewrite mulr_ge0// ?addr_ge0//; first by rewrite mulr_ge0// ltW.
  by rewrite ln_ge0// lerDl mulr_ge0.
case: n sg g0 a1 RHS0 => [|n] sg g0 a1 RHS0.
  have -> : (fun x : 0.-tuple T => (\big[Num.max/0]_(v <- V)
      `|\sum_(i < 0) a i * g v (tnth x i)|)%:E) = (fun _ => 0%:E).
    apply/funext => x; congr EFin; under eq_bigr do rewrite big_ord0 normr0.
    by elim: V {Lam Lam1 RHS0} => [|v V IH];
      rewrite ?big_nil ?big_cons ?IH ?maxxx.
  by rewrite integral0 lee_fin.
have mg v : measurable_fun [set: T] (g v) by have [] := sg v 0%N isT.
set S := fun v (x : n.+1.-tuple T) => (\sum_(i < n.+1) a i * g v (tnth x i))%R.
have mS v : measurable_fun [set: n.+1.-tuple T] (S v).
  apply: measurable_sum => i.
  apply: measurable_funM; first exact: measurable_cst.
  exact: measurableT_comp (mg v) (measurable_tnth i).
set Z := fun x => (\big[Num.max/0]_(v <- V) `|S v x|)%R.
have mZ : measurable_fun [set: n.+1.-tuple T] Z.
  by apply: measurable_bigmax_seq => v; exact: measurableT_comp (mS v).
have Z0 x : (0 <= Z x)%R.
  by rewrite /Z; elim/big_rec: _ => // v y _ y0; rewrite le_max y0 orbT.
have key (l : R) : (0 < l)%R -> (l <= (2 * L)^-1)%R ->
    \int[tuple_prod mu n.+1]_x (Z x)%:E <=
    ((Lam + 16 * l ^+ 2 * n.+1%:R * L ^+ 2) / l)%:E.
  move=> l0 l1.
  set E := expR (16 * l ^+ 2 * n.+1%:R * L ^+ 2).
  have mgf (v : I) (s : R) : (`|s| = 1)%R ->
      \int[tuple_prod mu n.+1]_x (expR (s * l * S v x))%:E <= E%:E.
    move=> s1.
    have h := @subexponential_sum_mgf _ _ _ mu n.+1 (fun=> g v) (fun=> L) a
      (s * l) (fun i ilt => sg v i ilt) (fun i ilt => g0 v i ilt).
    have h1 : forall i : nat, (i < n.+1)%N -> (`|s * l * a i| <= (2 * L)^-1)%R.
      move=> i ilt; rewrite !normrM s1 mul1r (gtr0_norm l0).
      apply: le_trans l1; rewrite -[X in (_ <= X)%R]mulr1.
      by apply: ler_wpM2l; [exact: ltW|exact: a1].
    apply: le_trans (h h1) _; rewrite lee_fin ler_expR /E.
    have ss : (s ^+ 2 = 1)%R.
      by rewrite -[(s ^+ 2)%R]real_normK ?num_real// s1 expr1n.
    have sum_le : (\sum_(i < n.+1) a i ^+ 2 * L ^+ 2 <= n.+1%:R * L ^+ 2)%R.
      have -> : (n.+1%:R * L ^+ 2 = \sum_(i < n.+1) L ^+ 2)%R.
        by rewrite sumr_const card_ord mulr_natl.
      apply: ler_sum => i _; rewrite -[X in (_ <= X)%R]mul1r.
      apply: ler_wpM2r; first exact: sqr_ge0.
      by rewrite -[(a i ^+ 2)%R]real_normK ?num_real// exprn_ile1// a1.
    rewrite exprMn ss mul1r -!mulrA; apply: ler_wpM2l => //.
    by rewrite !ler_pM2l.
  have mES (v : I) (s : R) : measurable_fun [set: n.+1.-tuple T]
      (fun x => (expR (s * l * S v x))%:E).
    apply/measurable_EFinP.
    apply: measurableT_comp; first exact: measurable_expR.
    by apply: measurable_funM; [exact: measurable_cst|exact: mS].
  (* the exponential moment of the maximum, through e^(l Z) <= 1 + sum of
     the e^(+- l S v) *)
  have hB : \int[tuple_prod mu n.+1]_x (expR (l * Z x))%:E <=
      (expR 1 * (1 + 2 * (size V)%:R) * E)%:E.
    apply: (@le_trans _ _ (\int[tuple_prod mu n.+1]_x
        ((1%R)%:E + \sum_(v <- V)
          ((expR (1 * l * S v x))%:E + (expR (-1 * l * S v x))%:E)))).
      apply: ge0_le_integral => //.
      - apply/measurable_EFinP.
        apply: measurableT_comp; first exact: measurable_expR.
        by apply: measurable_funM => //; exact: measurable_cst.
      - apply: emeasurable_funD; first exact: measurable_cst.
        by apply: emeasurable_sum => v; apply: emeasurable_funD; exact: mES.
      - move=> x _.
        under eq_bigr => v _ do rewrite -EFinD.
        rewrite sumEFin -EFinD lee_fin.
        apply: le_trans (expR_bigmax_le V (S ^~ x) (ltW l0)) _.
        by rewrite lerD2l; apply: ler_sum => v _; rewrite mul1r mulN1r mulNr.
    have e0 (s : R) (v : I) x :
        [set: (n.+1).-tuple T] x -> 0 <= (expR (s * l * S v x))%:E.
      by move=> _; rewrite lee_fin expR_ge0.
    have n1 : `|(-1 : R)|%R = 1%R by rewrite normrN normr1.
    have hF (v : I) : \int[tuple_prod mu n.+1]_x
        ((expR (1 * l * S v x))%:E + (expR (-1 * l * S v x))%:E) <= (2 * E)%:E.
      rewrite (ge0_integralD _ measurableT (e0 1%R v) (mES v 1%R)
        (e0 (-1)%R v) (mES v (-1)%R)).
      apply: le_trans (leeD (mgf v 1%R (normr1 _)) (mgf v (-1)%R n1)) _.
      by rewrite -EFinD lee_fin; lra.
    have hV (W : seq I) : \sum_(v <- W) \int[tuple_prod mu n.+1]_x
        ((expR (1 * l * S v x))%:E + (expR (-1 * l * S v x))%:E) <=
        ((size W)%:R * (2 * E))%:E.
      elim: W => [|w W IH]; first by rewrite big_nil mul0r.
      rewrite big_cons mulrS mulrDl [(1 * (2 * E))%R]mul1r EFinD.
      exact: leeD (hF w) IH.
    have mF (v : I) : measurable_fun [set: (n.+1).-tuple T]
        (fun x => (expR (1 * l * S v x))%:E + (expR (-1 * l * S v x))%:E).
      by apply: emeasurable_funD; exact: mES.
    have F0 (v : I) x : [set: (n.+1).-tuple T] x ->
        0 <= (expR (1 * l * S v x))%:E + (expR (-1 * l * S v x))%:E.
      by move=> _; rewrite adde_ge0// lee_fin expR_ge0.
    rewrite ge0_integralD//.
      by move=> x _; apply: sume_ge0 => v _; exact: F0.
      exact: emeasurable_sum.
    rewrite integral_cst// [X in 1 * X]probability_setT mul1e.
    rewrite (ge0_integral_sum _ measurableT mF F0).
    apply: le_trans (leeD (lexx 1) (hV V)) _.
    rewrite -EFinD lee_fin.
    have E1 : (1 <= E)%R.
      rewrite /E -[X in (X <= _)%R]expR0 ler_expR.
      apply: mulr_ge0; last exact: sqr_ge0.
      by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: sqr_ge0.
    have e1 : (1 <= expR 1 :> R)%R by rewrite -[X in (X <= _)%R]expR0 ler_expR.
    have NV : (0 <= (size V)%:R :> R)%R by [].
    apply: (@le_trans _ _ ((1 + 2 * (size V)%:R) * E)%R); first lra.
    rewrite -mulrA; apply: ler_peMl => //.
    by rewrite mulr_ge0//; lra.
  have q0 : (0 <= 16 * l ^+ 2 * n.+1%:R * L ^+ 2)%R.
    apply: mulr_ge0; last exact: sqr_ge0.
    by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: sqr_ge0.
  have eN : ((expR 1 : R) * (1 + 2 * (size V)%:R) \in Num.pos)%R.
    by rewrite posrE mulr_gt0 ?expR_gt0// ltr_pwDl// mulr_ge0.
  have EP : (E \in Num.pos)%R by rewrite posrE expR_gt0.
  have NP : ((1 + 2 * (size V)%:R : R) \in Num.pos)%R.
    by rewrite posrE ltr_pwDl// mulr_ge0.
  have eP : ((expR 1 : R) \in Num.pos)%R by rewrite posrE expR_gt0.
  have lnB : ln (expR 1 * (1 + 2 * (size V)%:R) * E) =
      (Lam + 16 * l ^+ 2 * n.+1%:R * L ^+ 2)%R.
    by rewrite (lnM eN EP) (lnM eP NP) /E !expRK.
  have lnB1 : (1 <= ln (expR 1 * (1 + 2 * (size V)%:R) * E))%R.
    by rewrite lnB; apply: le_trans Lam1 _; rewrite lerDl.
  by apply: le_trans (expectation_le_ln_mgf mZ Z0 l0 lnB1 hB) _; rewrite lnB.
(* the choice of l *)
have N0 : (0 < n.+1%:R :> R)%R by rewrite ltr0Sn.
have Lam0 : (0 < Lam)%R by apply: lt_le_trans Lam1; exact: ltr01.
have Lne : L != 0%R by rewrite gt_eqF.
pose s := Num.sqrt Lam; pose t := Num.sqrt (n.+1%:R : R).
have s0 : (0 < s)%R by rewrite sqrtr_gt0.
have t0 : (0 < t)%R by rewrite sqrtr_gt0.
have Ls : (s ^+ 2 = Lam)%R by rewrite sqr_sqrtr// ltW.
have Nt : (t ^+ 2 = n.+1%:R)%R by rewrite sqr_sqrtr// ltW.
have -> : Num.sqrt (n.+1%:R * Lam) = (t * s)%R by rewrite sqrtrM// ltW.
case: (leP Lam (4 * n.+1%:R)%R) => hL.
  have st : (s <= 2 * t)%R by nra.
  have l0 : (0 < s / (4 * L * t))%R by rewrite divr_gt0// !mulr_gt0.
  have tne : t != 0%R by rewrite gt_eqF.
  have sne : s != 0%R by rewrite gt_eqF.
  have l1 : (s / (4 * L * t) <= (2 * L)^-1)%R.
    rewrite ler_pdivrMr ?mulr_gt0//.
    by have -> : ((2 * L)^-1 * (4 * L * t) = 2 * t)%R by field.
  apply: le_trans (key _ l0 l1) _; rewrite lee_fin -Ls -Nt.
  have -> : ((s ^+ 2 + 16 * (s / (4 * L * t)) ^+ 2 * t ^+ 2 * L ^+ 2) /
      (s / (4 * L * t)) = 8 * L * (t * s))%R by field.
  by rewrite ler_pM2l ?mulr_gt0// lerDl sqr_ge0.
have l0 : (0 < (2 * L)^-1)%R by rewrite invr_gt0 mulr_gt0.
apply: le_trans (key _ l0 (lexx _)) _; rewrite lee_fin.
have -> : ((Lam + 16 * (2 * L)^-1 ^+ 2 * n.+1%:R * L ^+ 2) / (2 * L)^-1 =
    2 * L * (Lam + 4 * n.+1%:R))%R by field.
have ts0 : (0 <= L * (t * s))%R by rewrite mulr_ge0// ?mulr_ge0// ltW.
have h1 : (0 <= L * (Lam - 4 * n.+1%:R))%R by rewrite mulr_ge0 ?subr_ge0// ltW.
have h2 : (0 <= L * Lam)%R by rewrite mulr_ge0// ltW.
lra.
Qed.

End maximal_inequality_sum.


Section random_matrix_sum.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The logarithm of the number of points of the 1/4-net of the unit ball,
   as it enters subexponential_max_sum. *)
Lemma net_log_le m (N : R) : (0 <= N)%R -> (N <= (18 * expR 1) ^+ m)%R ->
  (1 + ln (1 + 2 * N) <= 6 * m.+1%:R)%R.
Proof.
move=> N0 hN.
have e2 : (2 <= expR 1 :> R)%R.
  by apply: le_trans (expR_ge1Dx 1); rewrite -[X in (X <= _)%R](natrD _ 1 1).
have e5 : (18 <= expR 5 :> R)%R.
  rewrite -[X in expR X](mulr1 5%:R) expRM_natl.
  apply: (@le_trans _ _ (2 ^+ 5)%R); first by rewrite -natrX ler_nat.
  by apply: lerXn2r; rewrite ?nnegrE ?expR_ge0.
have e18 : (18 * expR 1 <= expR 6 :> R)%R.
  have -> : (6 = 5 + 1 :> R)%R by rewrite (natrD _ 5 1).
  by rewrite expRD; apply: ler_wpM2r => //; exact: expR_ge0.
have eM : ((18 * expR 1) ^+ m <= expR (6 * m%:R) :> R)%R.
  by rewrite expRM_natr; apply: lerXn2r; rewrite ?nnegrE ?expR_ge0.
have M1 : (1 <= expR (6 * m%:R) :> R)%R.
  by rewrite -[X in (X <= _)%R]expR0 ler_expR mulr_ge0.
have e3 : (3 <= expR 5 :> R)%R by apply: le_trans e5; rewrite ler_nat.
have h2 : (1 + 2 * N <= expR (6 * m.+1%:R - 1))%R.
  have -> : (6 * m.+1%:R - 1 = 5 + 6 * m%:R :> R)%R by rewrite mulrSr; lra.
  rewrite expRD; apply: (@le_trans _ _ (3 * expR (6 * m%:R))%R).
    by have := le_trans hN eM; lra.
  by apply: ler_wpM2r => //; exact: expR_ge0.
have p1 : (1 + 2 * N \in Num.pos)%R by rewrite posrE; lra.
have p2 : (expR (6 * m.+1%:R - 1 : R) \in Num.pos)%R by rewrite posrE expR_gt0.
by move: h2; rewrite -(ler_ln p1 p2) expRK; lra.
Qed.

(* The operator norm of a weighted sum of independent random matrices whose
   quadratic forms are centered and subexponential, through a measurable
   majorant (the operator norm is a supremum over the unit ball), the same
   for all weights. *)
Theorem opnorm_sum_subexponential (mu : nat -> probability T R) n m
    (Y : T -> 'M[R]_m) (L : R) : (0 < L)%R ->
  (forall (v : 'cV[R]_m) k, (frobenius v <= 1)%R -> (k < n)%N ->
     subexponential (mu k) (fun t => mxdot v (Y t *m v)) L) ->
  (forall (v : 'cV[R]_m) k, (frobenius v <= 1)%R -> (k < n)%N ->
     \int[mu k]_t mxdot v (Y t *m v) = 0)%R ->
  exists N : (nat -> R) -> n.-tuple T -> R, forall a : nat -> R,
    (forall k, (k < n)%N -> `|a k| <= 1)%R ->
  [/\ measurable_fun [set: n.-tuple T] (N a),
    (forall x,
      opnorm (sym_part (\sum_(k < n) a k *: Y (tnth x k))) <= N a x)%R &
    \int[tuple_prod mu n]_x (N a x)%:E <=
      (96 * L * (Num.sqrt (n%:R * m.+1%:R) + m.+1%:R))%:E].
Proof.
move=> L0 sY Y0.
have [V [Vnet V1 Vs]] := @unit_ball_quarter_net R m.
(* the quadratic forms, set to 0 outside the unit ball *)
pose g (v : 'cV[R]_m) : T -> R :=
  if (frobenius v <= 1)%R then (fun t => mxdot v (Y t *m v)) else (fun=> 0%R).
have sg v k : (k < n)%N -> subexponential (mu k) (g v) L.
  move=> kn; rewrite /g; case: ifP => v1; first exact: sY.
  split => //.
  under eq_integral do rewrite /= normr0 mul0r expR0.
  by rewrite integral_cst// [X in _ * X]probability_setT mul1e lee_fin ler1n.
have g0 v k : (k < n)%N -> (\int[mu k]_t g v t = 0)%R.
  move=> kn; rewrite /g; case: ifP => v1; first exact: Y0.
  by rewrite /Rintegral integral0.
pose M (a : nat -> R) (x : n.-tuple T) :=
  (\big[Num.max/0]_(v <- V) `|\sum_(k < n) a k * g v (tnth x k)|)%R.
have mM a : measurable_fun [set: n.-tuple T] (M a).
  apply: measurable_bigmax_seq => v; apply: measurableT_comp => //.
  apply: measurable_sum => k.
  apply: measurable_funM; first exact: measurable_cst.
  have [_ mg _] := sg v k (ltn_ord k).
  exact: measurableT_comp mg (measurable_tnth k).
have M0 a x : (0 <= M a x)%R.
  by rewrite /M; elim/big_rec: _ => // v y _ y0; rewrite le_max y0 orbT.
exists (fun a x => 2 * M a x)%R => a a1; split.
- by apply: measurable_funM => //; exact: measurable_cst.
- move=> x; apply: le_trans (opnorm_sym_part_net _ Vnet V1) _.
  rewrite ler_pM2l//.
  rewrite (eq_big_seq (fun v => `|\sum_(k < n) a k * g v (tnth x k)|)%R)//.
  move=> v vV /=; congr (`|_|)%R; rewrite /g (V1 v vV) mulmx_suml mxdot_sumr.
  by apply: eq_bigr => k _; rewrite -scalemxAl mxdotZr.
- under eq_integral do rewrite EFinM.
  rewrite ge0_integralZl_EFin//; first by move=> x _; rewrite lee_fin M0.
    exact/measurable_EFinP.
  have h := @subexponential_max_sum _ _ _ mu n _ V g a L L0 sg g0 a1.
  apply: le_trans (lee_wpmul2l _ h) _; first by rewrite lee_fin.
  rewrite -EFinM lee_fin.
  have hL := net_log_le (ler0n _ _) Vs.
  set Lam := (1 + ln (1 + 2 * (size V)%:R))%R in hL *.
  have hs : (Num.sqrt (n%:R * Lam) <= 6 * Num.sqrt (n%:R * m.+1%:R))%R.
    have -> : (6 * Num.sqrt (n%:R * m.+1%:R) =
        Num.sqrt (6 ^+ 2 * (n%:R * m.+1%:R)) :> R)%R.
      rewrite [Num.sqrt (6 ^+ 2 * _)]sqrtrM; first by [].
      by rewrite sqrtr_sqr ger0_norm.
    have n0 : (0 <= n%:R :> R)%R by [].
    have m0 : (0 <= m.+1%:R :> R)%R by [].
    rewrite ler_sqrt; first by rewrite mulr_ge0// mulr_ge0.
    nra.
  have h1 : (0 <= L * (6 * Num.sqrt (n%:R * m.+1%:R) -
      Num.sqrt (n%:R * Lam)))%R by rewrite mulr_ge0 ?subr_ge0// ltW.
  have h2 : (0 <= L * (6 * m.+1%:R - Lam))%R.
    by rewrite mulr_ge0 ?subr_ge0// ltW.
  lra.
Qed.

End random_matrix_sum.
