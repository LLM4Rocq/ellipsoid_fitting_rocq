From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.comparison Require Import normal_mgf chi_square gauss_law.
From GaussianAnalysis.probability Require Import lindeberg subgaussian.
From GaussianAnalysis.probability Require Import conditioning.

(**md**************************************************************************)
(* # The Hanson-Wright inequality                                             *)
(*                                                                            *)
(* Let x have law tuple_prod mu n, so that X_i = f_i (x_i) are independent,   *)
(* centered and subgaussian with constant K (subgaussian.v), and let A be a   *)
(* real n x n matrix. The quadratic form Q = \sum_(i, j) a_ij X_i X_j         *)
(* concentrates around its mean: Hanson and Wright, in the form of Rudelson   *)
(* and Vershynin (Vershynin, High-Dimensional Probability, theorem 6.2.1).    *)
(* This is item HW of phase 5 (Lemma 3.2 of Koehler and Sohn, arXiv           *)
(* 2608.27372, lines 2157-2185), proved with explicit constants.              *)
(*                                                                            *)
(* Proved:                                                                    *)
(*                                                                            *)
(* - integral_gauss_expR_dot: E exp <g, w> = exp (|w|^2 / 2) for g of law     *)
(*   gauss n.                                                                 *)
(* - gauss_chaos_mgf: for M : 'M_(n, m), 0 <= t and 4 t opnorm M ^ 2 <= 1, E  *)
(*   exp (t |g M|^2) <= exp (3 / 2 t |M|_F^2): g M has the law of h B with B  *)
(*   = diag (sqrt d) P for the spectral decomposition M^T M = P^T diag d P    *)
(*   (ge0_integral_gauss_mulmx), and |h B|^2 is a weighted chi-square.        *)
(* - offdiag_decouple: \sum_(i != j) c_ij = 4 / 2^n \sum_S \sum_(i in S, j    *)
(*   notin S) c_ij, since a quarter of the sets S contain i and not j         *)
(*   (sum_set_indicator, by the involutions set_toggle); expR_avg_le,         *)
(*   Jensen's inequality for exp and a finite average; ge0_integral_avg.      *)
(* - hw_decoupled_mgf: for every set S, E exp (l \sum_(i in S, j notin S)     *)
(*   a_ij X_i X_j) <= exp (27 l^2 K^4 |A|_F^2) when 72 l^2 K^4 opnorm A ^ 2   *)
(*   <= 1. Resample the coordinates outside S (ge0_integral_tuple_prod_merge  *)
(*   of conditioning.v), apply Hoeffding's inequality to them, write the      *)
(*   result as a Gaussian integral, exchange the integrals (fubini_tonelli),  *)
(*   apply Hoeffding's inequality to the coordinates in S, and bound the      *)
(*   Gaussian chaos with the matrix hw_mask S A, whose norms are at most      *)
(*   those of A.                                                              *)
(* - hw_offdiag_mgf: E exp (l \sum_(i != j) a_ij X_i X_j) <= exp (432 l^2 K^4 *)
(*   |A|_F^2) when 1152 l^2 K^4 opnorm A ^ 2 <= 1, by offdiag_decouple and    *)
(*   expR_avg_le.                                                             *)
(*                                                                            *)
(* Planned (phase 5, stage 3; names come with the proofs):                    *)
(*                                                                            *)
(* - the diagonal \sum_i a_ii (X_i^2 - E X_i^2) by Bernstein's inequality;    *)
(* - hanson_wright: P(|Q - E Q| >= u) <= 2 exp (- c min (u^2 / (K^4 |A|_F^2), *)
(*   u / (K^2 opnorm A))), and Q - E Q is subexponential with constant C K^2  *)
(*   |A|_F.                                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gauss_mgf.
Context {R : realType}.

(* The moment generating function of the standard Gaussian vector. *)
Lemma integral_gauss_expR_dot n (w : 'rV[R]_n) :
  (\int[gauss n]_g (expR (mxdot g w))%:E = (expR (mxdot w w / 2))%:E)%E.
Proof.
have E (g : 'rV[R]_n) : expR (mxdot g w) = \prod_(i < n) expR (w 0 i * g 0 i).
  by rewrite /mxdot big_ord1 expR_sum; apply: eq_bigr => i _; rewrite mulrC.
under eq_integral do rewrite E.
have mf (i : 'I_n) : measurable_fun [set: R] (fun s : R => expR (w 0 i * s)).
  by apply: measurableT_comp => //; apply: measurable_funM.
have f0 (i : 'I_n) (s : R) : 0 <= expR (w 0 i * s) by exact: expR_ge0.
rewrite (ge0_integral_gauss_prod mf f0).
transitivity (\prod_(i < n) (expR (w 0 i ^+ 2 / 2))%:E)%E.
  apply: eq_bigr => i _; rewrite integral_normal_expR ?oner_neq0 //.
  by rewrite mulr0 add0r expr1n mulr1.
rewrite prodEFin -expR_sum /mxdot big_ord1 mulr_suml.
by congr (expR _)%:E; apply: eq_bigr => i _; rewrite expr2.
Qed.

(* A Gaussian chaos: |g M|^2 for g of law gauss n. *)
Lemma gauss_chaos_mgf n m (M : 'M[R]_(n, m)) (t : R) :
  0 <= t -> 4 * t * opnorm M ^+ 2 <= 1 ->
  (\int[gauss n]_g (expR (t * mxdot (g *m M) (g *m M)))%:E <=
   (expR (3 / 2 * t * mxdot M M))%:E)%E.
Proof.
move=> t0 tM; set S := M^T *m M; set L := opnorm M ^+ 2 in tM *.
have Ssym : S \is symmetricmx by apply/symmetricmxP; rewrite /S trmx_mul trmxK.
have [P Po [dd SE]] := symmetric_spectral Ssym.
have hform (x : 'cV[R]_m) : mxdot x (S *m x) = mxdot (M *m x) (M *m x).
  by rewrite /S -mulmxA mxdot_mulmxl.
have d0 k : 0 <= dd 0 k.
  move: k; apply/(spectral_form_ge 0 Po SE) => x.
  by rewrite mul0r hform mxdot_ge0.
have dL k : dd 0 k <= L.
  move: k; apply/(spectral_form_le _ Po SE) => x.
  rewrite hform -!frobenius_sqr /L.
  have := frobenius_mulmx_opnorm M x; have := frobenius_ge0 (M *m x).
  have := frobenius_ge0 x; have := opnorm_ge0 M; nra.
pose sq : 'rV[R]_m := \row_k Num.sqrt (dd 0 k).
pose B := diag_mx sq *m P.
have BB : M^T *m M = B^T *m B.
  rewrite /B trmx_mul tr_diag_mx mulmxA -(mulmxA P^T) mulmx_diag -/S SE.
  congr (_ *m diag_mx _ *m _); apply/rowP => k; rewrite !mxE.
  by rewrite -expr2 sqr_sqrtr.
have mf : measurable_fun [set: 'rV[R]_m]
    (fun y : 'rV[R]_m => (expR (t * mxdot y y))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  apply: measurable_funM => //; rewrite /mxdot; apply: measurable_sum => i.
  apply: measurable_sum => j; apply: measurable_funM => //;
    exact: measurable_mxentry.
rewrite (ge0_integral_gauss_mulmx BB mf (fun y => expR_ge0 _)).
have hB (y : 'rV[R]_m) : mxdot (y *m B) (y *m B) =
    \sum_k dd 0 k + centered_chi2 dd y.
  rewrite /B mulmxA mxdot_orthogonalmxr // /centered_chi2 -big_split /=.
  rewrite /mxdot big_ord1; apply: eq_bigr => k _.
  rewrite mul_mx_diag !mxE; have -> : y ord0 k = y 0 k by [].
  by rewrite mulrACA -!expr2 sqr_sqrtr //; ring.
under eq_integral do rewrite hB mulrDr expRD EFinM.
rewrite ge0_integralZl_EFin //.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  by apply: measurable_funM => //; exact: measurable_centered_chi2.
have dL' i : `|dd 0 i| <= L by rewrite ger0_norm.
have L0 : 0 <= L by rewrite /L exprn_ge0 ?opnorm_ge0.
have tL : `|2 * t| * L < 1.
  by rewrite ger0_norm ?mulr_ge0 //; nra.
have hc := integral_gauss_expR_centered_chi2_le dL' tL.
have e0 : (0 <= (expR (t * \sum_k dd 0 k))%:E)%E by rewrite lee_fin expR_ge0.
apply: le_trans (lee_wpmul2l e0 hc) _.
rewrite -EFinM -expRD lee_fin ler_expR.
have trS : \sum_k dd 0 k = mxdot M M.
  by rewrite -(spectral_trace Po SE) /S mxtrace_mulC -mxdot_trace.
have dd2 : mxdot dd dd <= L * mxdot M M.
  rewrite -trS mulr_sumr /mxdot big_ord1; apply: ler_sum => k _.
  by rewrite ler_wpM2r.
rewrite trS ger0_norm //.
have h1 : 0 < 1 - 2 * t * L by nra.
have MM0 : 0 <= mxdot M M := mxdot_ge0 M.
have key : t ^+ 2 * mxdot dd dd / (1 - 2 * t * L) <= t / 2 * mxdot M M.
  rewrite ler_pdivrMr //.
  have p1 : 0 <= t ^+ 2 * (L * mxdot M M - mxdot dd dd).
    by rewrite mulr_ge0 ?sqr_ge0 // subr_ge0.
  have p2 : 0 <= t * mxdot M M * (1 - 4 * t * L).
    by rewrite mulr_ge0 ?mulr_ge0 // subr_ge0.
  lra.
by move: key; lra.
Qed.

End gauss_mgf.

Section decoupling.
Context {R : realType} (n : nat).
Implicit Types (S : {set 'I_n}) (i j k l : 'I_n).

(* Remove k from S if it is there, add it otherwise. *)
Definition set_toggle k S : {set 'I_n} := if k \in S then S :\ k else k |: S.

Lemma set_toggleK k : involutive (set_toggle k).
Proof.
move=> S; rewrite /set_toggle; case: (boolP (k \in S)) => kS.
  by rewrite finset.setD11 finset.setD1K.
by rewrite finset.setU11 finset.setU1K.
Qed.

Lemma in_set_toggle k l S :
  (l \in set_toggle k S) = (if l == k then k \notin S else l \in S).
Proof.
rewrite /set_toggle; case: (boolP (k \in S)) => kS; case: eqP => [->|lk].
- by rewrite finset.setD11.
- by rewrite finset.in_setD1; move/eqP: lk => ->.
- by rewrite finset.setU11.
- by rewrite finset.in_setU1; move/eqP: lk => /negbTE ->.
Qed.

Lemma card_set_ord : #|{set 'I_n}| = 2 ^ n.
Proof. by rewrite -cardsT -powersetT card_powerset cardsT card_ord. Qed.

(* For i != j, a quarter of the sets contain i and not j. *)
Lemma sum_set_indicator i j : i != j ->
  \sum_(S : {set 'I_n}) ((i \in S) && (j \notin S))%:R = (2 ^ n)%:R / 4 :> R.
Proof.
move=> ij.
pose N (a b : bool) : R :=
  \sum_(S : {set 'I_n}) (((i \in S) == a) && ((j \in S) == b))%:R.
have NTF : \sum_(S : {set 'I_n}) ((i \in S) && (j \notin S))%:R = N true false.
  by apply: eq_bigr => S _; case: (i \in S); case: (j \in S).
have ji : (j == i) = false by apply/negbTE; rewrite eq_sym.
have Ti a b : N a b = N (~~ a) b.
  rewrite /N (reindex_inj (inv_inj (set_toggleK i))) /=; apply: eq_bigr => S _.
  rewrite !in_set_toggle eqxx ji.
  by case: (i \in S); case: a.
have Tj a b : N a b = N a (~~ b).
  rewrite /N (reindex_inj (inv_inj (set_toggleK j))) /=; apply: eq_bigr => S _.
  rewrite !in_set_toggle eqxx (negbTE ij).
  by case: (j \in S); case: b.
have total : N true true + N true false + N false true + N false false =
    (2 ^ n)%:R.
  rewrite /N -!big_split /=.
  rewrite (eq_bigr (fun _ => 1)).
    by move=> S _; case: (i \in S); case: (j \in S); rewrite /= ?addr0 ?add0r.
  by rewrite sumr_const card_set_ord.
have e1 : N true true = N true false by rewrite (Tj true true).
have e2 : N false true = N true false by rewrite (Ti false true) /= -e1.
have e3 : N false false = N true false by rewrite (Ti false false).
rewrite NTF; move: total; rewrite e1 e2 e3 => <-.
by field.
Qed.

(* The off-diagonal sum as an average over the sets S of the sums over
   i in S and j notin S. *)
Lemma offdiag_decouple (c : 'I_n -> 'I_n -> R) :
  \sum_i \sum_j (i != j)%:R * c i j =
  4 / (2 ^ n)%:R * \sum_(S : {set 'I_n})
    \sum_i \sum_j ((i \in S) && (j \notin S))%:R * c i j.
Proof.
have p0 : (2 ^ n)%:R != 0 :> R by rewrite pnatr_eq0 expn_eq0.
have h i j : (i != j)%:R = 4 / (2 ^ n)%:R *
    \sum_(S : {set 'I_n}) ((i \in S) && (j \notin S))%:R :> R.
  have [<-|ij] := eqVneq i j.
    rewrite big1 ?mulr0 // => S _.
    by case: (i \in S).
  by rewrite (sum_set_indicator ij) /=; field.
rewrite mulr_sumr.
under [RHS]eq_bigr => S _ do rewrite mulr_sumr.
rewrite [RHS]exchange_big /=; apply: eq_bigr => i _.
under [RHS]eq_bigr => S _ do rewrite mulr_sumr.
rewrite [RHS]exchange_big /=; apply: eq_bigr => j _.
rewrite h mulr_sumr mulr_suml; apply: eq_bigr => S _; ring.
Qed.

End decoupling.

Section expR_avg.
Context {R : realType}.

(* Jensen's inequality for exp and a finite average. *)
Lemma expR_avg_le (I : finType) (y : I -> R) : (0 < #|I|)%N ->
  expR (#|I|%:R^-1 * \sum_k y k) <= #|I|%:R^-1 * \sum_k expR (y k).
Proof.
move=> I0; set m := #|I|%:R^-1 * \sum_k y k.
have c0 : 0 < #|I|%:R :> R by rewrite ltr0n.
have h k : expR m * (1 + (y k - m)) <= expR (y k).
  have e : expR (y k) = expR m * expR (y k - m) by rewrite -expRD addrC subrK.
  by rewrite e; apply: ler_wpM2l; [exact: expR_ge0 | exact: expR_ge1Dx].
have c0' : #|I|%:R != 0 :> R by rewrite gt_eqF.
have hs : \sum_k expR m * (1 + (y k - m)) = expR m * #|I|%:R.
  rewrite -mulr_sumr; congr (_ * _).
  by rewrite big_split /= sumrB !sumr_const /m; field.
rewrite ler_pdivlMl // mulrC -hs.
by apply: ler_sum => k _; exact: h.
Qed.

End expR_avg.

Section integral_avg.
Context d (T : measurableType d) (R : realType).
Variable mu : {measure set T -> \bar R}.

(* If each g k has integral at most B, so has their average. *)
Lemma ge0_integral_avg (I : finType) (g : I -> T -> R) (B : R) :
  (0 < #|I|)%N -> (forall k, measurable_fun [set: T] (g k)) ->
  (forall k x, 0 <= g k x) ->
  (forall k, \int[mu]_x (g k x)%:E <= B%:E)%E ->
  (\int[mu]_x (#|I|%:R^-1 * \sum_k g k x)%:E <= B%:E)%E.
Proof.
move=> I0 mg g0 hB.
have Ni : 0 <= #|I|%:R^-1 :> R by rewrite invr_ge0 ler0n.
under eq_integral do rewrite EFinM -sumEFin.
rewrite ge0_integralZl_EFin //; try by [
  move=> x _; apply: sume_ge0 => k _; rewrite lee_fin |
  apply: emeasurable_sum => k; exact/measurable_EFinP].
rewrite ge0_integral_sum //; try by [
  move=> k x _; rewrite lee_fin | move=> k; exact/measurable_EFinP].
have hs : (\sum_k \int[mu]_x (g k x)%:E <= \sum_(k : I) B%:E)%E.
  by apply: lee_sum => k _; exact: hB.
have := lee_wpmul2l (_ : (0 <= (#|I|%:R^-1)%:E)%E) hs.
move=> /(_ _)/le_trans; apply; first by rewrite lee_fin.
have c0 : #|I|%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
rewrite sumEFin sumr_const -EFinM lee_fin le_eqVlt; apply/orP; left.
by apply/eqP; field.
Qed.

End integral_avg.

Section hanson_wright.
Context d (T : measurableType d) (R : realType).
Variables (mu : nat -> probability T R) (n : nat) (f : nat -> T -> R) (K : R).
Hypothesis sf : forall i, (i < n)%N -> subgaussian (mu i) (f i) K.
Hypothesis f0 : forall i, (i < n)%N -> (\int[mu i]_t f i t = 0)%R.

Local Notation P := (tuple_prod mu n).
Local Notation X x i := (f (nat_of_ord i) (tnth x i)).

Let mX (i : 'I_n) : measurable_fun [set: n.-tuple T] (fun x => X x i).
Proof.
have [_ mfi _] := sf (ltn_ord i).
exact: measurableT_comp mfi (measurable_tnth i).
Qed.

(* The decoupled form \sum_(i in S, j notin S) a_ij X_i X_j. *)
Definition hw_decoupled (S : {set 'I_n}) (A : 'M[R]_n) (x : n.-tuple T) : R :=
  \sum_i \sum_j ((i \in S) && (j \notin S))%:R * (A i j * (X x i * X x j)).

(* A function of the ordinals as a function of the integers. *)
Definition ord_ext (c : 'I_n -> R) (k : nat) : R :=
  if insub k is Some i then c i else 0.

Lemma ord_extE (c : 'I_n -> R) (i : 'I_n) : ord_ext c i = c i.
Proof. by rewrite /ord_ext valK. Qed.

(* Hoeffding's inequality for coefficients indexed by 'I_n. *)
Let hoeffding (c : 'I_n -> R) (l : R) :
  (\int[P]_x (expR (l * \sum_i c i * X x i))%:E <=
   (expR (3 * l ^+ 2 * \sum_i c i ^+ 2 * K ^+ 2))%:E)%E.
Proof.
have := @subgaussian_sum_mgf _ _ R mu n f (fun=> K) (ord_ext c) l sf f0.
under eq_integral do under eq_bigr do rewrite ord_extE.
by under eq_bigr do rewrite ord_extE.
Qed.

(* The matrix of the decoupled form: (g M)_i = \sum_(j notin S) g_j a_ij
   for i in S, 0 otherwise. *)
Definition hw_mask (S : {set 'I_n}) (A : 'M[R]_n) : 'M[R]_n :=
  \matrix_(j, i) (((i \in S) && (j \notin S))%:R * A i j).

Lemma hw_mask_diag (S : {set 'I_n}) (A : 'M[R]_n) :
  hw_mask S A = diag_mx (\row_j (j \notin S)%:R) *m A^T *m
    diag_mx (\row_i (i \in S)%:R).
Proof.
apply/matrixP => j i; rewrite mul_mx_diag mul_diag_mx !mxE.
by case: (i \in S); case: (j \in S); rewrite /= ?mul0r ?mulr0 ?mul1r ?mulr1.
Qed.

Lemma opnorm_diag01 (v : 'rV[R]_n) : (forall i, v 0 i = 0 \/ v 0 i = 1) ->
  opnorm (diag_mx v) <= 1.
Proof.
move=> v01; apply/opnorm_leP => // x; rewrite mul1r.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?frobenius_ge0 //.
rewrite !frobenius_sqr /mxdot; apply: ler_sum => i _; rewrite !big_ord1.
rewrite mul_diag_mx !mxE; case: (v01 i) => ->; rewrite ?mul0r ?mul1r //.
by have := sqr_ge0 (x i ord0); rewrite expr2.
Qed.

Lemma opnorm_hw_mask (S : {set 'I_n}) (A : 'M[R]_n) :
  opnorm (hw_mask S A) <= opnorm A.
Proof.
have h01 (b : bool) : (b%:R : R) = 0 \/ b%:R = 1 by case: b; [right | left].
rewrite hw_mask_diag; apply: le_trans (opnorm_mulmx _ _) _.
apply: le_trans (ler_wpM2r (opnorm_ge0 _) (opnorm_mulmx _ _)) _.
rewrite -[Y in _ <= Y]mul1r -[Y in _ <= Y]mulr1 opnorm_trmx.
rewrite ler_pM ?mulr_ge0 ?opnorm_ge0 //; last first.
  by apply: opnorm_diag01 => i; rewrite mxE; exact: h01.
rewrite ler_pM ?opnorm_ge0 //.
by apply: opnorm_diag01 => i; rewrite mxE; exact: h01.
Qed.

Lemma mxdot_hw_mask (S : {set 'I_n}) (A : 'M[R]_n) :
  mxdot (hw_mask S A) (hw_mask S A) <= mxdot A A.
Proof.
rewrite /mxdot exchange_big /=; apply: ler_sum => i _; apply: ler_sum => j _.
rewrite !mxE; case: (i \in S); case: (j \in S) => /=;
  rewrite ?mul0r ?mul1r ?lexx //; by have := sqr_ge0 (A i j); rewrite expr2.
Qed.

(* The moment generating function of the decoupled form: resample the
   coordinates outside S, apply Hoeffding's inequality to them, write the
   result as a Gaussian integral, exchange the integrals, apply Hoeffding's
   inequality to the coordinates in S and bound the Gaussian chaos. *)
Theorem hw_decoupled_mgf (S : {set 'I_n}) (A : 'M[R]_n) (l : R) :
  72 * l ^+ 2 * K ^+ 4 * opnorm A ^+ 2 <= 1 ->
  (\int[P]_x (expR (l * hw_decoupled S A x))%:E <=
   (expR (27 * l ^+ 2 * K ^+ 4 * mxdot A A))%:E)%E.
Proof.
move=> hl.
pose Sp : {pred 'I_n} := [pred i | i \in S].
pose b (x : n.-tuple T) (j : 'I_n) : R :=
  \sum_i ((i \in S) && (j \notin S))%:R * (A i j * X x i).
have mb (j : 'I_n) : measurable_fun [set: n.-tuple T] (fun x => b x j).
  apply: measurable_sum => i; apply: measurable_funM => //.
  exact: measurable_funM.
have mD : measurable_fun [set: n.-tuple T] (hw_decoupled S A).
  rewrite /hw_decoupled; apply: measurable_sum => i; apply: measurable_sum => j.
  apply: measurable_funM => //; apply: measurable_funM => //.
  exact: measurable_funM.
have mF : measurable_fun [set: n.-tuple T]
    (fun x => (expR (l * hw_decoupled S A x))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  exact: measurable_funM.
have F0 x : (0 <= (expR (l * hw_decoupled S A x))%:E)%E.
  by rewrite lee_fin expR_ge0.
rewrite (ge0_integral_tuple_prod_merge Sp mu mF F0).
have hm x y : hw_decoupled S A (tuple_merge Sp x y) = \sum_j b x j * X y j.
  rewrite /hw_decoupled exchange_big /=; apply: eq_bigr => j _.
  rewrite /b mulr_suml; apply: eq_bigr => i _; rewrite !tnth_merge !inE.
  by case: (i \in S); case: (j \in S); rewrite /= ?mul0r // !mul1r mulrA.
(* Hoeffding's inequality in the coordinates outside S *)
pose H x : \bar R := (expR (3 * l ^+ 2 * \sum_j b x j ^+ 2 * K ^+ 2))%:E.
have mFm : measurable_fun [set: n.-tuple T * n.-tuple T]
    (fun p => (expR (l * hw_decoupled S A (tuple_merge Sp p.1 p.2)))%:E).
  exact: measurableT_comp mF (measurable_tuple_merge Sp).
have mI : measurable_fun [set: n.-tuple T] (fun x =>
    (\int[P]_y (expR (l * hw_decoupled S A (tuple_merge Sp x y)))%:E)%E).
  exact: (measurable_fun_fubini_tonelli_F (m2 := P) _ mFm
    (fun p => F0 _)).
have mH : measurable_fun [set: n.-tuple T] H.
  apply/measurable_EFinP; apply: measurableT_comp => //.
  apply: measurable_funM => //; apply: measurable_sum => j.
  by apply: measurable_funM => //; exact: measurable_funX.
apply: (@le_trans _ _ (\int[P]_x H x)%E).
  apply: ge0_le_integral => //.
    by move=> x _; apply: integral_ge0 => y _; exact: F0.
  move=> x _; under eq_integral do rewrite hm.
  exact: hoeffding.
(* the Gaussian identity, with s^2 = 6 l^2 K^2 *)
set s := Num.sqrt (6 * l ^+ 2 * K ^+ 2).
have h6 : 0 <= 6 * l ^+ 2 * K ^+ 2.
  by apply: mulr_ge0; [apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0] |
    exact: sqr_ge0].
have hs : s * s = 6 * l ^+ 2 * K ^+ 2 by rewrite -expr2 sqr_sqrtr.
pose w (x : n.-tuple T) : 'rV[R]_n := s *: \row_j b x j.
have hH x : H x = (\int[gauss n]_g (expR (mxdot g (w x)))%:E)%E.
  rewrite integral_gauss_expR_dot /w mxdotZl mxdotZr /H; congr (expR _)%:E.
  have e : mxdot (\row_j b x j) (\row_j b x j) = \sum_j b x j ^+ 2.
    by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite !mxE expr2.
  by rewrite e -mulr_suml [in RHS]mulrA hs; field.
have Gform (g : 'rV[R]_n) x :
    mxdot g (w x) = \sum_j g 0 j * (s * b x j).
  by rewrite /mxdot big_ord1; apply: eq_bigr => j _; rewrite /w !mxE.
pose G (p : n.-tuple T * 'rV[R]_n) : \bar R := (expR (mxdot p.2 (w p.1)))%:E.
have Gf : (fun p : n.-tuple T * 'rV[R]_n => mxdot p.2 (w p.1)) =
    (fun p => \sum_j p.2 0 j * (s * b p.1 j)).
  by apply/funext => p; rewrite Gform.
have mG : measurable_fun [set: n.-tuple T * 'rV[R]_n] G.
  apply/measurable_EFinP; apply: measurableT_comp => //; rewrite Gf.
  apply: measurable_sum => j; apply: measurable_funM.
    exact: measurableT_comp (measurable_mxentry 0 j) measurable_snd.
  apply: measurable_funM => //.
  exact: measurableT_comp (mb j) measurable_fst.
have G0 p : (0 <= G p)%E by rewrite lee_fin expR_ge0.
under eq_integral => x _ do rewrite hH.
rewrite (fubini_tonelli (m1 := P) (m2 := gauss n) _ mG G0).
(* Hoeffding's inequality in the coordinates in S *)
set M := hw_mask S A; set t := 18 * l ^+ 2 * K ^+ 4.
have K4 : 0 <= K ^+ 4 by rewrite exprn_even_ge0.
have t0 : 0 <= t.
  by apply: (mulr_ge0 _ K4); apply: (mulr_ge0 _ (sqr_ge0 l)); exact: ler0n.
have mIG : measurable_fun [set: 'rV[R]_n] (fun g => (\int[P]_x G (x, g))%E).
  exact: (measurable_fun_fubini_tonelli_G (m1 := P) _ mG G0).
have mC : measurable_fun [set: 'rV[R]_n]
    (fun g : 'rV[R]_n => (expR (t * mxdot (g *m M) (g *m M)))%:E).
  apply/measurable_EFinP; apply: measurableT_comp => //.
  apply: measurable_funM => //; rewrite /mxdot; apply: measurable_sum => i.
  apply: measurable_sum => j; apply: measurable_funM => //;
    apply: measurableT_comp (measurable_mxentry i j) _;
    by apply: measurable_mulmx => //; exact: measurable_cst.
apply: (@le_trans _ _ (\int[gauss n]_g
    (expR (t * mxdot (g *m M) (g *m M)))%:E)%E).
  apply: ge0_le_integral => //.
    by move=> g _; apply: integral_ge0 => x _; exact: G0.
  move=> g _; pose c (i : 'I_n) := s * (g *m M) 0 i.
  have hc x : mxdot g (w x) = 1 * \sum_i c i * X x i.
    rewrite mul1r Gform /c /b.
    under eq_bigr do rewrite mulr_sumr mulr_sumr.
    rewrite exchange_big /=; apply: eq_bigr => i _.
    rewrite mxE mulr_sumr mulr_suml; apply: eq_bigr => j _.
    by rewrite /M !mxE; ring.
  under eq_integral => x _ do rewrite /G /= hc.
  apply: le_trans (hoeffding c 1) _.
  rewrite lee_fin ler_expR le_eqVlt; apply/orP; left; apply/eqP.
  rewrite /c; under eq_bigr do rewrite exprMn expr2 hs.
  rewrite mulr_sumr [in RHS]/mxdot big_ord1 [in RHS]mulr_sumr.
  by apply: eq_bigr => i _; rewrite /t; ring.
(* the Gaussian chaos *)
have oM : opnorm M ^+ 2 <= opnorm A ^+ 2.
  have := opnorm_hw_mask S A; have := opnorm_ge0 M; rewrite -/M; nra.
have lK : 0 <= l ^+ 2 * K ^+ 4 by rewrite mulr_ge0 ?sqr_ge0.
have M4 : 4 * t * opnorm M ^+ 2 <= 1.
  apply: le_trans hl; have := ler_wpM2l lK oM; rewrite /t; lra.
apply: le_trans (gauss_chaos_mgf t0 M4) _.
rewrite lee_fin ler_expR /t.
have := ler_wpM2l lK (mxdot_hw_mask S A); rewrite -/M; lra.
Qed.

(* The off-diagonal part \sum_(i != j) a_ij X_i X_j. *)
Definition hw_offdiag (A : 'M[R]_n) (x : n.-tuple T) : R :=
  \sum_i \sum_j (i != j)%:R * (A i j * (X x i * X x j)).

Let mdec (S : {set 'I_n}) (A : 'M[R]_n) :
  measurable_fun [set: n.-tuple T] (hw_decoupled S A).
Proof.
rewrite /hw_decoupled; apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM => //; apply: measurable_funM => //;
  exact: measurable_funM.
Qed.

Let moff (A : 'M[R]_n) : measurable_fun [set: n.-tuple T] (hw_offdiag A).
Proof.
rewrite /hw_offdiag; apply: measurable_sum => i; apply: measurable_sum => j.
by apply: measurable_funM => //; apply: measurable_funM => //;
  exact: measurable_funM.
Qed.

(* Decoupling: average the decoupled forms over the sets S. *)
Theorem hw_offdiag_mgf (A : 'M[R]_n) (l : R) :
  1152 * l ^+ 2 * K ^+ 4 * opnorm A ^+ 2 <= 1 ->
  (\int[P]_x (expR (l * hw_offdiag A x))%:E <=
   (expR (432 * l ^+ 2 * K ^+ 4 * mxdot A A))%:E)%E.
Proof.
move=> hl; set B := 432 * l ^+ 2 * K ^+ 4 * mxdot A A.
have hS (S : {set 'I_n}) :
    (\int[P]_x (expR (4 * l * hw_decoupled S A x))%:E <= (expR B)%:E)%E.
  have e1 : 72 * (4 * l) ^+ 2 * K ^+ 4 * opnorm A ^+ 2 =
      1152 * l ^+ 2 * K ^+ 4 * opnorm A ^+ 2 by ring.
  have e2 : 27 * (4 * l) ^+ 2 * K ^+ 4 * mxdot A A = B by rewrite /B; ring.
  by have := @hw_decoupled_mgf S A (4 * l); rewrite e1 e2; apply.
set N := #|{set 'I_n}|.
have N0 : (0 < N)%N by rewrite /N card_set_ord expn_gt0.
have Ni : 0 <= N%:R^-1 :> R by rewrite invr_ge0 ler0n.
have hpt x : expR (l * hw_offdiag A x) <=
    N%:R^-1 * \sum_(S : {set 'I_n}) expR (4 * l * hw_decoupled S A x).
  have e : l * hw_offdiag A x =
      N%:R^-1 * \sum_(S : {set 'I_n}) (4 * l * hw_decoupled S A x).
    rewrite /hw_offdiag (offdiag_decouple (fun i j => A i j * (X x i * X x j))).
    by rewrite /N card_set_ord -mulr_sumr /hw_decoupled; ring.
  by rewrite e; exact: expR_avg_le.
have mE (S : {set 'I_n}) : measurable_fun [set: n.-tuple T]
    (fun x => expR (4 * l * hw_decoupled S A x)).
  by apply: measurableT_comp => //; apply: measurable_funM.
apply: (@le_trans _ _ (\int[P]_x (N%:R^-1 *
    \sum_(S : {set 'I_n}) expR (4 * l * hw_decoupled S A x))%:E)%E).
  apply: ge0_le_integral => //.
  - apply/measurable_EFinP; apply: measurableT_comp => //.
    by apply: measurable_funM.
  - apply/measurable_EFinP; apply: measurable_funM => //.
    by apply: measurable_sum => S; exact: mE.
  by move=> x _; rewrite lee_fin hpt.
by apply: (ge0_integral_avg N0 mE) => // S x; exact: expR_ge0.
Qed.

End hanson_wright.

