From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets reals ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.

(**md**************************************************************************)
(* # Nets in Euclidean spaces                                                 *)
(*                                                                            *)
(* A finite eps-net of a set S of column vectors is a finite sequence N such  *)
(* that every point of S lies within Euclidean distance eps of a point of N.  *)
(* The operator norm of a matrix is controlled by its values on a net of the  *)
(* unit ball (opnorm_net, opnorm_net_bilinear, opnorm_net_sym).               *)
(*                                                                            *)
(* ```                                                                        *)
(*      is_net S N eps == every x in S has a point y of N with                *)
(*                        frobenius (x - y) <= eps                            *)
(*        unit_ball n == the closed unit ball [set x | frobenius x <= 1] of   *)
(*                        'cV[R]_n                                            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section nets.
Variable R : realType.
Implicit Types m n : nat.

Definition is_net n (S : set 'cV[R]_n) (N : seq 'cV[R]_n) (eps : R) :=
  forall x, S x -> exists2 y, y \in N & frobenius (x - y) <= eps.

Definition unit_ball n : set 'cV[R]_n := [set x | frobenius x <= 1].

Lemma unit_ball0 n : @unit_ball n 0.
Proof. by rewrite /unit_ball /= frobenius0 ler01. Qed.

Lemma is_net_sub n (S T : set 'cV[R]_n) N eps :
  S `<=` T -> is_net T N eps -> is_net S N eps.
Proof. by move=> ST TN x /ST/TN. Qed.

Lemma is_net_le n (S : set 'cV[R]_n) N eps eps' :
  eps <= eps' -> is_net S N eps -> is_net S N eps'.
Proof. by move=> ee SN x /SN[y yN xy]; exists y => //; exact: le_trans ee. Qed.

(* The values of A on a net of the unit ball control its operator norm. *)
Lemma opnorm_net m n (A : 'M[R]_(m, n)) (N : seq 'cV[R]_n) (eps b : R) :
  0 <= eps < 1 -> is_net (@unit_ball n) N eps ->
  (forall y, y \in N -> frobenius (A *m y) <= b) ->
  opnorm A <= b / (1 - eps).
Proof.
move=> /andP[e0 e1] AN Ab; have e1' : 0 < 1 - eps by rewrite subr_gt0.
have : opnorm A <= b + opnorm A * eps.
  apply: opnorm_le => x /AN[y yN xy].
  rewrite -[x](subrK y) mulmxDr addrC (le_trans (frobeniusD _ _)) // lerD ?Ab //.
  by rewrite (le_trans (frobenius_mulmx_opnorm _ _)) // ler_wpM2l ?opnorm_ge0.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

Lemma mxdot_net_bound m n (A : 'M[R]_(m, n)) (y u : 'cV[R]_m) (x v : 'cV[R]_n) :
  frobenius y <= 1 -> frobenius x <= 1 -> frobenius u <= 1 ->
  `|mxdot y (A *m x)| <=
    `|mxdot u (A *m v)| + opnorm A * (frobenius (y - u) + frobenius (x - v)).
Proof.
move=> y1 x1 u1.
have -> : mxdot y (A *m x) =
    mxdot u (A *m v) + mxdot (y - u) (A *m x) + mxdot u (A *m (x - v)).
  by rewrite mulmxBr mxdotBl mxdotBr; ring.
rewrite -addrA (le_trans (ler_normD _ _)) // lerD2l mulrDr.
rewrite (le_trans (ler_normD _ _)) // lerD //.
  rewrite (le_trans (mxdot_opnorm _ _ _)) // -mulrA ler_wpM2l ?opnorm_ge0 //.
  by rewrite -[leRHS]mulr1 ler_wpM2l ?frobenius_ge0.
rewrite (le_trans (mxdot_opnorm _ _ _)) // -mulrA ler_wpM2l ?opnorm_ge0 //.
by rewrite -[leRHS]mul1r ler_wpM2r ?frobenius_ge0.
Qed.

(* Bilinear values on nets of both unit balls control the operator norm. *)
Lemma opnorm_net_bilinear m n (A : 'M[R]_(m, n)) (U : seq 'cV[R]_m)
    (V : seq 'cV[R]_n) (eps b : R) :
  0 <= eps -> 2 * eps < 1 ->
  is_net (@unit_ball m) U eps -> (forall u, u \in U -> frobenius u <= 1) ->
  is_net (@unit_ball n) V eps ->
  (forall u v, u \in U -> v \in V -> `|mxdot u (A *m v)| <= b) ->
  opnorm A <= b / (1 - 2 * eps).
Proof.
move=> e0 e1 UN Ub VN Ab.
have e1' : 0 < 1 - 2 * eps by rewrite subr_gt0.
have b0 : 0 <= b.
  have [u uU _] := UN 0 (unit_ball0 m); have [v vV _] := VN 0 (unit_ball0 n).
  exact: le_trans (normr_ge0 _) (Ab u v uU vV).
have : opnorm A <= b + opnorm A * (2 * eps).
  apply: opnorm_le => x x1.
  have [Ax0|Axn0] := eqVneq (A *m x) 0.
    by rewrite Ax0 frobenius0 addr_ge0 ?mulr_ge0 ?opnorm_ge0.
  have Ax_gt0 : 0 < frobenius (A *m x) by rewrite frobenius_gt0.
  set y := (frobenius (A *m x))^-1 *: (A *m x).
  have y1 : frobenius y <= 1.
    by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
  have yE : frobenius (A *m x) = mxdot y (A *m x).
    by rewrite /y mxdotZl -frobenius_sqr expr2 mulKf ?gt_eqF.
  have [u uU yu] := UN y y1; have [v vV xv] := VN x x1.
  rewrite yE (le_trans (ler_norm _)) //.
  rewrite (le_trans (mxdot_net_bound A v y1 x1 (Ub u uU))) //.
  by rewrite lerD ?Ab // ler_wpM2l ?opnorm_ge0 // mulrDl mul1r lerD.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

Lemma form_unit_ball_le n (A : 'M[R]_n) (c : R) :
  (forall x : 'cV[R]_n, frobenius x <= 1 -> `|mxdot x (A *m x)| <= c) ->
  forall x : 'cV[R]_n, `|mxdot x (A *m x)| <= c * mxdot x x.
Proof.
move=> Ac x; have [->|x0] := eqVneq x 0; first by rewrite !mxdot0l normr0 mulr0.
have xp : 0 < frobenius x by rewrite frobenius_gt0.
set z := (frobenius x)^-1 *: x.
have z1 : frobenius z <= 1.
  by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
have := Ac z z1; rewrite /z -scalemxAr mxdotZl mxdotZr mulrA normrM.
rewrite ger0_norm ?mulr_ge0 ?invr_ge0 ?frobenius_ge0 // -invfM -expr2 frobenius_sqr.
by rewrite mulrC ler_pdivrMr ?mxdot_gt0 // mulrC.
Qed.

(* Values of the quadratic form on a net of the unit ball control the
   operator norm of a symmetric matrix. *)
Lemma opnorm_net_sym n (A : 'M[R]_n) (V : seq 'cV[R]_n) (eps b : R) :
  A \is symmetricmx -> 0 <= eps -> 2 * eps < 1 ->
  is_net (@unit_ball n) V eps -> (forall v, v \in V -> frobenius v <= 1) ->
  (forall v, v \in V -> `|mxdot v (A *m v)| <= b) ->
  opnorm A <= b / (1 - 2 * eps).
Proof.
move=> Asym e0 e1 VN Vb Ab.
have e1' : 0 < 1 - 2 * eps by rewrite subr_gt0.
have b0 : 0 <= b.
  by have [v vV _] := VN 0 (unit_ball0 n); exact: le_trans (normr_ge0 _) (Ab v vV).
have : opnorm A <= b + opnorm A * (2 * eps).
  apply/opnorm_symP => //; first by rewrite addr_ge0 ?mulr_ge0 ?opnorm_ge0.
  apply: form_unit_ball_le => x x1; have [v vV xv] := VN x x1.
  rewrite (le_trans (mxdot_net_bound A v x1 x1 (Vb v vV))) //.
  by rewrite lerD ?Ab // ler_wpM2l ?opnorm_ge0 // mulrDl mul1r lerD.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

End nets.

(* Lists of natural numbers with a bounded sum, the codes of the grid points
   of a net. *)
Section budget.

Fixpoint budget (n k : nat) : seq (seq nat) :=
  if n is n'.+1 then
    flatten [seq [seq a :: t | t <- budget n' (k - a)] | a <- iota 0 k.+1]
  else [:: [::]].

Lemma mem_budget n k (a : seq nat) :
  size a = n -> (sumn a <= k)%N -> a \in budget n k.
Proof.
elim: n k a => [|n IH] k [|x a] // sa sk.
apply/flattenP; exists [seq x :: t | t <- budget n (k - x)].
  apply/mapP; exists x => //; rewrite mem_iota /= add0n ltnS.
  exact: leq_trans (leq_addr _ _) sk.
apply/mapP; exists a => //; apply: IH; first by case: sa.
by rewrite -(leq_add2l x) subnKC // (leq_trans (leq_addr _ _) sk).
Qed.

Lemma sum_exp2_lt k : (\sum_(a < k.+1) 2 ^ (k - a) < 2 ^ k.+1)%N.
Proof.
elim: k => [|k IH]; first by rewrite big_ord1.
rewrite big_ord_recl subn0 [in X in (_ < X)%N]expnS mul2n -addnn ltn_add2l.
by under eq_bigr => a _ do rewrite lift0 subSS.
Qed.

Lemma size_budget n k : (size (budget n k) <= 2 ^ (n + k))%N.
Proof.
elim: n k => [|n IH] k; first by rewrite /= expn_gt0.
rewrite /budget -/budget size_flatten /shape -map_comp sumnE big_map.
apply: (@leq_trans (\sum_(a <- iota 0 k.+1) 2 ^ (n + (k - a)))).
  by apply: leq_sum => a _; rewrite /= size_map IH.
rewrite -[iota 0 k.+1]/(index_iota 0 k.+1) big_mkord.
under eq_bigr do rewrite expnD.
rewrite -big_distrr /= addSn expnS expnD mulnCA leq_mul2l.
by rewrite -expnS ltnW ?sum_exp2_lt ?orbT.
Qed.

End budget.
