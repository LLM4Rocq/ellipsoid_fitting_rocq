From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum zmodp.
From mathcomp Require Import matrix reals.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.
From GaussianAnalysis.combinatorics Require Import expander.
From GaussianApplications Require Import PsdRankDefinitions PsdRankStatement.
From GaussianApplications.PsdRank Require Import Model Main Realization.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the main theorem from its parts   *)
(*                                                                            *)
(* Item A6 of phase 14 (AGENTS.md, section Phase 14; the plan                 *)
(* notes/phase14-plan.md, section 6.3): the assembly of the main theorem of   *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/introduction.tex, lines 37-44, proved in                   *)
(* source/sections/matching.tex, lines 41-218), a Rocq formalization of the   *)
(* credited argument. The file follows no Lean module.                        *)
(*                                                                            *)
(* psd_rank_from_parts: psd_rank_statement follows from two hypotheses, Props *)
(* of this file:                                                              *)
(* - local_averaging_hyp, the local averaging of a cell at d = 100 (item A2,  *)
(*   local-averaging.tex, lines 64-92): laws of the cell with the five        *)
(*   conditions of smoothing_hyps, a contraction theta k with theta k -> 0    *)
(*   along even k, and the support of the restrictions inside cell_support    *)
(*   of the frame (PsdRank/Model.v);                                          *)
(* - parity_hyp, the parity functional (item A4, parity.tex, lines 131-150):  *)
(*   parity_functional at block degree (l + l) %/ 1000 for f_eps of the       *)
(*   frame, when the graph of the 100 permutations sigma j expands.           *)
(* The proof applies psd_rank_from_cell_data of PsdRank/Main.v at a = 99 and  *)
(* builds its cell data from the two hypotheses, from expander of             *)
(* library/combinatorics/expander.v (item L7: for every l >= 1, 100           *)
(* permutations of 'I_l whose graph expands) and from realization of          *)
(* PsdRank/Realization.v (item A5), with the charges 1 at the first cell and  *)
(* 0 elsewhere, of total 1.                                                   *)
(*                                                                            *)
(* Departures of phase 14 (the plan, section 2):                              *)
(* - departure 1: T = 1000, so the block degree of the parity functional is   *)
(*   D = t %/ 1000 for an even number t >= 1000 of cells;                     *)
(* - departure 2: the conditions on the cell size k are those of the lemmas   *)
(*   of the local averaging (k even, 6 <= k, 2 d <= k, k0 <= k) and of the    *)
(*   realization (k even, 2 d <= k). This file chooses                        *)
(*   k = 2 max(200, k0, k1), where theta k <= 1 / c for even k >= k1.         *)
(*                                                                            *)
(* The constants: L = 2^99, lambda = (64 L^4)^1000 and                        *)
(* c = L lambda^2 2^(L - 1), so that c theta k <= 1, which is the condition   *)
(* of psd_rank_from_cell_data; then K = 2 k. They stay symbolic in the proof. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The local averaging (A2) in the form that the final step uses: for even k
   with 6 <= k, 2 d <= k (d = 100) and k0 <= k, local laws of a cell with the
   contraction theta k, theta k -> 0, and the support of the restrictions
   inside cell_support. *)
Definition local_averaging_hyp : Prop :=
  forall R : realType, exists (k0 : nat) (theta : nat -> R),
  [/\ forall k, 0 <= theta k,
      forall e : R, 0 < e -> exists k1, forall k, ~~ odd k -> (k1 <= k)%N ->
        theta k <= e &
      forall k, ~~ odd k -> (6 <= k)%N -> (2 * 100 <= k)%N -> (k0 <= k)%N ->
      exists (cmu : 'F_2 -> {set 'I_k} -> R) (cnu : {perm 'I_k} -> R)
             (cpi : 'F_2 -> {perm 'I_k} -> 'rV['F_2]_99 -> {set 'I_k} -> R),
      (forall b : 'F_2,
       [/\ prob_vec (cmu b), prob_vec cnu, forall m y, prob_vec (cpi b m y),
           forall y x, \sum_m cnu m * cpi b m y x = cmu b x &
           forall y (g : {set 'I_k} -> R),
             \sum_m cnu m * (\sum_x cpi b m y x * g x - \sum_x cmu b x * g x) ^+ 2
               <= theta k * \sum_x cmu b x * g x ^+ 2]) /\
      (forall b m y x, 0 < cpi b m y x -> cell_support b m y x)].

(* The parity functional (A4), with departure 1: D = t %/ 1000, 1000 <= t. *)
Definition parity_hyp : Prop :=
  forall (R : realType) (l : nat) (sigma : 'I_100 -> {perm 'I_l})
         (b : 'rV['F_2]_(l + l)) (eps : R),
  (forall W : {set 'I_(l + l)},
     (minn #|W| (l + l - #|W|) <= #|perm_cut sigma W|)%N) ->
  (1000 <= l + l)%N ->
  parity_functional ((l + l) %/ 1000) eps (f_eps sigma b eps).

Theorem psd_rank_from_parts :
  local_averaging_hyp -> parity_hyp -> psd_rank_statement.
Proof.
move=> hA2 hA4; apply: (@psd_rank_from_cell_data 99) => R.
have [k0 [theta [th0 thlim hcell]]] := hA2 R.
(* L = 2^99, lambda = (64 L^4)^1000 and c = L lambda^2 2^(L - 1) stay
   symbolic: their bodies are cleared once their facts are proved. *)
set L := (2 ^ 99)%N.
pose lambda : R := (64 * L%:R ^+ 4) ^+ 1000.
pose c : R := L%:R * lambda ^+ 2 * 2 ^+ L.-1.
have L1 : (1 <= L)%N by rewrite /L expn_gt0.
have lam1 : 1 <= lambda.
  rewrite /lambda exprn_ege1 // mulr_ege1 //; first by rewrite ler1n.
  by rewrite exprn_ege1 // ler1n.
have lam0 : 0 < lambda := lt_le_trans ltr01 lam1.
have L0R : (0 : R) < L%:R by rewrite ltr0n; exact: L1.
have p0 : (0 : R) < 2 ^+ L.-1 by apply: exprn_gt0; exact: (@ltr0Sn R 1).
have c0 : 0 < c.
  rewrite /c; apply: mulr_gt0; last exact: p0.
  apply: mulr_gt0; first exact: L0R.
  exact: (exprn_gt0 2 lam0).
have lamE : lambda = (64 * L%:R ^+ 4) ^+ 1000 by [].
have cE : c = L%:R * lambda ^+ 2 * 2 ^+ L.-1 := erefl.
clearbody c lambda; clearbody L.
(* k: even, at least 200 = 2 d, k0 and k1, where theta k <= 1 / c. *)
have ci0 : 0 < c^-1 by rewrite invr_gt0.
have [k1 hk1] := thlim c^-1 ci0.
pose k := (maxn 200 (maxn k0 k1)).*2.
have kge (q : nat) : (q <= maxn 200 (maxn k0 k1))%N -> (q <= k)%N.
  by move=> h; rewrite /k -addnn (leq_trans h (leq_addr _ _)).
have k200 : (2 * 100 <= k)%N by apply: kge; exact: leq_maxl.
have ek : ~~ odd k by rewrite /k odd_double.
have kk0 : (k0 <= k)%N.
  by apply: kge; rewrite (leq_trans _ (leq_maxr _ _)) // leq_maxl.
have kk1 : (k1 <= k)%N.
  by apply: kge; rewrite (leq_trans _ (leq_maxr _ _)) // leq_maxr.
have k6 : (6 <= k)%N by apply: leq_trans k200.
exists k, 1000%N, (theta k), lambda; split.
- by apply/andP; split; [exact: leq_trans _ k6|].
- exact: lam1.
- rewrite -cE -(mulrV (unitf_gt0 c0)); apply: ler_wpM2l.
    exact: ltW c0.
  exact: hk1.
- by rewrite lamE.
move=> rho rho01 n t en et t1000 ktn nkt.
have [cmu [cnu [cpi [hlaw hsupp]]]] := hcell k ek k6 k200 kk0.
pose l := t./2.
have tl : t = (l + l)%N.
  by rewrite addnn /l -[t in LHS](odd_double_half t) (negbTE et) add0n.
rewrite tl in ktn t1000 *.
have l0 : (0 < l)%N by rewrite lt0n; apply/eqP => l0; move: t1000; rewrite l0.
have [sigma hsig] := expander l0.
(* the charges: 1 at the first cell, 0 elsewhere *)
have t0 : (0 < l + l)%N by rewrite addn_gt0 l0.
pose i0 : 'I_(l + l) := Ordinal t0.
pose b : 'rV['F_2]_(l + l) := \row_i ((i == i0)%:R : 'F_2).
have hb : \sum_(i < l + l) b 0 i = 1.
  rewrite (bigD1 i0) //= mxE eqxx big1 ?addr0 // => i ni0.
  by rewrite mxE (negbTE ni0).
have [U [Mm hreal]] := @realization R n k l sigma b en ek k200 ktn hb.
exists {set 'I_k}, {perm 'I_k}.
exists (fun i => cmu (b 0 i)), (fun _ => cnu), (fun i => cpi (b 0 i)), U, Mm.
exists (f_eps sigma b (1 - rho)); split.
- by split=> [i|i|i m y|i y x|i y g]; case: (hlaw (b 0 i)).
- move=> m x y _ hpi; apply: hreal => i; apply: hsupp.
  have F0 j : 0 <= cpi (b 0 j) (tnth m j) (row j y) (tnth x j).
    case: (hlaw (b 0 j)) => _ _ hp _ _.
    by have [h _] := hp (tnth m j) (row j y); exact: h.
  rewrite lt_def F0 andbT; apply/eqP => e0; move: hpi.
  by rewrite (bigD1 i) //= e0 mul0r ltxx.
- exact: (hA4 R l sigma b (1 - rho) hsig t1000).
Qed.
