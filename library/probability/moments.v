From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral hoelder probability.
From mathcomp Require Import arithmetic_tactic field_tactic.

(**md**************************************************************************)
(* # Moment inequalities                                                      *)
(*                                                                            *)
(* Lower bounds on probabilities from the first two moments of a real random  *)
(* variable X on a probability space P.                                       *)
(*                                                                            *)
(* - paley_zygmund: for 0 <= theta < E X,                                     *)
(*   P(theta <= X) >= (E X - theta)^2 / E X^2, without sign condition on X.   *)
(* - paley_zygmund_sqr: the same applied to X^2, a small-ball estimate from   *)
(*   the second and fourth moments: for 0 <= t < 1,                           *)
(*   P(t E X^2 <= X^2) >= (1 - t)^2 (E X^2)^2 / E X^4.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section paley_zygmund.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma paley_zygmund_point (z theta s : R) : 0 <= theta -> 0 <= s ->
  2 * s * z <= 2 * s * theta + s ^+ 2 * z ^+ 2 + ((theta <= z)%R)%:R.
Proof.
move=> th0 s0; have [thz|zth] := leP theta z; rewrite ?mulr1n ?mulr0n.
  have := sqr_ge0 (s * z - 1); nra.
have := sqr_ge0 (s * z); nra.
Qed.

Theorem paley_zygmund (X : T -> R) (theta : R) :
  X \in Lfun P 2%:E -> 0 <= theta -> (theta%:E < 'E_P[X])%E ->
  (((fine 'E_P[X] - theta) ^+ 2 / fine 'E_P[X ^+ 2])%:E <=
    P [set x | (theta <= X x)%R])%E.
Proof.
move=> X2 th0 thE.
have X1 : X \in Lfun P 1 := Lfun_subset12 (fin_num_measure P _ measurableT) X2.
have XX1 : X ^+ 2 \in Lfun P 1.
  have := Lfun2_mul_Lfun1 X2 X2.
  by congr (_ \in _); apply/funext => x; rewrite /= expr2.
have mX : measurable_fun setT X by have := sub_Lfun_mfun X1; rewrite inE.
set A := [set x | (theta <= X x)%R].
have mA : measurable A.
  rewrite -[A]setTI.
  exact: (measurable_fun_ler (measurable_cst theta) mX measurableT).
set m := fine 'E_P[X]; set M := fine 'E_P[X ^+ 2].
have Em : ('E_P[X] = m%:E)%E by rewrite fineK ?expectation_fin_num.
have EM : ('E_P[X ^+ 2] = M%:E)%E by rewrite fineK ?expectation_fin_num.
have M0 : 0 <= M.
  by rewrite -lee_fin -EM; apply: expectation_ge0 => x; rewrite /= sqr_ge0.
have mth : theta < m by rewrite -lte_fin -Em.
set s := (m - theta) / M.
have s0 : 0 <= s by rewrite divr_ge0 // subr_ge0 ltW.
have A1 : \1_A \in Lfun P 1 by apply/Lfun1_integrable; exact: integrable_indic.
have L1 : (2 * s) \o* X \in Lfun P 1 by apply: Lfun_scale.
have C1 : cst (2 * s * theta) \+ (s ^+ 2) \o* (X ^+ 2) \in Lfun P 1.
  by rewrite rpredD ?Lfun_cst // Lfun_scale.
have R1 : cst (2 * s * theta) \+ (s ^+ 2) \o* (X ^+ 2) \+ \1_A \in Lfun P 1.
  by rewrite rpredD.
have : ('E_P[((2 * s) \o* X)%R] <=
    'E_P[(cst (2 * s * theta) \+ (s ^+ 2) \o* (X ^+ 2) \+ \1_A)%R])%E.
  rewrite unlock; apply: le_integral => //.
  - by move/Lfun1_integrable: L1.
  - by move/Lfun1_integrable: R1.
  move=> x _; rewrite lee_fin /= indicE.
  have -> : (x \in A) = (theta <= X x) by apply/idP/idP => [/set_mem|/mem_set].
  have -> : (X ^+ 2) x = X x ^+ 2 by rewrite /= expr2.
  by rewrite mulrC [_ * s ^+ 2]mulrC paley_zygmund_point.
rewrite expectationZl // expectationD // expectationD ?Lfun_cst ?Lfun_scale //.
rewrite expectation_cst expectationZl // expectation_indic // Em EM.
have PA : P A = (fine (P A))%:E by rewrite fineK // fin_num_measure.
rewrite PA -!EFinM -!EFinD !lee_fin => H.
have -> : (m - theta) ^+ 2 / M = 2 * s * m - (2 * s * theta + s ^+ 2 * M).
  rewrite /s; have [->|Mn0] := eqVneq M 0.
    by rewrite !invr0 !(mulr0, mul0r, addr0, subr0, expr0n).
  by field.
by rewrite lerBlDl.
Qed.

End paley_zygmund.
