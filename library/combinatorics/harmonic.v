From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals exp.

(**md**************************************************************************)
(* # A bound on the harmonic numbers                                          *)
(*                                                                            *)
(* The n-th harmonic number H_n = sum_(i < n) 1 / (i + 1) is at most 1 + ln n *)
(* for every n >= 1, over any realType.                                       *)
(*                                                                            *)
(* - harmonic_ln: for every n > 0, sum_(i < n) 1 / (i + 1) <= 1 + ln n in R.  *)
(*   The proof applies ln (1 + x) <= x (le_ln1Dx of exp.v) at x =             *)
(*   -1 / (i + 1), which gives 1 / (i + 1) <= ln (i + 1) - ln i for i >= 1,   *)
(*   and telescopes.                                                          *)
(*                                                                            *)
(* This is a Rocq formalization of the harmonic bound that the trace estimate *)
(* of the lemma on local averaging of 'Exponential PSD rank of positively     *)
(* shifted matching matrices' uses without proof (family 126 of the OpenAI    *)
(* math collection, revision 1581d4cbd, source/sections/local-averaging.tex,  *)
(* lines 177-185: the sum of 1/j for j from 1 to g* + 1 is O(log(h + 2))). It *)
(* follows no Lean module of the collection. MathComp-Analysis defines the    *)
(* terms of the harmonic series, harmonic in sequences.v, not their partial   *)
(* sums; the statement writes the sum.                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section harmonic.
Variable R : realType.

(* 1 / (n + 1) <= ln (n + 1) - ln n for n > 0. *)
Local Lemma inv_le_ln_step (n : nat) : (0 < n)%N ->
  (n.+1%:R : R)^-1 <= ln (n.+1%:R : R) - ln (n%:R : R).
Proof.
move=> n0.
have hlt : (n.+1%:R : R)^-1 < 1 by rewrite invf_lt1 ?ltr0n // ltr1n ltnS.
have hx : -1 < - (n.+1%:R : R)^-1 by rewrite ltrN2.
have := le_ln1Dx hx.
have -> : 1 - (n.+1%:R : R)^-1 = n%:R / n.+1%:R.
  by rewrite -{1}(@divff _ n.+1%:R) ?pnatr_eq0 // -{2}[n.+1%:R^-1]mul1r
    -mulrBl -[1]/(1%:R) -natrB // subSS subn0.
rewrite ln_div ?posrE ?ltr0n // => h.
by rewrite -lerN2 opprB.
Qed.

Lemma harmonic_ln (n : nat) : (0 < n)%N ->
  \sum_(i < n) (i.+1%:R)^-1 <= 1 + ln (n%:R : R).
Proof.
case: n => // n _; elim: n => [|n ih].
  by rewrite big_ord1 ln1 addr0 invr1.
rewrite big_ord_recr /=.
apply: (Order.POrderTheory.le_trans (lerD ih (inv_le_ln_step (ltn0Sn n)))).
by rewrite -addrA [ln n.+1%:R + _]addrC subrK.
Qed.

End harmonic.

(* 1 + 1/2 + 1/3 + 1/4 <= 1 + ln 4. *)
Example harmonic_ln_four (R : realType) :
  \sum_(i < 4) (i.+1%:R : R)^-1 <= 1 + ln (4%:R : R).
Proof. exact: harmonic_ln. Qed.
