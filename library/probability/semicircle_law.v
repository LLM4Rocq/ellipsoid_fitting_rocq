From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp trigo.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.

(**md**************************************************************************)
(* # The semicircle law                                                       *)
(*                                                                            *)
(* The semicircle law of radius r > 0 has the density                         *)
(* 2 / (pi r^2) sqrt (r^2 - x^2) on [-r, r] with respect to Lebesgue measure. *)
(* Its variance is r^2 / 4. Wigner's semicircle law for a GOE matrix scaled   *)
(* by 1 / sqrt d has radius 2, and the law nu of Koehler and Sohn (arXiv      *)
(* 2608.27372, lines 345-349), of density sqrt (2 - x^2) / pi, has radius     *)
(* sqrt 2. As MathComp-Analysis does for normal_pdf m 0, the density at       *)
(* r = 0 is the indicator of [0, 1], so that semicircle_prob r is a           *)
(* probability for every r.                                                   *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs),    *)
(* for r > 0:                                                                 *)
(* - semicircle_prob r is a probability on measurableTypeR R; it gives the    *)
(*   complement of [-r, r] measure 0 and every half-line ]a, +oo[ with a < r  *)
(*   a positive measure.                                                      *)
(* - Integrating against semicircle_prob r is integrating against Lebesgue    *)
(*   measure with the density semicircle_pdf r, for nonnegative or            *)
(*   integrable functions.                                                    *)
(* - The law is invariant under x |-> -x, so the integral of f(-x) is that    *)
(*   of f(x).                                                                 *)
(* - The density has integral one, by the substitution x = r sin t.           *)
(* - E X^(k+2) = (k + 1) r^2 / (k + 4) E X^k, by integration by parts         *)
(*   against (r^2 - x^2)^(3/2); hence E X = 0, E X^2 = r^2 / 4, the odd       *)
(*   moments vanish, and at r = 2 the even moments are the Catalan numbers.   *)
(*                                                                            *)
(* ```                                                                        *)
(*    semicircle_pdf r x == 2 / (pi r^2) sqrt (r^2 - x^2), zero outside       *)
(*                          [-r, r] since Num.sqrt is zero on negative        *)
(*                          numbers; the indicator of [0, 1] if r = 0         *)
(*     semicircle_prob r == the measure with density semicircle_pdf r with    *)
(*                          respect to Lebesgue measure                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section semicircle_density.
Context {R : realType}.

Definition semicircle_pdf (r x : R) : R :=
  if r == 0 then \1_`[0, 1] x
  else 2 / (pi * r ^+ 2) * Num.sqrt (r ^+ 2 - x ^+ 2).

Definition semicircle_prob (r : R) : set (measurableTypeR R) -> \bar R :=
  fun V => (\int[lebesgue_measure]_(x in V) (semicircle_pdf r x)%:E)%E.

End semicircle_density.
