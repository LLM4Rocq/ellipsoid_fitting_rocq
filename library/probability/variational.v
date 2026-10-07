From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.

(**md**************************************************************************)
(* # A scalar variational problem for a law on the line                       *)
(*                                                                            *)
(* For a law mu on the line with a finite second moment, the upper partial    *)
(* moments m(w) = E (X - w)_+ and s(w) = E (X - w)_+^2 solve the variational  *)
(* problem of Koehler and Sohn (arXiv 2608.27372, Lemmas 5.7 and 5.8): for    *)
(* c > -1 and z real, the equation w + z = c m(w) has a unique solution w,    *)
(* and                                                                        *)
(*   sup { (E (X + z) f(X))_+^2 / (E f(X)^2 + c (E f(X))^2) :                 *)
(*         f >= 0, E f(X)^2 < oo, E f(X) > 0 }  =  s(w) + c m(w)^2,           *)
(* attained at f(x) = (x - w)_+ when the right-hand side is positive.         *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs):    *)
(* - Regularity: 0 <= m(w1) - m(w2) <= w2 - w1 for w1 <= w2;                  *)
(*   E X - w <= m(w); m(w) <= E X^2 / (4 w) for w > 0, so m(w) -> 0 as        *)
(*   w -> +oo; |s(w + h) - s(w) + 2 h m(w)| <= h^2, so s is differentiable    *)
(*   with s' = -2 m.                                                          *)
(* - Lemma 5.7, first part: for c > -1, w = upper_cutoff mu c z satisfies     *)
(*   w + z = c m(w), it is the only solution, and w' + z <= c m(w') if and    *)
(*   only if w' <= w; moreover, for w1 <= w2,                                 *)
(*   (w2 - c m(w2)) - (w1 - c m(w1)) >= min(1, 1 + c) (w2 - w1).              *)
(* - The energy E = s + c m^2 is strictly decreasing where m > 0: for c > -1  *)
(*   and w1 <= w2, E(w1) - E(w2) >= 2 min(1, 1 + c) m(w2) (w2 - w1).          *)
(* - Lemma 5.7: for c > -1 and every measurable f >= 0 with f^2 integrable,   *)
(*   (E (X + z) f(X))_+^2 <= upper_value mu c z (E f(X)^2 + c (E f(X))^2);    *)
(*   for p(x) = (x - w)_+, with w the cutoff,                                 *)
(*   E (X + z) p(X) = E p(X)^2 + c (E p(X))^2 = upper_value mu c z; hence     *)
(*   the supremum above equals upper_value mu c z.                            *)
(* - z |-> upper_value mu c z is nondecreasing, and strictly increasing       *)
(*   where it is positive.                                                    *)
(* - Lemma 5.8, in a quantitative form: for laws mu1, mu2 with finite second  *)
(*   moments, c > -1, w2 = upper_cutoff mu2 c z and                           *)
(*   D = |m_1(w2) - m_2(w2)|, the cutoff w1 of mu1 satisfies                  *)
(*   |w1 - w2| <= delta := |c| D / min(1, 1 + c), and                         *)
(*   |upper_value mu1 c z - upper_value mu2 c z| <= |s_1(w2) - s_2(w2)|       *)
(*     + |c| |m_1(w2)^2 - m_2(w2)^2| + 2 (1 + |c|) (m_1(w2) + delta) delta.   *)
(*   Only the values at the single point w2 enter. Hence, if m_{mu_n} and     *)
(*   s_{mu_n} converge to m_mu and s_mu at the cutoff of mu, the cutoffs and  *)
(*   the values of mu_n converge to those of mu.                              *)
(* - Symmetric laws (the scalar part of Lemma 5.9): if mu is invariant under  *)
(*   x |-> -x and E X^2 = v, then m(-w) = m(w) + w and                        *)
(*   s(-w) + s(w) = v + w^2; for c > -1, c' = -c / (1 + c) and                *)
(*   z' = -z / (1 + c), upper_cutoff mu c' z' = - upper_cutoff mu c z and     *)
(*   upper_value mu c z + upper_value mu c' z' = v + z^2 / (1 + c).           *)
(*                                                                            *)
(* Laws on the line are probabilities on measurableTypeR R, as in             *)
(* fourier/charfun.v. A finite second moment is the integrability of x^2.     *)
(*                                                                            *)
(* ```                                                                        *)
(*  upper_moment mu k w == \int[mu]_x ((x - w)_+)^k, the upper partial moment *)
(*                         of order k at w: m(w) for k = 1, s(w) for k = 2    *)
(*  upper_energy mu c w == s(w) + c m(w)^2                                    *)
(*  upper_cutoff mu c z == sup {w | w + z <= c m(w)}, the solution of         *)
(*                         w + z = c m(w) when c > -1                         *)
(*   upper_value mu c z == upper_energy mu c (upper_cutoff mu c z), the value *)
(*                         of the variational problem                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section upper_moments.
Context {R : realType} (mu : probability (measurableTypeR R) R).

Definition upper_moment (k : nat) (w : R) : R :=
  \int[mu]_x (Num.max ((x : R) - w) 0 ^+ k).

Definition upper_energy (c w : R) : R :=
  upper_moment 2 w + c * upper_moment 1 w ^+ 2.

Definition upper_cutoff (c z : R) : R :=
  sup [set w : R | w + z <= c * upper_moment 1 w].

Definition upper_value (c z : R) : R := upper_energy c (upper_cutoff c z).

End upper_moments.
