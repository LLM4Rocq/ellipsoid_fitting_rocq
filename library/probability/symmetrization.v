From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Rademacher averages, contraction and symmetrization                      *)
(*                                                                            *)
(* Rademacher signs are written as a finite average over the 2^n sign         *)
(* vectors, not as a measure. For independent random elements X_1, ..., X_n   *)
(* (tuple_prod) and a finite class of functions f_j, the tools of empirical   *)
(* process theory that the small-ball method needs, for expectations only:    *)
(* no concentration inequality is used.                                       *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs):    *)
(* - rademacher_mean is linear and monotone, and the average over signs of    *)
(*   |sum_k eps_k a_k| is at most (sum_k a_k^2)^(1/2) (Cauchy-Schwarz).       *)
(* - Contraction (Ledoux-Talagrand): for a finite class of vectors t_j of     *)
(*   R^n and L-Lipschitz phi_k with phi_k(0) = 0,                             *)
(*     rademacher_mean (max_j |sum_k eps_k phi_k(t_jk)|)                      *)
(*       <= 2 L rademacher_mean (max_j |sum_k eps_k t_jk|),                   *)
(*   from the same inequality without absolute values and without the         *)
(*   factor 2, proved one coordinate at a time.                               *)
(* - Symmetrization (Gine-Zinn): for X of law tuple_prod mu n and a finite    *)
(*   class of bounded measurable f_j,                                         *)
(*     E max_j |sum_k (f_j(X_k) - E f_j(X_k))|                                *)
(*       <= 2 E (rademacher_mean (max_j |sum_k eps_k f_j(X_k)|)).             *)
(*   Proof: an independent copy X' as the second block of a tuple of n + n    *)
(*   coordinates (ge0_integral_tuple_prod_cat of tuple_rows.v); Jensen's      *)
(*   inequality one coordinate of X' at a time and the exchange of X_k and    *)
(*   X'_k one k at a time, both by Fubini at one coordinate                   *)
(*   (ge0_integral_tuple_prod_set of efron_stein.v).                          *)
(*                                                                            *)
(* ```                                                                        *)
(*        rademacher b == the sign 1 if b, -1 otherwise                       *)
(* rademacher_mean n F == 2^-n sum_{s : n.-tuple bool} F s, the expectation   *)
(*                        of F over n independent Rademacher signs            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section rademacher.
Context {R : realType}.

Definition rademacher (b : bool) : R := if b then 1 else -1.

Definition rademacher_mean n (F : n.-tuple bool -> R) : R :=
  (2 ^+ n)^-1 * \sum_(s : n.-tuple bool) F s.

End rademacher.
