From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Rademacher averages, symmetrization and bounded differences              *)
(*                                                                            *)
(* Rademacher signs are written as a finite average over the 2^n sign         *)
(* vectors, not as a measure. For independent random elements X_1, ..., X_n   *)
(* (tuple_prod) and a finite class of functions f_i, the classical tools of   *)
(* empirical process theory.                                                  *)
(*                                                                            *)
(* Main results to prove (stage 1 of phase 5; names come with the proofs):    *)
(* - (exp u + exp (-u)) / 2 <= exp (u^2 / 2); hence Hoeffding's bound for     *)
(*   Rademacher sums: the average over signs of exp (sum_k eps_k a_k) is at   *)
(*   most exp (sum_k a_k^2 / 2).                                              *)
(* - Hoeffding's lemma, with the constant 1/2: for a measurable G with        *)
(*   values in an interval of length c, E exp (t (G - E G)) <=                *)
(*   exp (t^2 c^2 / 2).                                                       *)
(* - McDiarmid's bounded differences inequality: if F is measurable on        *)
(*   n.-tuple T and changing coordinate k changes F by at most c_k, then for  *)
(*   s >= 0, P(F >= E F + s) and P(F <= E F - s) are at most                  *)
(*   exp (- s^2 / (2 sum_k c_k^2)).                                           *)
(* - If g_k maps the law nu_k to mu_k, then x |-> (g_k (x_k))_k maps          *)
(*   tuple_prod nu n to tuple_prod mu n, for the integrals of bounded         *)
(*   measurable functions.                                                    *)
(* - Symmetrization (Gine-Zinn): for a finite class of bounded measurable     *)
(*   f_i,                                                                     *)
(*     E max_i |sum_k (f_i(X_k) - E f_i(X_k))|                                *)
(*       <= 2 E (rademacher_mean (max_i |sum_k eps_k f_i(X_k)|)).             *)
(* - Contraction (Ledoux-Talagrand): for a finite nonempty class of vectors   *)
(*   t_i of R^n and L-Lipschitz phi_k with phi_k(0) = 0,                      *)
(*     rademacher_mean (max_i |sum_k eps_k phi_k(t_ik)|)                      *)
(*       <= 2 L rademacher_mean (max_i |sum_k eps_k t_ik|),                   *)
(*   from the same inequality without absolute values and without the         *)
(*   factor 2, proved one coordinate at a time.                               *)
(* - rademacher_mean |sum_k eps_k| <= sqrt n.                                 *)
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
