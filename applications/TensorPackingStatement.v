From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import reals sequences exp.
From GaussianAnalysis.matrix Require Import euclidean.

(**md**************************************************************************)
(* # Tensor packing in finite dimensions: the statement                       *)
(*                                                                            *)
(* Target T2 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The statement of a Rocq formalization   *)
(* of the credited argument of Theorem 4.1, 'Tensor packing', of 'Pointwise   *)
(* convergence of fourfold ergodic averages for mixing transformations'       *)
(* (family 154 of the OpenAI math collection, revision 1581d4cbd,             *)
(* sections/04-packing.tex). The collection has no Lean version of it. This   *)
(* file holds the statement only.                                             *)
(*                                                                            *)
(* Setting. R is any realType. x_1, ..., x_m lie in the unit ball of          *)
(* 'rV[R]_n1 and y_1, ..., y_m in the unit ball of 'rV[R]_n2 (frobenius is    *)
(* the Euclidean norm of a row, mxdot the inner product). Gx and Gy are       *)
(* relations on 'I_m with at most L successors at every vertex, that contain  *)
(* every pair a != b with |<x_a, x_b>| > eta, respectively |<y_a, y_b>| >     *)
(* eta. A_1, ..., A_r are Frobenius-orthonormal in 'M[R]_(n1, n2), with r <=  *)
(* d: they span the range of an orthogonal projection P of rank r on the      *)
(* tensor product, identified with 'M[R]_(n1, n2), and |P(x_a tensor y_a)|^2  *)
(* = sum_k (x_a A_k y_a^T)^2.                                                 *)
(*                                                                            *)
(* tensor_packing_statement, for every R: there is C > 0 such that, for all   *)
(* such data with 0 < eps <= 1, d >= 1 and 0 <= eta <= eps^2 / 10^4, the      *)
(* number of indices a with sum_k (x_a A_k y_a^T)^2 >= eps^2 is at most C (1  *)
(* + L) / eps^2 exp (C eps^(-2) sqrt d ln (2 + d)).                           *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - Finite dimensions: the Hilbert spaces of the manuscript are 'rV[R]_n1    *)
(*   and 'rV[R]_n2, their tensor product is 'M[R]_(n1, n2) with the Frobenius *)
(*   inner product, and a projection of rank at most d is given by an         *)
(*   orthonormal basis of its range. The manuscript's reduction from          *)
(*   arbitrary Hilbert spaces to finite spans, and its consequence for d_m =  *)
(*   (1 + log m)^(3/2), are not part of the statement.                        *)
(* - The graphs are relations with at most L successors at every vertex, not  *)
(*   necessarily symmetric; an undirected graph of maximum degree L is one of *)
(*   them, so the statement is the manuscript's in this respect or stronger.  *)
(*   The two graphs may differ, as in the manuscript.                         *)
(* - The constant C is universal: it depends on nothing (formally, on R       *)
(*   only).                                                                   *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition tensor_packing_statement : Prop :=
  forall R : realType, exists C : R, 0 < C /\
  forall (n1 n2 m d L r : nat) (eps eta : R)
    (x : 'I_m -> 'rV[R]_n1) (y : 'I_m -> 'rV[R]_n2)
    (Gx Gy : 'I_m -> 'I_m -> bool) (A : 'I_r -> 'M[R]_(n1, n2)),
  0 < eps -> eps <= 1 -> (0 < d)%N -> 0 <= eta -> eta <= eps ^+ 2 / 10000 ->
  (forall a, frobenius (x a) <= 1) -> (forall a, frobenius (y a) <= 1) ->
  (forall a, #|[set b | Gx a b]| <= L)%N ->
  (forall a, #|[set b | Gy a b]| <= L)%N ->
  (forall a b, a != b -> eta < `|mxdot (x a) (x b)| -> Gx a b) ->
  (forall a b, a != b -> eta < `|mxdot (y a) (y b)| -> Gy a b) ->
  (forall k l, mxdot (A k) (A l) = (k == l)%:R) -> (r <= d)%N ->
  #|[set a | eps ^+ 2 <= \sum_(k < r) ((x a) *m A k *m (y a)^T) 0 0 ^+ 2]|%:R
    <= C * (1 + L%:R) / eps ^+ 2 *
       expR (C / eps ^+ 2 * Num.sqrt d%:R * ln (2 + d%:R)).
