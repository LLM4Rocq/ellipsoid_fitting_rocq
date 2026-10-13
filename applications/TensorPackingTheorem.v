From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import reals sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.matrix Require Import euclidean tensor_packing.
From GaussianApplications Require Import TensorPackingStatement.

(**md**************************************************************************)
(* # Tensor packing: the theorem                                              *)
(*                                                                            *)
(* Target T2 of phase 12. tensor_packing_theorem proves                       *)
(* tensor_packing_statement of TensorPackingStatement.v from the library file *)
(* matrix/tensor_packing.v, which is a Rocq formalization of the credited     *)
(* argument of Theorem 4.1, 'Tensor packing', of 'Pointwise convergence of    *)
(* fourfold ergodic averages for mixing transformations' (family 154 of the   *)
(* OpenAI math collection, revision 1581d4cbd, sections/04-packing.tex). The  *)
(* collection has no Lean version of it.                                      *)
(*                                                                            *)
(* The constant is C = 30000: the library theorem tensor_packing has the same *)
(* hypotheses, and writes the exponent C eps^(-2) sqrt d ln (2 + d) as        *)
(* 30000 sqrt d ln (2 + d) / eps^2.                                           *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Theorem tensor_packing_theorem : tensor_packing_statement.
Proof.
move=> R; exists 30000; split; first by lra.
move=> n1 n2 m d L r eps eta x y Gx Gy A eps0 eps1 d0 eta0 eta_eps x1 y1.
move=> degx degy exx exy Aon rd.
have -> : 30000 / eps ^+ 2 * Num.sqrt d%:R * ln (2 + d%:R) =
    30000 * Num.sqrt d%:R * ln (2 + d%:R) / eps ^+ 2 :> R by ring.
exact: (tensor_packing eps0 eps1 d0 eta0 eta_eps x1 y1 degx degy exx exy
  Aon rd).
Qed.
