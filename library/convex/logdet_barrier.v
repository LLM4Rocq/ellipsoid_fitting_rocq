From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import vector boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun exp.
From GaussianAnalysis Require Import euclidean real_spectral self_concordant.

(**md**************************************************************************)
(* # The log-determinant barrier                                              *)
(*                                                                            *)
(* -ln det is a self-concordant barrier with parameter n on the cone of       *)
(* positive definite n x n matrices (Nesterov-Nemirovskii Proposition 5.4.5), *)
(* hence on its trace slices; the two-sided barrier                           *)
(* -ln det (A - m I) - ln det (M I - A) is a 2n-self-concordant barrier on    *)
(* the matrices of trace n with m I < A < M I. This is Lemma 2.8 of Koehler   *)
(* and Sohn (arXiv 2608.27372). Matrices are seen as row vectors of size      *)
(* n * n through mxvec, so that self_concordant.v applies; the inner product  *)
(* of mxvec A and mxvec B is the Frobenius product mxdot A B.                 *)
(*                                                                            *)
(* ```                                                                        *)
(*            posdefmx A == A is symmetric positive definite:                 *)
(*                          0 < x A x^T for every row vector x != 0           *)
(*          pd_slice n s == the matrices A (as mxvec A) that are positive     *)
(*                          definite with trace s                             *)
(*      logdet_barrier x == - ln (det (vec_mx x)), for x : 'rV[R]_(n * n)     *)
(*       pd_slice2 n m M == the matrices A (as mxvec A) of trace n with       *)
(*                          A - m I and M I - A positive definite             *)
(* logdet_barrier2 m M x == - ln det (A - m I) - ln det (M I - A)             *)
(*                          + n ln ((1 - m) (M - 1)), with A = vec_mx x       *)
(* ```                                                                        *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5):                                      *)
(* - The subspaces of 'rV[R]_(n * n) made of the mxvec of the symmetric       *)
(*   matrices, and of the symmetric matrices of trace 0, with their           *)
(*   membership lemmas; the dimension of the latter is at most n * n.         *)
(* - For A positive definite and U symmetric,                                 *)
(*   -ln det (A + t U) = -ln det A - sum_i ln (1 + t l_i) where the l_i are   *)
(*   the eigenvalues of W U W^T, W the whitening matrix of A                  *)
(*   (matrix/whitening.v); so the derivatives along U are                     *)
(*   D = - tr (A^-1 U), D^2 = tr (A^-1 U A^-1 U) and                          *)
(*   D^3 = - 2 tr ((A^-1 U)^3) (paper, lines 1260-1278).                      *)
(* - logdet_barrier is an n-self-concordant barrier on the positive definite  *)
(*   cone (directions: the symmetric matrices), and on pd_slice n s for s > 0 *)
(*   (directions: the symmetric matrices of trace 0); both domains are        *)
(*   convex and relatively open (rel_open_convex).                            *)
(* - logdet_barrier >= 0 on pd_slice n n%:R, with value 0 at the identity     *)
(*   (det A <= (tr A / n)^n).                                                 *)
(* - For 0 < m < 1 < M, logdet_barrier2 m M is a 2n-self-concordant barrier   *)
(*   on pd_slice2 n m M, nonnegative, with value 0 at the identity.           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section logdet_definitions.
Context {R : realType}.

Definition posdefmx n (A : 'M[R]_n) : Prop :=
  A \is symmetricmx /\ forall x : 'rV[R]_n, x != 0 -> 0 < mxdot x (x *m A).

Definition pd_slice n (s : R) : set 'rV[R]_(n * n) :=
  [set x | posdefmx (vec_mx x) /\ \tr (vec_mx x) = s].

Definition logdet_barrier n (x : 'rV[R]_(n * n)) : R := - ln (\det (vec_mx x)).

Definition pd_slice2 n (m M : R) : set 'rV[R]_(n * n) :=
  [set x | posdefmx (vec_mx x - m%:M) /\ posdefmx (M%:M - vec_mx x) /\
           \tr (vec_mx x) = n%:R].

Definition logdet_barrier2 n (m M : R) (x : 'rV[R]_(n * n)) : R :=
  - ln (\det (vec_mx x - m%:M)) - ln (\det (M%:M - vec_mx x)) +
  n%:R * ln ((1 - m) * (M - 1)).

End logdet_definitions.

Arguments pd_slice {R} n s.
Arguments pd_slice2 {R} n m M.
