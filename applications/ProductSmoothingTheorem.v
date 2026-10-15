From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum zmodp matrix.
From mathcomp Require Import reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part.
From GaussianAnalysis.fourier Require Import boolean_fourier product_smoothing.
From GaussianApplications Require Import ProductSmoothingStatement.

(**md**************************************************************************)
(* # Product smoothing of matrix squares: the theorem                         *)
(*                                                                            *)
(* Target T11 of phase 13. product_smoothing_theorem proves                   *)
(* product_smoothing_statement of ProductSmoothingStatement.v by              *)
(* product_smoothing of library/fourier/product_smoothing.v, a Rocq           *)
(* formalization of the credited argument of the theorem 'Fourier smoothing   *)
(* of matrix squares' of 'Exponential PSD rank of positively shifted matching *)
(* matrices' (family 126 of the OpenAI math collection, revision 1581d4cbd,   *)
(* source/sections/fourier-smoothing.tex, lines 42-98). The collection has no *)
(* Lean version of it. The library theorem has the same statement, with the   *)
(* same order of the binders; its axioms are three of boolp: propositional    *)
(* extensionality, functional extensionality and constructive indefinite      *)
(* description.                                                               *)
(******************************************************************************)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Theorem product_smoothing_theorem : product_smoothing_statement.
Proof.
by move=> R X M t a r mu nu pi theta B lambda F; exact: product_smoothing.
Qed.
