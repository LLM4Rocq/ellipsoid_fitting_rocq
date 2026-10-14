From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.

(**md**************************************************************************)
(* # PSD rank of shifted matching matrices: the definitions                   *)
(*                                                                            *)
(* The PSD main statement of phase 13 (AGENTS.md, section Phase 13, batch 3;  *)
(* the plan notes/phase13-plan.md, section 2). The definitions of the         *)
(* statement of PsdRankStatement.v, from 'Exponential PSD rank of positively  *)
(* shifted matching matrices' (family 126 of the OpenAI math collection,      *)
(* revision 1581d4cbd, source/sections/introduction.tex, lines 12-23). The    *)
(* Lean model of the collection for family 126 has the same objects, with     *)
(* ordered pairs as edges:                                                    *)
(* Lean: Edge, IsPerfectMatching, PerfectMatching, OddCut (Model.lean)        *)
(* Lean: Crosses, crossingCount (Model.lean, lines 19-25)                     *)
(*                                                                            *)
(* For a natural number n, the vertices are 'I_n.                             *)
(* - The edges of the complete graph K_n are the 2-subsets of 'I_n (kn_edge). *)
(* - edge_cut U is delta(U), the edges with exactly one endpoint in U.        *)
(* - A perfect matching is a set of edges such that every vertex lies in      *)
(*   exactly one of them (is_perfect_matching); perfect_matching n is the     *)
(*   finite type of the perfect matchings of K_n, the manuscript's M_n.       *)
(* - odd_set n is the finite type of the subsets of 'I_n of odd cardinality,  *)
(*   the manuscript's O_n.                                                    *)
(* - crossing U M = |M cap delta(U)|.                                         *)
(* - shifted_matching_mx rho U M = |M cap delta(U)| - 1 + rho, in any         *)
(*   realType R, is the matrix A_n(rho) of the manuscript (equation           *)
(*   eq:main-matrix), with rows the odd sets and columns the perfect          *)
(*   matchings.                                                               *)
(*                                                                            *)
(* Choices, for the reviewer.                                                 *)
(*                                                                            *)
(* - An edge is a 2-subset of 'I_n, where the Lean model uses an ordered pair *)
(*   p with p.1 < p.2; with 2-subsets the cut condition is #|e :&: U| == 1.   *)
(* - The two index types are sig subtypes of finite types, hence finite       *)
(*   types, as psd_factorization requires.                                    *)
(* - The definitions take every n and every rho; the statement restricts them *)
(*   to even n >= n0 and 0 < rho < 1, as the manuscript's theorem does (the   *)
(*   manuscript defines A_n(rho) for even n >= 4 and 0 <= rho <= 1).          *)
(* - Sanity lemmas, not frozen, are in PsdRank/Model.v: crossing U M is odd,  *)
(*   so every entry of A_n(rho) is at least rho; and A_n(1) has a PSD         *)
(*   factorization whose size is the number of edges, 'C(n, 2).               *)
(*                                                                            *)
(* ```                                                                        *)
(*            kn_edge e == e is an edge of K_n: a 2-subset of 'I_n            *)
(*          edge_cut U == delta(U): the edges with one endpoint in U          *)
(* is_perfect_matching M == M is a set of edges covering each vertex once     *)
(*   perfect_matching n == the perfect matchings of K_n                       *)
(*            odd_set n == the subsets of 'I_n of odd cardinality             *)
(*         crossing U M == |M cap delta(U)|                                   *)
(* shifted_matching_mx rho U M == |M cap delta(U)| - 1 + rho                  *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section psd_rank_definitions.
Variable n : nat.

(* The edges of K_n are the 2-subsets of 'I_n. *)
Definition kn_edge (e : {set 'I_n}) : bool := #|e| == 2.

(* delta(U): the edges with exactly one endpoint in U. *)
Definition edge_cut (U : {set 'I_n}) : {set {set 'I_n}} :=
  [set e | kn_edge e & #|e :&: U| == 1].

(* A perfect matching: a set of edges such that every vertex lies in
   exactly one of them. *)
Definition is_perfect_matching (M : {set {set 'I_n}}) : bool :=
  [forall e in M, kn_edge e] && [forall v, #|[set e in M | v \in e]| == 1].

Definition perfect_matching := {M : {set {set 'I_n}} | is_perfect_matching M}.

Definition odd_set := {U : {set 'I_n} | odd #|U|}.

(* |M cap delta(U)| *)
Definition crossing (U : odd_set) (M : perfect_matching) : nat :=
  #|val M :&: edge_cut (val U)|.

(* A_n(rho)_(U, M) = |M cap delta(U)| - 1 + rho *)
Definition shifted_matching_mx (R : realType) (rho : R)
    (U : odd_set) (M : perfect_matching) : R :=
  ((crossing U M)%:R - 1 + rho)%R.

End psd_rank_definitions.
