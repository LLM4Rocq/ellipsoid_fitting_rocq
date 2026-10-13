From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.

(**md**************************************************************************)
(* # Capped variance of random k-SAT: the definitions                         *)
(*                                                                            *)
(* Target T7 of phase 12 (AGENTS.md, section Phase 12; the plan               *)
(* notes/phase12-plan.md, section 3). The definitions of the statement of     *)
(* SatVarianceStatement.v, from 'A limiting satisfiability threshold for      *)
(* every fixed clause size' (family 235 of the OpenAI math collection,        *)
(* revision 1581d4cbd, source/sections/introduction.tex and                   *)
(* concentration.tex). The Lean counterparts, in                              *)
(* lean/OAI/Probability/RandomSAT of the collection:                          *)
(* Lean: ProperClause, SatisfiesClause (Model.lean)                           *)
(* Lean: capMultiplier, mainCap, variance_capped (Concentration.lean)         *)
(*                                                                            *)
(* All are finite; R is any realType.                                         *)
(*                                                                            *)
(* - A proper signed k-clause on n variables is a partial sign assignment c   *)
(*   of {ffun 'I_n -> option bool} with exactly k signed variables            *)
(*   (proper_clause): c i = Some true is the literal x_i, c i = Some false    *)
(*   the literal not x_i, and c i = None means that x_i does not occur. The   *)
(*   clauses of size k form the finite type clause n k; there are 2^k         *)
(*   binom(n, k) of them, as in the manuscript, and the uniform law on clause *)
(*   n k gives each the same probability.                                     *)
(* - An assignment sigma of {ffun 'I_n -> bool} satisfies c when some literal *)
(*   of c is true (clause_sat). For a tuple t of M clauses, prefix_sat t m    *)
(*   says that some assignment satisfies the clauses of t at the positions i  *)
(*   < m; prefix_sat t 0 holds.                                               *)
(* - sat_cap k n = 2^(k+1) n is the cap L_k n of the manuscript, and          *)
(*   sat_prefix_len t is the largest m <= M with prefix_sat t m: the length   *)
(*   of the longest satisfiable prefix of t, capped at M. For M = sat_cap k n *)
(*   it is the statistic V_n = min(H_n - 1, L_k n) of the manuscript, written *)
(*   directly on the first L_k n clauses, so that no clause beyond the cap is *)
(*   drawn.                                                                   *)
(* - sat_mean F is the average of F over all tuples of M clauses, its         *)
(*   expectation when the M clauses are independent and uniform on clause n k *)
(*   (drawn with replacement), and sat_var F its variance. sat_capped_var n k *)
(*   is the variance of V_n.                                                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section sat_variance_definitions.
Variable R : realType.
Implicit Types n k M : nat.

Definition proper_clause n k (c : {ffun 'I_n -> option bool}) : bool :=
  #|[set i | c i != None]| == k.

Definition clause n k := {c : {ffun 'I_n -> option bool} | proper_clause k c}.

Definition clause_sat n k (sigma : {ffun 'I_n -> bool}) (c : clause n k) :
    bool :=
  [exists i, val c i == Some (sigma i)].

Definition prefix_sat n k M (t : M.-tuple (clause n k)) (m : nat) : bool :=
  [exists sigma : {ffun 'I_n -> bool},
    [forall i : 'I_M, (i < m)%N ==> clause_sat sigma (tnth t i)]].

Definition sat_cap k n : nat := 2 ^ k.+1 * n.

Definition sat_prefix_len n k M (t : M.-tuple (clause n k)) : nat :=
  \max_(m < M.+1 | prefix_sat t m) m.

Definition sat_mean n k M (F : M.-tuple (clause n k) -> R) : R :=
  (#|{: M.-tuple (clause n k)}|%:R)^-1 *
    \sum_(t : M.-tuple (clause n k)) F t.

Definition sat_var n k M (F : M.-tuple (clause n k) -> R) : R :=
  sat_mean (fun t => (F t - sat_mean F) ^+ 2).

Definition sat_capped_var n k : R :=
  sat_var (fun t : (sat_cap k n).-tuple (clause n k) => (sat_prefix_len t)%:R).

End sat_variance_definitions.
