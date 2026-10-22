From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.

(**md**************************************************************************)
(* # Trace and multiplicity                                                   *)
(*                                                                            *)
(* A positive semidefinite matrix K that fixes the constant vector and        *)
(* commutes with a set of permutation matrices: if every nonzero orthogonal   *)
(* projection that commutes with these permutation matrices and kills the     *)
(* constants has trace at least m, then the quadratic form of K on the        *)
(* vectors orthogonal to the constants is controlled by the trace of K^2.     *)
(* For the w-subsets of 'I_k, every such projection that commutes with the    *)
(* action of all the permutations of 'I_k has trace at least k/2 when k is    *)
(* even and k >= 6.                                                           *)
(*                                                                            *)
(* The general statements of this file are compiled Prop definitions, for     *)
(* review with batch 1 of phase 14 (AGENTS.md, section Phase 14, step 0,      *)
(* items 5 and 6). Each will be proved by the lemma of the same name without  *)
(* the suffix _statement.                                                     *)
(*                                                                            *)
(* - trace_multiplicity_statement: let K in 'M[R]_N be positive semidefinite  *)
(*   with K 1 = 1, where 1 is the constant column vector, and let it commute  *)
(*   with perm_mx s for every s in a list S of permutations of 'I_N. Let m >  *)
(*   0, and suppose that every Q with Q symmetric, Q Q = Q, Q != 0, Q 1 = 0,  *)
(*   commuting with every perm_mx s for s in S, has trace at least m. Then    *)
(*   <x, K x>^2 <= (tr K^2 - 1) / m |x|^4 for every column vector x           *)
(*   orthogonal to 1. The square avoids a square root. The two hypotheses on  *)
(*   Q, symmetric and then idempotent, say that Q is an orthogonal            *)
(*   projection (orthoprojmx of psd_splitting.v), written out. The statement  *)
(*   is about permutation matrices: for an arbitrary family of matrices that  *)
(*   commute with K it is false, since a matrix that does not fix the         *)
(*   constants on both sides can leave no nonzero projection to satisfy the   *)
(*   hypothesis.                                                              *)
(* - ksubset_multiplicity_statement: let k be even with 6 <= k, w any         *)
(*   number, and Q a matrix indexed by the w-subsets of 'I_k with Q           *)
(*   symmetric, Q Q = Q, Q != 0 and Q 1 = 0, that commutes with ksubset_mx w  *)
(*   s for every permutation s of 'I_k. Then tr Q >= k %/ 2.                  *)
(*                                                                            *)
(* These are Rocq formalizations of the credited argument, the step 'From     *)
(* trace to contraction' of the proof of the lemma on local averaging of      *)
(* 'Exponential PSD rank of positively shifted matching matrices' (family 126 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/local-averaging.tex, lines 191-246): the claim of lines    *)
(* 197-223 that every nonzero permutation-invariant subspace orthogonal to    *)
(* the constants has dimension at least k/2, and the bound (k/2) mu^2 <= tr   *)
(* K^2 - 1 of lines 225-234. The Lean development of the collection, which    *)
(* this file reads for routes and conventions:                                *)
(* Lean: simultaneous_sign_eigenvector (Involutions.lean, line 70)            *)
(* Lean: independent_eigenprofiles (Involutions.lean, line 109)               *)
(* Lean: eigenspace_dim_mul_sq_le_trace_square (SpectralMultiplicity.lean,    *)
(*   line 24)                                                                 *)
(* Lean: quadratic_form_le_of_multiplicity (SpectralMultiplicity.lean, line   *)
(*   55)                                                                      *)
(*                                                                            *)
(* Departures. The manuscript counts the dimension of an invariant subspace,  *)
(* and the Lean development the rank of an eigenspace. These statements bound *)
(* the trace of an orthogonal projection instead, so that the proofs need no  *)
(* rank: c pairwise orthogonal nonzero vectors in the range of Q give c <= tr *)
(* Q through orthoprojmxB. The proof of the multiplicity bound follows the    *)
(* route of the audit of the manuscript, not the full simultaneous            *)
(* diagonalization of the pair transpositions: it refines a vector inside the *)
(* (-1)-eigenspace of the product of the first two of them, and it replaces   *)
(* the alternating group by single exchanges of the w-subsets, each a         *)
(* 3-cycle. The bound k/2 is the manuscript's; 6 <= k is needed by the proof  *)
(* (at k = 4 the argument through 3-cycles fails), and it is a hypothesis.    *)
(*                                                                            *)
(* ```                                                                        *)
(*          ksubset k w == the w-subsets of 'I_k, a finite type               *)
(*   ksubset_mx w s == the 0/1 matrix, indexed by the enumeration of the      *)
(*                     w-subsets, of the permutation that s : {perm 'I_k}     *)
(*                     induces on them: its entry (i, j) is 1 when the i-th   *)
(*                     w-subset is the image under s of the j-th              *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section multiplicity.
Variable R : realType.

Definition trace_multiplicity_statement : Prop :=
  forall (N m : nat) (K : 'M[R]_N) (S : seq {perm 'I_N}),
  psdmx K -> K *m (const_mx 1 : 'cV[R]_N) = const_mx 1 -> (0 < m)%N ->
  (forall s, s \in S -> perm_mx s *m K = K *m perm_mx s) ->
  (forall Q : 'M[R]_N, Q \is symmetricmx -> Q *m Q = Q -> Q != 0 ->
     Q *m (const_mx 1 : 'cV[R]_N) = 0 ->
     (forall s, s \in S -> perm_mx s *m Q = Q *m perm_mx s) -> m%:R <= \tr Q) ->
  forall x : 'cV[R]_N, mxdot x (const_mx 1) = 0 ->
  mxdot x (K *m x) ^+ 2 <= (\tr (K *m K) - 1) / m%:R * mxdot x x ^+ 2.

(* The w-subsets of 'I_k, and the 0/1 matrix of the permutation that s
   induces on them, indexed by their enumeration. *)
Definition ksubset (k w : nat) := {A : {set 'I_k} | #|A| == w}.

Definition ksubset_mx (k w : nat) (s : {perm 'I_k}) :
    'M[R]_#|{: ksubset k w}| :=
  \matrix_(i < #|{: ksubset k w}|, j < #|{: ksubset k w}|)
    (val (enum_val i : ksubset k w) == s @: val (enum_val j : ksubset k w))%:R.

Definition ksubset_multiplicity_statement : Prop :=
  forall (k w : nat) (Q : 'M[R]_#|{: ksubset k w}|),
  ~~ odd k -> (6 <= k)%N ->
  Q \is symmetricmx -> Q *m Q = Q -> Q != 0 ->
  Q *m (const_mx 1 : 'cV[R]_#|{: ksubset k w}|) = 0 ->
  (forall s : {perm 'I_k}, ksubset_mx w s *m Q = Q *m ksubset_mx w s) ->
  (k %/ 2)%:R <= \tr Q.
End multiplicity.
