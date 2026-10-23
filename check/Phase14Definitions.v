(* The project definitions that the general statements of phase 14
   accepted by the user (batch 1, at 39f58468aeaa) unfold to and that no
   earlier check protects, characterized by properties that determine them
   (AGENTS.md, section Phase 14, The word for the extension; the plan
   notes/phase14-plan.md, section 9). By the user's decision of 22 October
   2026 (Q2), their code stays that of the acceptance commit until this
   check characterizes them from it.

   Each lemma states its property in this file, written out down to the
   definitions of MathComp, and is proved by computation (by []). make
   check compiles the file into a required output, so it fails unless each
   definition still computes to the text written here: after a change of
   its meaning, and also after a change of its implementation that keeps
   the meaning but not the computation. scripts/check_sources.py fixes the
   code of this file.

   - ksubset (matrix/multiplicity.v): the w-subsets of 'I_k, as the subtype
     of the sets of size w.
   - ksubset_mx (matrix/multiplicity.v): the 0/1 matrix, indexed by the
     enumeration of the w-subsets, of the permutation that s induces on
     them: the entry (i, j) is 1 exactly when the i-th subset is the image
     by s of the j-th.
   - perm_cut (combinatorics/expander.v): the labels e = (j, u) of the
     bipartite multigraph of the permutations s j on 'I_l + 'I_l, whose
     edge joins lshift l u and rshift l (s j u), that cross W. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix reals.
From GaussianAnalysis.matrix Require Import multiplicity.
From GaussianAnalysis.combinatorics Require Import expander.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma ksubset_characterization (k w : nat) :
  ksubset k w = {A : {set 'I_k} | #|A| == w}.
Proof. by []. Qed.

Lemma ksubset_mx_characterization (R : realType) (k w : nat)
    (s : {perm 'I_k}) :
  ksubset_mx R w s =
  \matrix_(i < #|{: ksubset k w}|, j < #|{: ksubset k w}|)
    ((val (enum_val i : ksubset k w) ==
      [set s x | x in val (enum_val j : ksubset k w)]) %:R : R).
Proof. by []. Qed.

Lemma perm_cut_characterization (d l : nat) (s : 'I_d -> {perm 'I_l})
    (W : {set 'I_(l + l)}) :
  perm_cut s W =
  [set e : 'I_d * 'I_l |
     (lshift l e.2 \in W) != (rshift l (s e.1 e.2) \in W)].
Proof. by []. Qed.
Print Assumptions perm_cut_characterization.
