From mathcomp Require Import all_ssreflect_compat fingroup perm.

(**md**************************************************************************)
(* # Expanding bipartite multigraphs from permutations                        *)
(*                                                                            *)
(* For d permutations s 0, ..., s (d - 1) of 'I_l, consider the bipartite     *)
(* multigraph on the 2 l vertices 'I_(l + l) whose edge with label (j, u),    *)
(* for j < d and u < l, joins the left vertex lshift l u to the right vertex  *)
(* rshift l (s j u). Every vertex has degree d, the right ones because each s *)
(* j is a bijection; there are no loops, and parallel edges are distinct      *)
(* labels.                                                                    *)
(*                                                                            *)
(* - perm_cut s W: the cut of a vertex set W, the set of labels (j, u) whose  *)
(*   edge has exactly one end in W. Its cardinal counts the edges of the cut  *)
(*   with their multiplicities.                                               *)
(* - expander_statement: for every l >= 1 there are 100 permutations s 0,     *)
(*   ..., s 99 of 'I_l such that every vertex set W satisfies min(|W|, 2 l -  *)
(*   |W|) <= |perm_cut s W|. It is stated here for review, before its proof.  *)
(*                                                                            *)
(* A Rocq formalization of the lemma 'Expanding multigraphs' (lem:expander)   *)
(* of 'Exponential PSD rank of positively shifted matching matrices' (family  *)
(* 126 of the OpenAI math collection, revision 1581d4cbd),                    *)
(* source/sections/parity.tex, lines 28-91, with d = 100 and beta = 1/100.    *)
(* The statement departs from the TeX in three ways. It holds for every l >=  *)
(* 1, that is for every even t = 2 l >= 2, where the TeX says every           *)
(* sufficiently large even t: no step of the proof uses largeness. It names   *)
(* the construction of the proof, the union of 100 permutations between the   *)
(* two sides, where the TeX states the existence of a bipartite 100-regular   *)
(* multigraph. And since beta d = 1, the expansion inequality is an           *)
(* inequality of natural numbers. Connectivity, the last sentence of the      *)
(* lemma, is used in the form: a set with an empty cut is empty or the whole  *)
(* vertex set.                                                                *)
(*                                                                            *)
(* The proof, in a later commit, counts the tuples of permutations, among the *)
(* (l!)^100, that fail at some W. It replaces the entropy bound of the TeX by *)
(* crude estimates with small numerals: at most w - 1 exceptional labels for  *)
(* a set W of size w <= l, and the factor (w / l) kept through the union over *)
(* the sets of size w. It works in nat or rat, so that no real type is        *)
(* needed. It follows no Lean module of the collection, which proves a weaker *)
(* theorem by another route and has no expander.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The cut of W in the bipartite multigraph on 'I_(l + l) of d permutations:
   the label (j, u) joins lshift l u to rshift l (s j u). *)
Definition perm_cut (d l : nat) (s : 'I_d -> {perm 'I_l})
    (W : {set 'I_(l + l)}) : {set 'I_d * 'I_l} :=
  [set e | (lshift l e.2 \in W) != (rshift l (s e.1 e.2) \in W)].

(* For every l >= 1, some 100 permutations of 'I_l give a multigraph in which
   every cut has at least min(|W|, 2 l - |W|) edges. *)
Definition expander_statement : Prop :=
  forall l : nat, (0 < l)%N ->
  exists s : 'I_100 -> {perm 'I_l},
  forall W : {set 'I_(l + l)}, (minn #|W| (l + l - #|W|) <= #|perm_cut s W|)%N.
