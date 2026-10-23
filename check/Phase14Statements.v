(* The general statements of phase 14 accepted by the user (batch 1, at
   39f58468aeaa), stated in full as the acceptance inventory of
   scripts/check_sources.py (INVENTORY_P14) records them, and proved by
   their library lemmas. The statements of one library file are read in a
   module with the Require, Import and Open Scope commands of that file at
   the commit of their acceptance, where the inventory printed them. make
   check compiles this file; its code is fixed by scripts/check_sources.py. *)

(* The Require commands of each file are inside its module, so that the
   imports end with the module. *)

(* library/matrix/multiplicity.v, accepted at 39f58468aeaa *)
Module accepted_multiplicity.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix sesquilinear reals.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.matrix.multiplicity.

Lemma trace_multiplicity_accepted : forall R : realType, forall (N m : nat) (K : 'M_N) (S0 : seq {perm 'I_N}), @psdmx R N K -> K *m (@const_mx R N 1 1 : 'cV_N) = @const_mx R N 1 1 -> (0 < m)%N -> (forall s : perm_perm_type__canonical__eqtype_Equality 'I_N, s \in S0 -> @perm_mx R N s *m K = K *m @perm_mx R N s) -> (forall Q : 'M_N, Q \is symmetricmx -> Q *m Q = Q -> Q != 0 -> Q *m (@const_mx R N 1 1 : 'cV_N) = 0 -> (forall s : perm_perm_type__canonical__eqtype_Equality 'I_N, s \in S0 -> @perm_mx R N s *m Q = Q *m @perm_mx R N s) -> m%:R <= \tr Q) -> forall x : 'cV_N, @mxdot R N 1 x (@const_mx R N 1 1) = 0 -> @mxdot R N 1 x (K *m x) ^+ 2 <= (\tr (K *m K) - 1) / m%:R * @mxdot R N 1 x x ^+ 2.
Proof. exact: @trace_multiplicity. Qed.

Lemma ksubset_multiplicity_accepted : forall R : realType, forall (k w : nat) (Q : 'M_#|{: ksubset k w}|), ~~ odd k -> (5 < k)%N -> Q \is symmetricmx -> Q *m Q = Q -> Q != 0 -> Q *m (@const_mx R #|{: ksubset k w}| 1 1 : 'cV_#|{: ksubset k w}|) = 0 -> (forall s : {perm 'I_k}, @ksubset_mx R k w s *m Q = Q *m @ksubset_mx R k w s) -> (k %/ 2)%:R <= \tr Q.
Proof. exact: @ksubset_multiplicity. Qed.

End accepted_multiplicity.

(* library/combinatorics/harmonic.v, accepted at 39f58468aeaa *)
Module accepted_harmonic.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals exp.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.combinatorics.harmonic.

Lemma harmonic_ln_accepted : forall R : realType, forall n : nat, (0 < n)%N -> \sum_(i < n) i.+1%:R^-1 <= 1 + @ln R (n%:R : R).
Proof. exact: @harmonic_ln. Qed.

End accepted_harmonic.

(* library/combinatorics/binomial_bounds.v, accepted at 39f58468aeaa *)
Module accepted_binomial_bounds.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum rat reals.
From mathcomp Require Import sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Require Import GaussianAnalysis.combinatorics.binomial_bounds.

Lemma bin_mul_pow_accepted : forall b l s : nat, (b <= l)%N -> ('C(b, s) * l ^ s <= 'C(l, s) * b ^ s)%N.
Proof. exact: @bin_mul_pow. Qed.

End accepted_binomial_bounds.

(* library/combinatorics/expander.v, accepted at 39f58468aeaa *)
Module accepted_expander.
From mathcomp Require Import all_ssreflect_compat fingroup perm.
Require Import GaussianAnalysis.combinatorics.expander.

Lemma expander_accepted : forall l : nat, 0 < l -> exists s : 'I_100 -> {perm 'I_l}, forall W : {set 'I_(l + l)}, minn #|W| (l + l - #|W|) <= #|@perm_cut 100 l s W|.
Proof. exact: @expander. Qed.

End accepted_expander.

(* Every accepted statement, for one axiom report. *)
Definition phase14_statements_accepted :=
  (accepted_multiplicity.trace_multiplicity_accepted,
   accepted_multiplicity.ksubset_multiplicity_accepted,
   accepted_harmonic.harmonic_ln_accepted,
   accepted_binomial_bounds.bin_mul_pow_accepted,
   accepted_expander.expander_accepted).
Print Assumptions phase14_statements_accepted.
