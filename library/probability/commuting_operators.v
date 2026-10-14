From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.

(**md**************************************************************************)
(* # Commuting operators and averages over random intersections               *)
(*                                                                            *)
(* The general statements of this file are compiled Prop definitions, for     *)
(* review with batch 1 of phase 13; their proofs follow their acceptance.     *)
(*                                                                            *)
(* - Iterates of monotone maps of a partial order T (a porderType). The       *)
(*   iterates of a monotone map are monotone (homo_iter_statement). If A and  *)
(*   B are monotone, B sub-commutes with A (B (A y) <= A (B y) for every y),  *)
(*   and B x <= A x at one point x, then iter m B x <= iter m A x for every m *)
(*   (iter_le_subcomm_statement). The comparison at a single point is what    *)
(*   the applications have: there, the one-step comparison holds at one       *)
(*   function only.                                                           *)
(* - Operators on the functions X -> R, for a type X and a numDomainType R:   *)
(*   linear_op A says that A is additive and homogeneous, and monotone_op A   *)
(*   that f <= g pointwise implies A f <= A g pointwise (for a linear         *)
(*   operator, positivity). The pointwise comparison of the iterates of two   *)
(*   monotone operators (monotone_iter_le_statement); the iterate of a        *)
(*   multiple of a linear operator (iter_scale_statement); the binomial       *)
(*   expansion of the iterate of the p-mixture of two commuting linear        *)
(*   operators (iter_mix_binomial_statement): in the language of Markov       *)
(*   operators, m steps that each move by A with probability p and by B       *)
(*   otherwise make a binomial number of A-steps; and the fixed-count         *)
(*   interpolation (binomial_mix_le_iter_statement): if A, B and C are        *)
(*   monotone linear operators that commute and the p-mixture of A and B is   *)
(*   below C at f, then for 0 <= p <= 1 the binomial mixture of the iterates  *)
(*   of A and B at f is below the iterate of C at f.                          *)
(* - Averages over random intersections, for a finite family E : C -> {set T} *)
(*   of subsets of a finite type T and f : {set T} -> R, over a realFieldType *)
(*   R: meet_avg E f S is the mean of f (S :&: E c) for c uniform on C. It is *)
(*   a monotone linear operator (meet_avg_linear_statement,                   *)
(*   meet_avg_monotone_statement) that fixes the constants when C is nonempty *)
(*   (meet_avg_cst_statement); any two such averages commute                  *)
(*   (meet_avgC_statement); and its m-th iterate intersects S with m          *)
(*   independent uniform members of the family (iter_meet_avg_statement).     *)
(*                                                                            *)
(* This file is part of target T9 of phase 13: a Rocq formalization, in       *)
(* general form, of the operator comparisons of the credited argument of 'A   *)
(* limiting satisfiability threshold for every fixed clause size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd). The manuscript proves  *)
(* its interpolation and transfer lemmas (source/sections/convergence.tex,    *)
(* the lemmas 'Auxiliary product inequality' and 'Proper-clause transfer')    *)
(* with marked Poisson families, a derivative in time and Poisson thinning.   *)
(* The Lean development of the collection (lean/OAI/Probability/RandomSAT)    *)
(* fixes the number of random constraints and compares the iterates of        *)
(* commuting averaging operators instead; this file follows it. The Lean      *)
(* development compares the iterates for exactly commuting monotone operators *)
(* on real functions; here the comparison is stated for sub-commuting         *)
(* monotone maps of a partial order, at one point, and its operator forms are *)
(* corollaries. In the manuscript the averages are over one uniform random    *)
(* constraint, which keeps the solutions that satisfy it: an average over     *)
(* random intersections.                                                      *)
(* Lean: finiteClauseAverage (Interpolation.lean, line 24)                    *)
(* Lean: finiteClauseAverage_commute (Interpolation.lean, line 53)            *)
(* Lean: iterate_compare_of_commute (Interpolation.lean, line 77)             *)
(* Lean: mixedAverage (Interpolation.lean, line 92)                           *)
(* Lean: mixed_finiteAverage_iterate (Interpolation.lean, line 278)           *)
(* Lean: auxiliary_interpolation (Interpolation.lean, line 397)               *)
(* Lean: proper_scaled_le_auxiliaryProbability (Transfer.lean, line 150)      *)
(*                                                                            *)
(* ```                                                                        *)
(*        linear_op A == the operator A : (X -> R) -> X -> R is additive and  *)
(*                       homogeneous, at every point of X                     *)
(*      monotone_op A == f <= g pointwise implies A f <= A g pointwise        *)
(*     meet_avg E f S == unif_mean (fun c => f (S :&: E c)), the mean of f at *)
(*                       the intersection of S with a uniform member of E     *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section operators.
Context {R : numDomainType} {X : Type}.

(* Linearity and monotonicity of an operator on the functions X -> R. *)
Definition linear_op (A : (X -> R) -> X -> R) : Prop :=
  (forall (f g : X -> R) (x : X),
     A (fun y => f y + g y) x = A f x + A g x) /\
  (forall (a : R) (f : X -> R) (x : X), A (fun y => a * f y) x = a * A f x).

Definition monotone_op (A : (X -> R) -> X -> R) : Prop :=
  forall f g : X -> R, (forall y, f y <= g y) -> forall x, A f x <= A g x.

End operators.

Section meet_avg.
Context {R : realFieldType} {T C : finType}.

(* The mean of f at the intersection of S with a uniform member of the
   family E. *)
Definition meet_avg (E : C -> {set T}) (f : {set T} -> R) (S : {set T}) : R :=
  unif_mean (fun c => f (S :&: E c)).

End meet_avg.

(* The general statements, for review. *)

(* The iterates of a monotone map of a partial order are monotone. *)
Definition homo_iter_statement : Prop :=
  forall (disp : Order.disp_t) (T : porderType disp) (A : T -> T) (m : nat),
  {homo A : x y / (x <= y)%O} -> {homo iter m A : x y / (x <= y)%O}.

(* The comparison of the iterates of two monotone maps at one point x: if B
   sub-commutes with A and B x <= A x, then iter m B x <= iter m A x. *)
Definition iter_le_subcomm_statement : Prop :=
  forall (disp : Order.disp_t) (T : porderType disp) (A B : T -> T) (x : T),
  {homo A : y z / (y <= z)%O} -> {homo B : y z / (y <= z)%O} ->
  (forall y, (B (A y) <= A (B y))%O) -> (B x <= A x)%O ->
  forall m, (iter m B x <= iter m A x)%O.

(* The same comparison for monotone operators on functions, at one
   function f, pointwise. *)
Definition monotone_iter_le_statement : Prop :=
  forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R)
         (f : X -> R),
  monotone_op A -> monotone_op B ->
  (forall g x, B (A g) x <= A (B g) x) -> (forall x, B f x <= A f x) ->
  forall (m : nat) (x : X), iter m B f x <= iter m A f x.

(* The iterate of c A is c ^+ m times the iterate of A. *)
Definition iter_scale_statement : Prop :=
  forall (R : numDomainType) (X : Type) (A : (X -> R) -> X -> R) (c : R),
  linear_op A ->
  forall (m : nat) (f : X -> R) (x : X),
  iter m (fun g y => c * A g y) f x = c ^+ m * iter m A f x.

(* The binomial expansion of the iterate of the p-mixture of two commuting
   linear operators. *)
Definition iter_mix_binomial_statement : Prop :=
  forall (R : numDomainType) (X : Type) (A B : (X -> R) -> X -> R) (p : R),
  linear_op A -> linear_op B -> (forall f, A (B f) = B (A f)) ->
  forall (m : nat) (f : X -> R) (x : X),
  iter m (fun g y => p * A g y + (1 - p) * B g y) f x =
  binomial_mean m p (fun j => iter j A (iter (m - j) B f) x).

(* The fixed-count interpolation: if the p-mixture of A and B is below C at
   f, so is the binomial mixture of their iterates below the iterate of C,
   for commuting monotone linear operators A, B and C. *)
Definition binomial_mix_le_iter_statement : Prop :=
  forall (R : numDomainType) (X : Type) (A B C : (X -> R) -> X -> R)
         (p : R) (f : X -> R),
  0 <= p <= 1 ->
  linear_op A -> linear_op B -> linear_op C ->
  monotone_op A -> monotone_op B -> monotone_op C ->
  (forall g, A (B g) = B (A g)) -> (forall g, A (C g) = C (A g)) ->
  (forall g, B (C g) = C (B g)) ->
  (forall x, p * A f x + (1 - p) * B f x <= C f x) ->
  forall (m : nat) (x : X),
  binomial_mean m p (fun j => iter j A (iter (m - j) B f) x) <=
  iter m C f x.

(* Averages over random intersections are monotone linear operators. *)
Definition meet_avg_linear_statement : Prop :=
  forall (R : realFieldType) (T C : finType) (E : C -> {set T}),
  linear_op (@meet_avg R T C E).

Definition meet_avg_monotone_statement : Prop :=
  forall (R : realFieldType) (T C : finType) (E : C -> {set T}),
  monotone_op (@meet_avg R T C E).

Definition meet_avg_cst_statement : Prop :=
  forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (a : R)
         (U : {set T}),
  (0 < #|C|)%N -> meet_avg E (fun=> a) U = a.

(* Any two averages over random intersections commute. *)
Definition meet_avgC_statement : Prop :=
  forall (R : realFieldType) (T C D : finType) (E : C -> {set T})
         (F : D -> {set T}) (f : {set T} -> R),
  meet_avg E (meet_avg F f) = meet_avg F (meet_avg E f).

(* The m-th iterate intersects S with m independent uniform members. *)
Definition iter_meet_avg_statement : Prop :=
  forall (R : realFieldType) (T C : finType) (E : C -> {set T}) (m : nat)
         (f : {set T} -> R) (S : {set T}),
  iter m (meet_avg E) f S =
  unif_mean (fun t : m.-tuple C => f (S :&: \bigcap_(c <- t) E c)).
