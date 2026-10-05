From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions LowerDefinitions LowerFrechet
  FullThirdDefinitions FullThirdFrechet FullThirdContinuity
  BlockOperatorDefinitions BlockOperatorNormedDefinitions BlockOperatorSpaces
  BlockC3Definitions BlockC3Assembly MatrixThird.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/BlockGibbsC3.v from Coquelicot to MathComp-Analysis.

   Every lemma, definition and theorem of the original keeps its name and its
   arguments, in the same order. The section keeps its variables and its
   hypotheses, in the same order. One lemma is added, block_gibbs_linear_ext,
   marked below. The statements change form in the ways of the ports of
   LowerFrechet, FullThirdFrechet, BlockOperatorDefinitions,
   BlockC3Definitions and BlockC3Assembly, which this module imports.

   1. Linear maps. Coquelicot's is_linear l is a record with three fields,
        l (plus x y) = plus (l x) (l y),
        l (scal k x) = scal k (l x),
        exists M, 0 < M /\ forall x, norm (l x) <= M * norm x.
      As in BlockOperatorDefinitions and LowerFrechet, the port states it as
      the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity, which is equivalent to the first two
      fields, and of Coquelicot's norm bound (README, difference 2). The
      bound uses Stdlib's 0, <, <= and * around MathComp's norms. The norm on
      block_array n m is the Euclidean norm of all entries of
      LowerDefinitions, and the norm on R^o is the absolute value, as in
      Coquelicot, so the bound means the same, constants included. This is
      the predicate of bounded_block_map, so the six linearity lemmas are
      exactly the side conditions of the exist terms in the three operator
      definitions, as in the original.

   2. Real-valued maps. A map into R given to linear is written with codomain
      R^o, the normed module view of R, as in (F z s : block_array n m -> R^o)
      in the section hypothesis HL. R^o is R by definition, so F keeps the
      type nat -> nat -> block_array n m -> R of the original, and the maps
      are the same.

   3. The operator spaces block_first_operator_space n m,
      block_second_operator_space n m and block_third_operator_space n m and
      the predicate block_operator_C3 are those of BlockC3Definitions. There
      Coquelicot's filterdiff f (locally A) l is is_diff A f l, and
      Coquelicot's continuity at the point A is {for A, continuous f}. The
      three operator definitions build the same operators as in the
      original: their evaluations are lower_first, lower_second and
      lower_third, by reflexivity, as block_gibbs_operator_evaluations
      states.

   So the statements say the same thing as in the original.
   full_block_soft_minimax_C3, the theorem that BlockGibbsBounds,
   BlockRowEvaluation, BlockC3Results and BlockC3Policy use, keeps its
   statement word for word.

   Proofs. The original took the linearity of a Frechet derivative with
   proj1 of Coquelicot's filterdiff. The port takes it from
   matrix_third_is_diff_linear of MatrixThird, which proves that the
   derivative l of is_diff A f l is linear and bounded in the form of point 1.
   That is why this module imports MatrixThird in addition to the imports of
   the original. Coquelicot's is_linear_ext becomes block_gibbs_linear_ext
   below, proved by rewriting the function with funext of MathComp's boolp.
   It rests on boolp.functional_extensionality_dep, one of the seven axioms
   of the README. *)

(* Added by the port, in place of Coquelicot's is_linear_ext: the predicate
   of point 1 does not depend on how the map is written. *)
Lemma block_gibbs_linear_ext {U W : normedModType R} (f g : U -> W) :
  (forall x, f x = g x) ->
  (linear f /\
    exists M : R, 0 < M /\ forall x : U, (`|f x|)%R <= M * (`|x|)%R) ->
  linear g /\
    exists M : R, 0 < M /\ forall x : U, (`|g x|)%R <= M * (`|x|)%R.
Proof.
  move=> H Hf.
  have -> : g = f by apply: funext => x; rewrite H.
  exact Hf.
Qed.

Section GibbsBlockOperators.
Context (n m : nat) (beta gamma : R).
Context (F : nat -> nat -> block_array n m -> R) (Y S : list nat).
Context (Hb : 0 < beta) (Hg : 0 < gamma) (HY : Y <> []) (HS : S <> []).
Context (HL : forall z s, In z Y -> In s S ->
  linear (F z s : block_array n m -> R^o) /\
  exists M : R, 0 < M /\ forall x : block_array n m, (`|F z s x|)%R <= M * (`|x|)%R).

Lemma block_gibbs_first_linear A :
  linear (lower_first beta gamma F Y S A : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall U : block_array n m, (`|lower_first beta gamma F Y S A U|)%R <= M * (`|U|)%R.
Proof.
  exact (matrix_third_is_diff_linear _ _ A
    (lower_first_frechet beta gamma F Y S A Hb Hg HY HS HL)).
Qed.

Lemma block_gibbs_second_last_linear A U :
  linear (lower_second beta gamma F Y S A U : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall V : block_array n m, (`|lower_second beta gamma F Y S A U V|)%R <= M * (`|V|)%R.
Proof.
  exact (matrix_third_is_diff_linear _ _ A
    (lower_second_frechet beta gamma F Y S A U Hb Hg HY HS HL)).
Qed.

Lemma block_gibbs_second_first_linear A V :
  linear ((fun U => lower_second beta gamma F Y S A U V) : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall U : block_array n m, (`|lower_second beta gamma F Y S A U V|)%R <= M * (`|U|)%R.
Proof.
  apply (block_gibbs_linear_ext (lower_second beta gamma F Y S A V : block_array n m -> R^o)).
  - intros; apply lower_second_symmetric.
  - apply block_gibbs_second_last_linear.
Qed.

Lemma block_gibbs_third_last_linear A U V :
  linear (lower_third beta gamma F Y S A U V : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall W : block_array n m, (`|lower_third beta gamma F Y S A U V W|)%R <= M * (`|W|)%R.
Proof.
  exact (matrix_third_is_diff_linear _ _ A
    (lower_third_frechet beta gamma F Y S A U V Hb Hg HY HS HL)).
Qed.

Lemma block_gibbs_third_second_linear A U W :
  linear ((fun V => lower_third beta gamma F Y S A U V W) : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall V : block_array n m, (`|lower_third beta gamma F Y S A U V W|)%R <= M * (`|V|)%R.
Proof.
  apply (block_gibbs_linear_ext (lower_third beta gamma F Y S A U W : block_array n m -> R^o)).
  - intros; apply lower_third_swap_right.
  - apply block_gibbs_third_last_linear.
Qed.

Lemma block_gibbs_third_first_linear A V W :
  linear ((fun U => lower_third beta gamma F Y S A U V W) : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall U : block_array n m, (`|lower_third beta gamma F Y S A U V W|)%R <= M * (`|U|)%R.
Proof.
  apply (block_gibbs_linear_ext
    ((fun U => lower_third beta gamma F Y S A V U W) : block_array n m -> R^o)).
  - intros; apply lower_third_swap_left.
  - apply block_gibbs_third_second_linear.
Qed.

Definition block_gibbs_first_operator A : block_first_operator_space n m :=
  exist _ (lower_first beta gamma F Y S A) (block_gibbs_first_linear A).

Definition block_gibbs_second_operator (A : block_array n m) : block_second_operator_space n m.
Proof.
  refine (exist _ (fun V => exist _ (fun U => lower_second beta gamma F Y S A U V)
    (block_gibbs_second_first_linear A V)) _).
  apply block_operator_linearity_from_evaluations; intros U; apply block_gibbs_second_last_linear.
Defined.

Definition block_gibbs_third_operator (A : block_array n m) : block_third_operator_space n m.
Proof.
  unshelve refine (exist _ (fun W => exist _ (fun V => exist _
    (fun U => lower_third beta gamma F Y S A U V W)
    (block_gibbs_third_first_linear A V W)) _) _).
  - apply block_operator_linearity_from_evaluations; intros U; apply block_gibbs_third_second_linear.
  - apply block_operator_linearity_from_evaluations; intros V.
    apply block_operator_linearity_from_evaluations; intros U; apply block_gibbs_third_last_linear.
Defined.

Theorem block_gibbs_operator_evaluations A U V W :
  block_first_evaluation n m (block_gibbs_first_operator A) U = lower_first beta gamma F Y S A U /\
  block_second_evaluation n m (block_gibbs_second_operator A) U V = lower_second beta gamma F Y S A U V /\
  block_third_evaluation n m (block_gibbs_third_operator A) U V W = lower_third beta gamma F Y S A U V W.
Proof. repeat split; reflexivity. Qed.

Theorem block_gibbs_operator_C3 :
  block_operator_C3 n m
    (fun A => soft_minimax beta gamma (fun z s => F z s A) Y S)
    block_gibbs_first_operator block_gibbs_second_operator block_gibbs_third_operator.
Proof.
  apply block_C3_from_evaluations.
  - intros A; apply lower_first_frechet; assumption.
  - intros A U; apply lower_second_frechet; assumption.
  - intros A U V; apply lower_third_frechet; assumption.
  - intros A U V W; apply lower_third_continuous; assumption.
Qed.
End GibbsBlockOperators.

Theorem full_block_soft_minimax_C3 n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  exists (D1 : block_array n m -> block_first_operator_space n m)
    (D2 : block_array n m -> block_second_operator_space n m)
    (D3 : block_array n m -> block_third_operator_space n m),
    block_operator_C3 n m (lower_block_phi n m beta gamma y B Y S) D1 D2 D3 /\
    forall A U V W,
      block_first_evaluation n m (D1 A) U = lower_block_first n m beta gamma y B Y S A U /\
      block_second_evaluation n m (D2 A) U V = lower_block_second n m beta gamma y B Y S A U V /\
      block_third_evaluation n m (D3 A) U V W = lower_block_third n m beta gamma y B Y S A U V W.
Proof.
  intros Hb Hg HY HS.
  assert (HL : forall z s, In z Y -> In s S ->
    linear (lower_block_scores n m y B z s : block_array n m -> R^o) /\
    exists M : R, 0 < M /\
      forall x : block_array n m, (`|lower_block_scores n m y B z s x|)%R <= M * (`|x|)%R).
  { intros; apply lower_block_score_linear. }
  exists (block_gibbs_first_operator n m beta gamma (lower_block_scores n m y B) Y S Hb Hg HY HS HL),
    (block_gibbs_second_operator n m beta gamma (lower_block_scores n m y B) Y S Hb Hg HY HS HL),
    (block_gibbs_third_operator n m beta gamma (lower_block_scores n m y B) Y S Hb Hg HY HS HL).
  split.
  - apply block_gibbs_operator_C3.
  - intros; apply block_gibbs_operator_evaluations.
Qed.
