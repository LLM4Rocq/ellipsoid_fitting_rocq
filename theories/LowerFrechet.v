From Stdlib Require Import Reals List Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights
  MatrixDefinitions MatrixCoordinates MatrixTrace MatrixGibbs MatrixSecond
  SoftMatrixDefinitions LowerDefinitions LowerNormBounds.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/LowerFrechet.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. The statements change form in three ways,
   the same ways as in the ports of MatrixCoordinates, MatrixGibbs and
   MatrixSecond, which this module imports.

   1. Frechet derivatives. Coquelicot's NormedModule R_AbsRing becomes
      normedModType R, and Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis: f is differentiable at A and its
      differential 'd f A is l. Both say that l is linear and continuous and
      that f (A + H) = f A + l H + o(H) as H tends to 0. On block_array n m
      the norm is the Euclidean norm of all entries of LowerDefinitions, as
      in Coquelicot; differentiability does not depend on the choice among
      equivalent norms in any case.

   2. Linear maps. Coquelicot's is_linear l is stated, as in
      MatrixCoordinates, as the conjunction
        linear l /\
        exists M : R, 0 < M /\ forall x, (`|l x|)%R <= M * (`|x|)%R
      of MathComp's algebraic linearity and Coquelicot's norm bound. The
      norms are those of the spaces involved: the absolute value on R, and
      on block_array n m the norm of LowerDefinitions. So the hypotheses of
      the four generic theorems and the conclusion of
      lower_block_score_linear mean what they meant in the original,
      constants included.

   3. Real-valued maps. A map into R given to is_diff or linear is written
      with codomain R^o, the normed module view of R, as in
      (F z s : E -> R^o). R^o is R by definition, so F keeps the type
      nat -> nat -> E -> R of the original, and the maps are the same.

   The arithmetic, exp and ln inside the soft maxima and Gibbs averages are
   Stdlib's, as in the original. In the proofs, filterdiff_linear becomes
   matrix_linear_is_diff of MatrixCoordinates, filterdiff_const becomes
   is_diff_cst, filterdiff_ext_lin becomes is_diff_eq with an equation of
   functions, is_linear_ext becomes rewriting the function with funext, and
   is_linear_comp becomes matrix_linear_comp of MatrixCoordinates. *)

Theorem lower_inner_frechet {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A : E) z :
  0 < gamma -> S <> [] ->
  (forall s, In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => lower_inner_value gamma F S M z) : E -> R^o)
    (fun U => lower_inner_first gamma F S A U z).
Proof.
  intros Hg HS HF; unfold lower_inner_value, lower_inner_first.
  apply (soft_max_frechet gamma (F z) (F z) S A); try assumption; try lra.
  intros s Hs; apply matrix_linear_is_diff, HF; exact Hs.
Qed.

Theorem lower_inner_first_frechet {E : normedModType R} gamma
    (F : nat -> nat -> E -> R) S (A U : E) z :
  S <> [] ->
  (forall s, In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => lower_inner_first gamma F S M U z) : E -> R^o)
    (fun V => gamma * lower_inner_covariance gamma F S A U V z).
Proof.
  intros HS HF.
  pose proof (gibbs_average_frechet gamma (F z) (F z)
    (fun s (_ : E) => F z s U) (fun (_ : nat) (_ : E) => 0) S A HS) as H.
  assert (HD : forall s, In s S -> is_diff A (F z s : E -> R^o) (F z s)).
  { intros s Hs; apply matrix_linear_is_diff, HF; exact Hs. }
  assert (HC : forall s, In s S ->
    is_diff A ((fun _ : E => F z s U) : E -> R^o) (fun _ : E => 0)).
  { intros s Hs; exact (is_diff_cst (F z s U : R^o) A). }
  specialize (H HD HC).
  unfold lower_inner_first, lower_inner_covariance.
  apply: (is_diff_eq H).
  apply: funext => V.
  change (gibbs_average gamma (fun s => F z s A) S (fun _ => 0) +
    gamma * gibbs_covariance gamma (fun s => F z s A) S
    (fun s => F z s U) (fun s => F z s V) =
    gamma * gibbs_covariance gamma (fun s => F z s A) S
    (fun s => F z s U) (fun s => F z s V)).
  rewrite (gibbs_average_const _ _ _ _ HS); ring.
Qed.

Theorem lower_first_frechet {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A : E) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall z s, In z Y -> In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => soft_minimax beta gamma (fun z s => F z s M) Y S) : E -> R^o)
    (lower_first beta gamma F Y S A).
Proof.
  intros Hb Hg HY HS HF; unfold soft_minimax, lower_first.
  change (is_diff A
    ((fun M => soft_min beta (fun z => lower_inner_value gamma F S M z) Y) : E -> R^o)
    (fun U => gibbs_average (- beta) (fun z => lower_inner_value gamma F S A z) Y
      (fun z => lower_inner_first gamma F S A U z))).
  apply (soft_min_frechet beta
    (fun z M => lower_inner_value gamma F S M z)
    (fun z U => lower_inner_first gamma F S A U z) Y A); try assumption; try lra.
  intros z Hz; apply lower_inner_frechet; try assumption.
  intros s Hs; apply HF; assumption.
Qed.

Theorem lower_second_frechet {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U : E) :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall z s, In z Y -> In s S ->
    linear (F z s : E -> R^o) /\
    exists M : R, 0 < M /\ forall x : E, (`|F z s x|)%R <= M * (`|x|)%R) ->
  is_diff A ((fun M => lower_first beta gamma F Y S M U) : E -> R^o)
    (lower_second beta gamma F Y S A U).
Proof.
  intros Hb Hg HY HS HF.
  pose proof (gibbs_average_frechet (- beta)
    (fun z M => lower_inner_value gamma F S M z)
    (fun z V => lower_inner_first gamma F S A V z)
    (fun z M => lower_inner_first gamma F S M U z)
    (fun z V => gamma * lower_inner_covariance gamma F S A U V z) Y A HY) as H.
  assert (HD : forall z, In z Y ->
    is_diff A ((fun M => lower_inner_value gamma F S M z) : E -> R^o)
      (fun V => lower_inner_first gamma F S A V z)).
  { intros z Hz; apply lower_inner_frechet; try assumption; intros; apply HF; assumption. }
  assert (HC : forall z, In z Y ->
    is_diff A ((fun M => lower_inner_first gamma F S M U z) : E -> R^o)
      (fun V => gamma * lower_inner_covariance gamma F S A U V z)).
  { intros z Hz; apply lower_inner_first_frechet; try assumption; intros; apply HF; assumption. }
  specialize (H HD HC); unfold lower_first, lower_second.
  apply: (is_diff_eq H).
  apply: funext => V.
  change (gibbs_average (- beta) (lower_inner_value gamma F S A) Y
      (fun z => gamma * lower_inner_covariance gamma F S A U V z) +
    - beta * gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_first gamma F S A U) (fun z => lower_inner_first gamma F S A V z) =
    gamma * gibbs_average (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U V) -
    beta * gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)).
  rewrite gibbs_average_scale -Ropp_mult_distr_l; reflexivity.
Qed.

Theorem lower_block_score_linear n m y B z s :
  linear (lower_block_scores n m y B z s : block_array n m -> R^o) /\
  exists M : R, 0 < M /\
    forall x : block_array n m,
      (`|lower_block_scores n m y B z s x|)%R <= M * (`|x|)%R.
Proof.
  have E : lower_block_scores n m y B z s =
    (fun U : block_array n m => coordinate_sum m
      (fun i => y z i * trace_pair n (B s) (block_entry n m U i))).
  { apply: funext => U; unfold lower_block_scores, soft_matrix_scores.
    symmetry; apply lower_coordinate_sum_finite. }
  rewrite E.
  apply (coordinate_sum_linear m
    (fun i (U : block_array n m) => y z i * trace_pair n (B s) (block_entry n m U i)));
    intros i Hi; apply matrix_linear_scale.
  apply (@matrix_linear_comp (block_NormedModule n m) (matrix_NormedModule n) R^o
    (fun U : block_array n m => block_entry n m U i)
    (trace_pair n (B s) : matrix n -> R^o)).
  - apply tuple_entry_linear.
  - apply trace_pair_linear.
Qed.

Theorem lower_block_derivatives n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  forall A : block_array n m,
  is_diff A (lower_block_phi n m beta gamma y B Y S : block_array n m -> R^o)
    (lower_block_first n m beta gamma y B Y S A) /\
  forall U : block_array n m,
  is_diff A
    ((fun M => lower_block_first n m beta gamma y B Y S M U) : block_array n m -> R^o)
    (lower_block_second n m beta gamma y B Y S A U).
Proof.
  intros Hb Hg HY HS A; split.
  - apply (lower_first_frechet beta gamma (lower_block_scores n m y B) Y S A); try assumption.
    intros; apply lower_block_score_linear.
  - intros U; apply lower_second_frechet; try assumption.
    intros; apply lower_block_score_linear.
Qed.
