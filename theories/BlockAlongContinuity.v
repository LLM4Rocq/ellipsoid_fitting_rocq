From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions GibbsDefinitions ThirdDefinitions
  LowerDefinitions LowerFrechet FullThirdDefinitions FiniteGibbsContinuity
  MatrixCoordinates.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Continuity along paths of the derivatives of the block soft minimax.
   Let A, U, V, W be paths from a topological space E to block_array n m,
   continuous at a point q. Then the following functions of x are
   continuous at q ({for q, continuous _}):
   - the block scores of A x (block_score_along_continuous);
   - the inner soft maximum and the inner Gibbs average, covariance and
     third cumulant of the scores, in the directions U x, V x, W x
     (block_inner_value_along_continuous and the next three lemmas);
   - the first derivative lower_block_first at A x in the direction U x
     (block_first_along_continuous) and the third derivative
     lower_block_third at A x in the directions U x, V x, W x
     (block_third_along_continuous).
   The proofs combine the continuity of Gibbs averages, covariances and
   third cumulants in their parameters (FiniteGibbsContinuity) with the
   continuity of the linear score map and of the inner soft maximum.

   When E is a concrete type such as R, Rocq's plain apply may not find the
   topology of E by unification, and then runs for a long time. Use
   ssreflect's apply:, or give E explicitly, as in
   apply (@block_first_along_continuous R). When E is a variable of type
   topologicalType, plain apply works. *)

Lemma block_score_along_continuous {E : topologicalType} n m y B z s
    (A : E -> block_array n m) q :
  {for q, continuous A} ->
  {for q, continuous (fun x => lower_block_scores n m y B z s (A x))}.
Proof.
  intro HA.
  apply: (@continuous_comp E (block_array n m) R A (lower_block_scores n m y B z s) q HA).
  exact: (matrix_linear_continuous (lower_block_scores n m y B z s : block_array n m -> R^o)
    (lower_block_score_linear n m y B z s)).
Qed.

Lemma block_inner_value_along_continuous {E : topologicalType} n m gamma y B S z
    (A : E -> block_array n m) q :
  0<gamma -> S<>[] -> {for q, continuous A} ->
  {for q, continuous (fun x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)}.
Proof.
  intros Hg HS HA.
  apply: (@continuous_comp E (block_array n m) R A
    (fun M => lower_inner_value gamma (lower_block_scores n m y B) S M z) q HA).
  have HD := lower_inner_frechet gamma (lower_block_scores n m y B) S (A q) z Hg HS
    (fun s _ => lower_block_score_linear n m y B z s).
  exact: (differentiable_continuous (ex_diff (is_diff_def := HD))).
Qed.

Lemma block_inner_first_along_continuous {E : topologicalType} n m gamma y B S z
    (A U : E -> block_array n m) q :
  S<>[] -> {for q, continuous A} -> {for q, continuous U} ->
  {for q, continuous (fun x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (U x) z)}.
Proof.
  intros HS HA HU; unfold lower_inner_first.
  apply (gibbs_average_continuous gamma
    (fun s x => lower_block_scores n m y B z s (A x))
    (fun s x => lower_block_scores n m y B z s (U x)) S q); try assumption;
    intros; apply block_score_along_continuous; assumption.
Qed.

Lemma block_inner_covariance_along_continuous {E : topologicalType} n m gamma y B S z
    (A U V : E -> block_array n m) q :
  S<>[] -> {for q, continuous A} -> {for q, continuous U} -> {for q, continuous V} ->
  {for q, continuous (fun x => lower_inner_covariance gamma (lower_block_scores n m y B) S
    (A x) (U x) (V x) z)}.
Proof.
  intros HS HA HU HV; unfold lower_inner_covariance.
  apply (gibbs_covariance_continuous gamma
    (fun s x => lower_block_scores n m y B z s (A x))
    (fun s x => lower_block_scores n m y B z s (U x))
    (fun s x => lower_block_scores n m y B z s (V x)) S q); try assumption;
    intros; apply block_score_along_continuous; assumption.
Qed.

Lemma block_inner_cumulant_along_continuous {E : topologicalType} n m gamma y B S z
    (A U V W : E -> block_array n m) q :
  S<>[] -> {for q, continuous A} -> {for q, continuous U} -> {for q, continuous V} ->
  {for q, continuous W} ->
  {for q, continuous (fun x => lower_inner_cumulant gamma (lower_block_scores n m y B) S
    (A x) (U x) (V x) (W x) z)}.
Proof.
  intros HS HA HU HV HW; unfold lower_inner_cumulant.
  apply (gibbs_cumulant3_continuous gamma
    (fun s x => lower_block_scores n m y B z s (A x))
    (fun s x => lower_block_scores n m y B z s (U x))
    (fun s x => lower_block_scores n m y B z s (V x))
    (fun s x => lower_block_scores n m y B z s (W x)) S q); try assumption;
    intros; apply block_score_along_continuous; assumption.
Qed.

Theorem block_first_along_continuous {E : topologicalType} n m beta gamma y B Y S
    (A U : E -> block_array n m) q :
  0<gamma -> Y<>[] -> S<>[] -> {for q, continuous A} -> {for q, continuous U} ->
  {for q, continuous (fun x => lower_block_first n m beta gamma y B Y S (A x) (U x))}.
Proof.
  intros Hg HY HS HA HU; unfold lower_block_first, lower_first.
  apply (gibbs_average_continuous (-beta)
    (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
    (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (U x) z) Y q).
  - exact HY.
  - intros; apply block_inner_value_along_continuous; assumption.
  - intros; apply block_inner_first_along_continuous; assumption.
Qed.

Theorem block_third_along_continuous {E : topologicalType} n m beta gamma y B Y S
    (A U V W : E -> block_array n m) q :
  0<gamma -> Y<>[] -> S<>[] -> {for q, continuous A} -> {for q, continuous U} ->
  {for q, continuous V} -> {for q, continuous W} ->
  {for q, continuous (fun x =>
    lower_block_third n m beta gamma y B Y S (A x) (U x) (V x) (W x))}.
Proof.
  intros Hg HY HS HA HU HV HW; unfold lower_block_third, lower_third.
  apply continuous_Rplus_fct.
  - apply continuous_Rminus_fct.
    + apply continuous_Rmult_fct; [apply: cst_continuous|].
      apply (gibbs_average_continuous (-beta)
        (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
        (fun z x => lower_inner_cumulant gamma (lower_block_scores n m y B) S (A x) (U x) (V x) (W x) z) Y q).
      * exact HY.
      * intros z Hz; exact (block_inner_value_along_continuous n m gamma y B S z A q Hg HS HA).
      * intros z Hz; exact (block_inner_cumulant_along_continuous n m gamma y B S z A U V W q HS HA HU HV HW).
    + apply continuous_Rmult_fct; [apply: cst_continuous|].
      apply continuous_Rplus_fct.
      * apply continuous_Rplus_fct.
        -- apply (gibbs_covariance_continuous (-beta) (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
            (fun z x => lower_inner_covariance gamma (lower_block_scores n m y B) S (A x) (U x) (V x) z) (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (W x) z) Y q).
           ++ exact HY.
           ++ intros z Hz; exact (block_inner_value_along_continuous n m gamma y B S z A q Hg HS HA).
           ++ intros z Hz; exact (block_inner_covariance_along_continuous n m gamma y B S z A U V q HS HA HU HV).
           ++ intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A W q HS HA HW).
        -- apply (gibbs_covariance_continuous (-beta) (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
            (fun z x => lower_inner_covariance gamma (lower_block_scores n m y B) S (A x) (U x) (W x) z) (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (V x) z) Y q).
           ++ exact HY.
           ++ intros z Hz; exact (block_inner_value_along_continuous n m gamma y B S z A q Hg HS HA).
           ++ intros z Hz; exact (block_inner_covariance_along_continuous n m gamma y B S z A U W q HS HA HU HW).
           ++ intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A V q HS HA HV).
      * apply (gibbs_covariance_continuous (-beta) (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
          (fun z x => lower_inner_covariance gamma (lower_block_scores n m y B) S (A x) (V x) (W x) z) (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (U x) z) Y q).
         ++ exact HY.
         ++ intros z Hz; exact (block_inner_value_along_continuous n m gamma y B S z A q Hg HS HA).
         ++ intros z Hz; exact (block_inner_covariance_along_continuous n m gamma y B S z A V W q HS HA HV HW).
         ++ intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A U q HS HA HU).
  - apply continuous_Rmult_fct; [apply: cst_continuous|].
    apply (gibbs_cumulant3_continuous (-beta) (fun z x => lower_inner_value gamma (lower_block_scores n m y B) S (A x) z)
      (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (U x) z) (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (V x) z) (fun z x => lower_inner_first gamma (lower_block_scores n m y B) S (A x) (W x) z) Y q).
    + exact HY.
    + intros z Hz; exact (block_inner_value_along_continuous n m gamma y B S z A q Hg HS HA).
    + intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A U q HS HA HU).
    + intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A V q HS HA HV).
    + intros z Hz; exact (block_inner_first_along_continuous n m gamma y B S z A W q HS HA HW).
Qed.
