From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Soft.Definitions Gibbs.Definitions
  Gibbs.Weights Gibbs.MomentBounds Matrix.Definitions
  Matrix.OperatorDefinitions Soft.MinimaxDerivativeDefinitions
  Soft.BlockScoreBounds Soft.MinimaxFrechet.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Uniform bounds on lower_first and lower_second of Soft.MinimaxDerivativeDefinitions, the
   first two derivatives of the nested soft minimax, when the scores
   satisfy |F z s W| <= K * |W|:
   - lower_gibbs_covariance_uniform_bound: if |u| <= Ku and |v| <= Kv on
     I, the Gibbs covariance of u and v is at most 2 * Ku * Kv in absolute
     value;
   - lower_first_uniform_bound: |lower_first ... A U| <= K * |U|;
   - lower_second_uniform_bound:
     |lower_second ... A U V| <= 2 * K ^ 2 * (beta + gamma) * |U| * |V|;
   - lower_block_first_bound: for the block scores, with rows y z of unit
     Euclidean norm and matrices B s of operator norm at most k,
     |lower_block_first ... A U| <= sqrt (n + 1) * k * |U|.
   The space E is any normedModType R. On block_array n m the norm
   (`|U|)%R is the square root of the sum of the squared Frobenius norms of
   the blocks. With ssreflect loaded, Stdlib's seq 0 (S m) is written
   List.seq 0 (S m). *)

Theorem lower_gibbs_covariance_uniform_bound c f I u v Ku Kv :
  I <> [] -> 0 <= Ku -> 0 <= Kv ->
  (forall i, In i I -> Rabs (u i) <= Ku) ->
  (forall i, In i I -> Rabs (v i) <= Kv) ->
  Rabs (gibbs_covariance c f I u v) <= 2 * Ku * Kv.
Proof.
  intros HI HKu HKv Hu Hv.
  pose proof (gibbs_mean_uniform_bound c f I u Ku HI Hu) as HU.
  pose proof (gibbs_mean_uniform_bound c f I v Kv HI Hv) as HV.
  assert (HUV : Rabs (gibbs_average c f I (fun i => u i * v i)) <= Ku * Kv).
  { apply gibbs_mean_uniform_bound; [exact HI|]; intros i Hi; rewrite Rabs_mult.
    apply Rmult_le_compat; try apply Rabs_pos; [apply Hu|apply Hv]; exact Hi. }
  assert (Hprod : Rabs (gibbs_average c f I u) * Rabs (gibbs_average c f I v) <= Ku * Kv).
  { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  unfold gibbs_covariance; eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp Rabs_mult; nra.
Qed.

Theorem lower_first_uniform_bound {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U : E) K :
  Y <> [] -> S <> [] ->
  (forall z s, In z Y -> In s S -> Rabs (F z s U) <= K * (`|U|)%R) ->
  Rabs (lower_first beta gamma F Y S A U) <= K * (`|U|)%R.
Proof.
  intros HY HS HF; unfold lower_first.
  apply gibbs_mean_uniform_bound; [exact HY|]; intros z Hz.
  unfold lower_inner_first; apply gibbs_mean_uniform_bound; [exact HS|].
  intros s Hs; apply HF; assumption.
Qed.

Theorem lower_second_uniform_bound {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V : E) K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= K ->
  (forall z s, In z Y -> In s S -> forall W : E, Rabs (F z s W) <= K * (`|W|)%R) ->
  Rabs (lower_second beta gamma F Y S A U V) <=
    2 * K ^ 2 * (beta + gamma) * (`|U|)%R * (`|V|)%R.
Proof.
  intros Hb Hg HY HS HK HF.
  assert (HKU : 0 <= K * (`|U|)%R).
  { apply Rmult_le_pos; [exact HK|apply/RleP; apply normr_ge0]. }
  assert (HKV : 0 <= K * (`|V|)%R).
  { apply Rmult_le_pos; [exact HK|apply/RleP; apply normr_ge0]. }
  assert (HM : forall z W, In z Y ->
    Rabs (lower_inner_first gamma F S A W z) <= K * (`|W|)%R).
  { intros z W Hz; apply gibbs_mean_uniform_bound; [exact HS|].
    intros s Hs; apply HF; assumption. }
  assert (HC : forall z, In z Y ->
    Rabs (lower_inner_covariance gamma F S A U V z) <=
      2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { intros z Hz; apply lower_gibbs_covariance_uniform_bound; try assumption.
    - intros s Hs; apply HF; assumption.
    - intros s Hs; apply HF; assumption. }
  assert (HI : Rabs (gibbs_average (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_covariance gamma F S A U V)) <= 2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { apply gibbs_mean_uniform_bound; assumption. }
  assert (HO : Rabs (gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)) <=
    2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { apply lower_gibbs_covariance_uniform_bound; try assumption.
    - intros z Hz; apply HM; exact Hz.
    - intros z Hz; apply HM; exact Hz. }
  unfold lower_second; eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp !Rabs_mult.
  rewrite (Rabs_pos_eq gamma (Rlt_le _ _ Hg)) (Rabs_pos_eq beta (Rlt_le _ _ Hb)).
  replace (2 * K ^ 2 * (beta + gamma) * (`|U|)%R * (`|V|)%R) with
    (gamma * (2 * (K * (`|U|)%R) * (K * (`|V|)%R)) +
      beta * (2 * (K * (`|U|)%R) * (K * (`|V|)%R))) by ring.
  apply Rplus_le_compat; apply Rmult_le_compat_l; try lra; assumption.
Qed.

Theorem lower_block_first_bound n m beta gamma y B Y S (A U : block_array n m) k :
  Y <> [] -> S <> [] -> 0 <= k ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall s, In s S -> matrix_operator_norm n (B s) <= k) ->
  Rabs (lower_block_first n m beta gamma y B Y S A U) <=
    sqrt (INR (Datatypes.S n)) * k * (`|U|)%R.
Proof.
  intros HY HS Hk Hunit HB; apply lower_first_uniform_bound; try assumption.
  intros z s Hz Hs; apply (lower_block_score_bound n m y B S k z s U); try assumption.
  apply Hunit; exact Hz.
Qed.
