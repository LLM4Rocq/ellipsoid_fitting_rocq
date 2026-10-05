From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights GibbsMomentBounds
  MatrixDefinitions OperatorDefinitions LowerDefinitions LowerNormBounds LowerFrechet.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/LowerBounds.v from Coquelicot to MathComp-Analysis.

   Every theorem of the original keeps its name and its arguments, in the
   same order. No lemma is added. The statements change form in four ways,
   the ways of the ports of LowerNormBounds and LowerFrechet, which this
   module imports, and of the restated challenge ellipsoid_lower_bounds in
   analysis/challenges.

   1. Norms. Coquelicot's norm U becomes MathComp's norm (`|U|)%R. On
      block_array n m it is the norm of LowerDefinitions, the square root of
      the sum of the squared Frobenius norms of the blocks, as in the
      original, because the port of MatrixDefinitions nests
      euclidean_product of MatrixEuclideanProduct and keeps Coquelicot's
      product norm. So the constants sqrt (INR (S n)) and
      2 * INR (S n) * k ^ 2 * (beta + gamma) are stated against the same
      norm as before. Comparisons, products and powers around the norms are
      Stdlib's.

   2. NormedModule R_AbsRing becomes normedModType R in
      lower_first_uniform_bound and lower_second_uniform_bound. The space E
      is only the type of the points A, U, V and of the arguments of F, so
      the values are those of the original.

   3. Frechet derivatives. Coquelicot's filterdiff f (locally A) l becomes
      is_diff A f l of MathComp-Analysis in
      lower_block_uniform_derivative_bounds, as in lower_block_derivatives of
      the port of LowerFrechet: f is differentiable at A and its differential
      'd f A is l, which is linear and continuous. The real-valued maps are
      typed into R^o, the normed module view of R, which is R by definition.

   4. Lists. With ssreflect loaded, the bare name seq means MathComp's type
      of sequences, so Stdlib's seq 0 (S m) is written List.seq 0 (S m), as
      in the port of LowerDefinitions. The list is the same.

   The proofs keep their steps. norm_ge_0 becomes normr_ge0 through RleP,
   and Stdlib's "rewrite A, B" and "rewrite ... by tac" are written in the
   forms that ssreflect accepts. *)

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
