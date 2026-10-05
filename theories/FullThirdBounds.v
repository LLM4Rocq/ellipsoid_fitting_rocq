From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights GibbsMomentBounds
  ThirdDefinitions MatrixDefinitions OperatorDefinitions LowerDefinitions LowerNormBounds
  LowerFrechet LowerBounds FullThirdDefinitions FullThirdFrechet FullThirdContinuity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/FullThirdBounds.v from Coquelicot to MathComp-Analysis.

   Both theorems keep their names and their arguments, in the same order. No
   lemma is added.

   lower_gibbs_cumulant_uniform_bound mentions no normed space, and its text
   is the original's.

   lower_third_uniform_bound changes form in two ways, the ways of
   lower_second_uniform_bound in the port of LowerBounds and of clause 4 of
   the restated challenge ellipsoid_full_third in analysis/challenges.

   1. NormedModule R_AbsRing becomes normedModType R. The space E is only the
      type of the points A, U, V, W and of the arguments of F, so the values
      are those of the original.

   2. Coquelicot's norm P becomes MathComp's norm (`|P|)%R, the norm of E.
      The constant 8 * K ^ 3 * (beta + gamma) ^ 2 is stated against it as
      before. Comparisons, products and powers around the norms are
      Stdlib's.

   The proofs keep their steps. norm_ge_0 becomes normr_ge0 through RleP,
   and Stdlib's "rewrite A, B" and "rewrite ... by tac" are written in the
   forms that ssreflect accepts. *)

Theorem lower_gibbs_cumulant_uniform_bound c f I u v w Ku Kv Kw :
  I <> [] -> 0 <= Ku -> 0 <= Kv -> 0 <= Kw ->
  (forall i, In i I -> Rabs (u i) <= Ku) ->
  (forall i, In i I -> Rabs (v i) <= Kv) ->
  (forall i, In i I -> Rabs (w i) <= Kw) ->
  Rabs (gibbs_cumulant3 c f I u v w) <= 8 * Ku * Kv * Kw.
Proof.
  intros HI HKu HKv HKw Hu Hv Hw.
  assert (HC : forall h K, (forall i, In i I -> Rabs (h i) <= K) ->
    forall i, In i I -> Rabs (h i - gibbs_average c f I h) <= 2 * K).
  { intros h K Hh i Hi.
    pose proof (gibbs_mean_uniform_bound c f I h K HI Hh).
    pose proof (Hh i Hi).
    eapply Rle_trans; [apply Rabs_triang|]; rewrite Rabs_Ropp; lra. }
  unfold gibbs_cumulant3; apply gibbs_mean_uniform_bound; [exact HI|].
  intros i Hi; rewrite !Rabs_mult.
  replace (8 * Ku * Kv * Kw) with ((2 * Ku) * (2 * Kv) * (2 * Kw)) by ring.
  apply Rmult_le_compat; try (apply Rmult_le_pos; apply Rabs_pos); try apply Rabs_pos.
  - apply Rmult_le_compat; try apply Rabs_pos; apply HC; assumption.
  - apply HC; assumption.
Qed.

Theorem lower_third_uniform_bound {E : normedModType R} beta gamma
    (F : nat -> nat -> E -> R) Y S (A U V W : E) K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= K ->
  (forall z s, In z Y -> In s S -> forall P : E, Rabs (F z s P) <= K * (`|P|)%R) ->
  Rabs (lower_third beta gamma F Y S A U V W) <=
    8 * K ^ 3 * (beta + gamma) ^ 2 * (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  intros Hb Hg HY HS HK HL.
  assert (HN : forall P : E, 0 <= K * (`|P|)%R).
  { intros; apply Rmult_le_pos; [exact HK|apply/RleP; apply normr_ge0]. }
  assert (HM : forall P z, In z Y ->
    Rabs (lower_inner_first gamma F S A P z) <= K * (`|P|)%R).
  { intros P z Hz; apply gibbs_mean_uniform_bound; [exact HS|]; intros s Hs; apply HL; assumption. }
  assert (HC : forall P Q z, In z Y ->
    Rabs (lower_inner_covariance gamma F S A P Q z) <=
      2 * (K * (`|P|)%R) * (K * (`|Q|)%R)).
  { intros P Q z Hz; apply lower_gibbs_covariance_uniform_bound; try assumption; try apply HN;
      intros s Hs; apply HL; assumption. }
  assert (HI : Rabs (gibbs_average (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_cumulant gamma F S A U V W)) <=
      8 * (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  { apply gibbs_mean_uniform_bound; [exact HY|]; intros z Hz.
    apply lower_gibbs_cumulant_uniform_bound; try assumption; try apply HN;
      intros s Hs; apply HL; assumption. }
  assert (HOC : forall P Q R, Rabs (gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_covariance gamma F S A P Q) (lower_inner_first gamma F S A R)) <=
    4 * (K * (`|P|)%R) * (K * (`|Q|)%R) * (K * (`|R|)%R)).
  { intros P Q R.
    replace (4 * (K * (`|P|)%R) * (K * (`|Q|)%R) * (K * (`|R|)%R)) with
      (2 * (2 * (K * (`|P|)%R) * (K * (`|Q|)%R)) * (K * (`|R|)%R)) by ring.
    apply lower_gibbs_covariance_uniform_bound; try assumption; try apply HN.
    - pose proof (HN P); pose proof (HN Q); nra.
    - intros z Hz; apply HC; exact Hz.
    - intros z Hz; apply HM; exact Hz. }
  assert (HOT : Rabs (gibbs_cumulant3 (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)
    (lower_inner_first gamma F S A W)) <=
      8 * (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  { apply lower_gibbs_cumulant_uniform_bound; try assumption; try apply HN;
      intros z Hz; apply HM; exact Hz. }
  pose proof (HOC U V W) as H1; pose proof (HOC U W V) as H2; pose proof (HOC V W U) as H3.
  set (T := (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  assert (HT : 0 <= T) by (unfold T; apply Rmult_le_pos; [apply Rmult_le_pos|]; apply HN).
  assert (HSum : Rabs (
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U V) (lower_inner_first gamma F S A W) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U W) (lower_inner_first gamma F S A V) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A V W) (lower_inner_first gamma F S A U)) <= 12 * T).
  { eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|].
    unfold T; nra. }
  unfold lower_third; eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|].
  (* ssreflect's rewrite matches up to conversion, so a bare !Rabs_mult
     would also unfold gamma ^ 2 into a product. The instances are given. *)
  rewrite Rabs_Ropp (Rabs_mult (gamma ^ 2)) (Rabs_mult (beta * gamma)).
  rewrite (Rabs_mult beta gamma) (Rabs_mult (beta ^ 2)).
  assert (Hg2 : 0 <= gamma ^ 2) by nra.
  assert (Hb2 : 0 <= beta ^ 2) by nra.
  rewrite (Rabs_pos_eq (gamma ^ 2) Hg2) (Rabs_pos_eq (beta ^ 2) Hb2).
  rewrite (Rabs_pos_eq beta (Rlt_le _ _ Hb)) (Rabs_pos_eq gamma (Rlt_le _ _ Hg)).
  assert (HHI : gamma ^ 2 * Rabs (gibbs_average (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_cumulant gamma F S A U V W)) <= gamma ^ 2 * (8 * T)).
  { apply Rmult_le_compat_l; [nra|unfold T; nra]. }
  assert (HHT : beta ^ 2 * Rabs (gibbs_cumulant3 (- beta) (lower_inner_value gamma F S A) Y
    (lower_inner_first gamma F S A U) (lower_inner_first gamma F S A V)
    (lower_inner_first gamma F S A W)) <= beta ^ 2 * (8 * T)).
  { apply Rmult_le_compat_l; [nra|unfold T; nra]. }
  assert (HHS : beta * gamma * Rabs (
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U V) (lower_inner_first gamma F S A W) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A U W) (lower_inner_first gamma F S A V) +
    gibbs_covariance (- beta) (lower_inner_value gamma F S A) Y
      (lower_inner_covariance gamma F S A V W) (lower_inner_first gamma F S A U)) <= beta * gamma * (12 * T)).
  { apply Rmult_le_compat_l; [nra|exact HSum]. }
  replace (8 * K ^ 3 * (beta + gamma) ^ 2 * (`|U|)%R * (`|V|)%R * (`|W|)%R) with
    (8 * (beta + gamma) ^ 2 * T) by (unfold T; ring).
  assert (0 <= beta * gamma * T) by (apply Rmult_le_pos; [nra|exact HT]).
  nra.
Qed.
