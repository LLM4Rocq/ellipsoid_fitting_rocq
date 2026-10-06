From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions
  MatrixDefinitions MatrixCoordinates OperatorDefinitions MatrixGibbsDefinitions
  MatrixSecondDefinitions MatrixThirdDefinitions GradientDefinitions MatrixGradient
  CoefficientBounds HessianDefinitions MatrixHessian QuadraticDefinitions
  QuadraticCalculus ContinuityDefinitions CoefficientDefinitions CoefficientMaps
  FiniteGibbsContinuity MatrixThirdContinuity QuadraticGradient.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Regularity of the gradient of the soft minimax along the quadratic map
   x |-> quadratic_matrix n lambda C x = C + lambda * (x x^T - I), in four
   submodules that importers name. QuadraticUniformBounds bounds Gibbs
   averages, covariances and cumulants, and the second and third
   derivatives of the soft minimax (growth_matrix_second_bound,
   growth_matrix_third_bound). QuadraticPolynomialGrowth bounds the entries
   of the gradient and of its first two derivatives in x by polynomials of
   degree 0, 1 and 2 in `|x| (quadratic_gradient_entries_polynomial_growth).
   QuadraticGrowthContinuity proves their continuity, and QuadraticGrowth
   gathers everything (quadratic_gradient_entry_polynomial_regular).

   Plain apply of the lemmas growth_..._continuous does not find the
   topology of a concrete domain such as vector n: use ssreflect's apply:,
   or give the domain E explicitly. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac growth_norm_nonneg := apply/RleP; apply normr_ge0.

Module QuadraticUniformBounds.
Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions MatrixDefinitions
  MatrixCoordinates OperatorDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions
  MatrixThirdDefinitions GradientDefinitions MatrixGradient CoefficientBounds.

Lemma growth_gibbs_mean_bound c f I u K :
  I <> [] -> (forall i, In i I -> Rabs (u i) <= K) ->
  Rabs (gibbs_average c f I u) <= K.
Proof.
  intros HI Hu; apply Rabs_le; split.
  - assert (H : 0 <= gibbs_average c f I (fun i => u i + K)).
    { apply gibbs_average_nonnegative; [exact HI|].
      intros i Hi; pose proof (Hu i Hi) as H1; pose proof (Rle_abs (- u i)) as H2.
      rewrite Rabs_Ropp in H2; lra. }
    rewrite gibbs_average_add (gibbs_average_const c f I K HI) in H; lra.
  - assert (H : 0 <= gibbs_average c f I (fun i => K + (-1) * u i)).
    { apply gibbs_average_nonnegative; [exact HI|].
      intros i Hi; pose proof (Hu i Hi) as H1; pose proof (Rle_abs (u i)) as H2; lra. }
    rewrite gibbs_average_add (gibbs_average_const c f I K HI) gibbs_average_scale in H.
    lra.
Qed.

Theorem growth_gibbs_covariance_bound c f I u v Ku Kv :
  I <> [] -> 0 <= Ku -> 0 <= Kv ->
  (forall i, In i I -> Rabs (u i) <= Ku) ->
  (forall i, In i I -> Rabs (v i) <= Kv) ->
  Rabs (gibbs_covariance c f I u v) <= 2 * Ku * Kv.
Proof.
  intros HI HKu HKv Hu Hv.
  pose proof (growth_gibbs_mean_bound c f I u Ku HI Hu) as HU.
  pose proof (growth_gibbs_mean_bound c f I v Kv HI Hv) as HV.
  assert (HUV : Rabs (gibbs_average c f I (fun i => u i * v i)) <= Ku * Kv).
  { apply growth_gibbs_mean_bound; [exact HI|]; intros i Hi; rewrite Rabs_mult.
    apply Rmult_le_compat; try apply Rabs_pos; [apply Hu|apply Hv]; exact Hi. }
  assert (Hprod : Rabs (gibbs_average c f I u) * Rabs (gibbs_average c f I v) <= Ku * Kv).
  { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  unfold gibbs_covariance; eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp Rabs_mult; nra.
Qed.

Theorem growth_gibbs_cumulant_bound c f I u v w Ku Kv Kw :
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
    pose proof (growth_gibbs_mean_bound c f I h K HI Hh) as H1.
    pose proof (Hh i Hi) as H2.
    eapply Rle_trans; [apply Rabs_triang|]; rewrite Rabs_Ropp; lra. }
  unfold gibbs_cumulant3; apply growth_gibbs_mean_bound; [exact HI|].
  intros i Hi; rewrite !Rabs_mult.
  replace (8 * Ku * Kv * Kw) with ((2 * Ku) * (2 * Kv) * (2 * Kw)) by ring.
  apply Rmult_le_compat; try (apply Rmult_le_pos; apply Rabs_pos); try apply Rabs_pos.
  - apply Rmult_le_compat; try apply Rabs_pos; apply HC; assumption.
  - apply HC; assumption.
Qed.

Theorem growth_matrix_second_bound n beta gamma offset coeff Y S (A U V : matrix n) K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= K ->
  (forall z s, In z Y -> In s S -> forall W : matrix n,
    Rabs (trace_pair n (coeff z s) W) <= K * (`|W|)%R) ->
  Rabs (matrix_nested_second_derivative n beta gamma offset coeff Y S A U V) <=
    2 * K ^ 2 * (beta + gamma) * (`|U|)%R * (`|V|)%R.
Proof.
  intros Hb Hg HY HS HK HF.
  assert (HKU : 0 <= K * (`|U|)%R) by (apply Rmult_le_pos; [exact HK|growth_norm_nonneg]).
  assert (HKV : 0 <= K * (`|V|)%R) by (apply Rmult_le_pos; [exact HK|growth_norm_nonneg]).
  assert (HM : forall z W, In z Y ->
    Rabs (matrix_inner_derivative n gamma offset coeff S A W z) <= K * (`|W|)%R).
  { intros z W Hz; apply growth_gibbs_mean_bound; [exact HS|]; intros s Hs; apply HF; assumption. }
  assert (HC : forall z, In z Y ->
    Rabs (matrix_inner_covariance n gamma offset coeff S A U V z) <=
      2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { intros z Hz; apply growth_gibbs_covariance_bound; try assumption.
    - intros s Hs; apply HF; assumption.
    - intros s Hs; apply HF; assumption. }
  assert (HI : Rabs (gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_covariance n gamma offset coeff S A U V)) <=
      2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { apply growth_gibbs_mean_bound; assumption. }
  assert (HO : Rabs (gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)) <=
    2 * (K * (`|U|)%R) * (K * (`|V|)%R)).
  { apply growth_gibbs_covariance_bound; try assumption; intros z Hz; apply HM; exact Hz. }
  unfold matrix_nested_second_derivative; eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp !Rabs_mult.
  rewrite (Rabs_pos_eq gamma (Rlt_le _ _ Hg)) (Rabs_pos_eq beta (Rlt_le _ _ Hb)).
  replace (2 * K ^ 2 * (beta + gamma) * (`|U|)%R * (`|V|)%R) with
    (gamma * (2 * (K * (`|U|)%R) * (K * (`|V|)%R)) +
     beta * (2 * (K * (`|U|)%R) * (K * (`|V|)%R))) by ring.
  apply Rplus_le_compat; apply Rmult_le_compat_l; try lra; assumption.
Qed.

Theorem growth_matrix_third_bound n beta gamma offset coeff Y S (A U V W : matrix n) K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= K ->
  (forall z s, In z Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff z s) P) <= K * (`|P|)%R) ->
  Rabs (matrix_nested_third_derivative n beta gamma offset coeff Y S A U V W) <=
    8 * K ^ 3 * (beta + gamma) ^ 2 * (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  intros Hb Hg HY HS HK HL.
  assert (HN : forall P : matrix n, 0 <= K * (`|P|)%R).
  { intros; apply Rmult_le_pos; [exact HK|growth_norm_nonneg]. }
  assert (HM : forall P z, In z Y ->
    Rabs (matrix_inner_derivative n gamma offset coeff S A P z) <= K * (`|P|)%R).
  { intros P z Hz; apply growth_gibbs_mean_bound; [exact HS|]; intros s Hs; apply HL; assumption. }
  assert (HC : forall P Q z, In z Y ->
    Rabs (matrix_inner_covariance n gamma offset coeff S A P Q z) <=
      2 * (K * (`|P|)%R) * (K * (`|Q|)%R)).
  { intros P Q z Hz; apply growth_gibbs_covariance_bound; try assumption; try apply HN;
      intros s Hs; apply HL; assumption. }
  assert (HI : Rabs (gibbs_average (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_cumulant n gamma offset coeff S A U V W)) <=
      8 * (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  { apply growth_gibbs_mean_bound; [exact HY|]; intros z Hz.
    apply growth_gibbs_cumulant_bound; try assumption; try apply HN;
      intros s Hs; apply HL; assumption. }
  assert (HOC : forall P Q R, Rabs (gibbs_covariance (- beta)
    (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_covariance n gamma offset coeff S A P Q)
    (matrix_inner_derivative n gamma offset coeff S A R)) <=
    4 * (K * (`|P|)%R) * (K * (`|Q|)%R) * (K * (`|R|)%R)).
  { intros P Q R.
    replace (4 * (K * (`|P|)%R) * (K * (`|Q|)%R) * (K * (`|R|)%R)) with
      (2 * (2 * (K * (`|P|)%R) * (K * (`|Q|)%R)) * (K * (`|R|)%R)) by ring.
    apply growth_gibbs_covariance_bound; try assumption; try apply HN.
    - pose proof (HN P); pose proof (HN Q); nra.
    - intros z Hz; apply HC; exact Hz.
    - intros z Hz; apply HM; exact Hz. }
  assert (HOT : Rabs (gibbs_cumulant3 (- beta) (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)
    (matrix_inner_derivative n gamma offset coeff S A W)) <=
      8 * (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  { apply growth_gibbs_cumulant_bound; try assumption; try apply HN;
      intros z Hz; apply HM; exact Hz. }
  pose proof (HOC U V W) as H1; pose proof (HOC U W V) as H2; pose proof (HOC V W U) as H3.
  set (T := (K * (`|U|)%R) * (K * (`|V|)%R) * (K * (`|W|)%R)).
  assert (HT : 0 <= T) by (unfold T; apply Rmult_le_pos; [apply Rmult_le_pos|]; apply HN).
  assert (HSum : Rabs (
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A U V)
      (matrix_inner_derivative n gamma offset coeff S A W) +
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A U W)
      (matrix_inner_derivative n gamma offset coeff S A V) +
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A V W)
      (matrix_inner_derivative n gamma offset coeff S A U)) <= 12 * T).
  { eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|].
    unfold T; nra. }
  unfold matrix_nested_third_derivative; eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang|apply Rle_refl]|].
  (* Stdlib's rewrite, written with ->, which ssreflect leaves to Stdlib: the
     ssreflect rewrite would also expand gamma ^ 2 into a product. *)
  rewrite -> Rabs_Ropp, !Rabs_mult.
  rewrite (Rabs_pos_eq (gamma ^ 2) (pow2_ge_0 gamma)).
  rewrite (Rabs_pos_eq (beta ^ 2) (pow2_ge_0 beta)).
  rewrite (Rabs_pos_eq beta (Rlt_le _ _ Hb)) (Rabs_pos_eq gamma (Rlt_le _ _ Hg)).
  assert (HHI : gamma ^ 2 * Rabs (gibbs_average (- beta)
    (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_cumulant n gamma offset coeff S A U V W)) <= gamma ^ 2 * (8 * T)).
  { apply Rmult_le_compat_l; [nra|unfold T; nra]. }
  assert (HHT : beta ^ 2 * Rabs (gibbs_cumulant3 (- beta)
    (matrix_inner_values n gamma offset coeff S A) Y
    (matrix_inner_derivative n gamma offset coeff S A U)
    (matrix_inner_derivative n gamma offset coeff S A V)
    (matrix_inner_derivative n gamma offset coeff S A W)) <= beta ^ 2 * (8 * T)).
  { apply Rmult_le_compat_l; [nra|unfold T; nra]. }
  assert (HHS : beta * gamma * Rabs (
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A U V)
      (matrix_inner_derivative n gamma offset coeff S A W) +
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A U W)
      (matrix_inner_derivative n gamma offset coeff S A V) +
    gibbs_covariance (- beta) (matrix_inner_values n gamma offset coeff S A) Y
      (matrix_inner_covariance n gamma offset coeff S A V W)
      (matrix_inner_derivative n gamma offset coeff S A U)) <= beta * gamma * (12 * T)).
  { apply Rmult_le_compat_l; [nra|exact HSum]. }
  replace (8 * K ^ 3 * (beta + gamma) ^ 2 * (`|U|)%R * (`|V|)%R * (`|W|)%R) with
    (8 * (beta + gamma) ^ 2 * T) by (unfold T; ring).
  assert (0 <= beta * gamma * T) by (apply Rmult_le_pos; [nra|exact HT]).
  match type of HHI with ?a <= _ => match type of HHS with ?b <= _ =>
    match type of HHT with ?c <= _ =>
      change (a + b + c <= 8 * (beta + gamma) ^ 2 * T) end end end.
  nra.
Qed.

End QuadraticUniformBounds.

Module QuadraticPolynomialGrowth.
Import SoftDefinitions GibbsDefinitions GibbsWeights MatrixDefinitions MatrixCoordinates
  OperatorDefinitions MatrixGibbsDefinitions MatrixSecondDefinitions MatrixThirdDefinitions
  GradientDefinitions MatrixGradient HessianDefinitions MatrixHessian CoefficientBounds
  QuadraticDefinitions QuadraticCalculus QuadraticUniformBounds.

Lemma growth_finite_coefficient_bound n (coeff : nat -> nat -> matrix n) Y S :
  exists K : R, 0 <= K /\ forall y s, In y Y -> In s S -> (`|coeff y s|)%R <= K.
Proof.
  exists (finite_sum (fun y => finite_sum (fun s => (`|coeff y s|)%R) S) Y).
  assert (H0 : forall y s, 0 <= (`|coeff y s|)%R) by (intros; growth_norm_nonneg).
  assert (HN : forall y, 0 <= finite_sum (fun s => (`|coeff y s|)%R) S).
  { intros; apply gibbs_sum_nonnegative; intros; apply H0. }
  split; [apply gibbs_sum_nonnegative; intros; apply HN|].
  intros y s Hy Hs; eapply Rle_trans with (finite_sum (fun t => (`|coeff y t|)%R) S).
  - exact (gibbs_sum_member (fun t => (`|coeff y t|)%R) S s (fun t _ => H0 y t) Hs).
  - exact (gibbs_sum_member (fun z => finite_sum (fun t => (`|coeff z t|)%R) S) Y y
      (fun z _ => HN z) Hy).
Qed.

Lemma growth_trace_coefficient_bound n (coeff : nat -> nat -> matrix n) Y S K :
  (forall y s, In y Y -> In s S -> (`|coeff y s|)%R <= K) ->
  forall y s, In y Y -> In s S -> forall U : matrix n,
  Rabs (trace_pair n (coeff y s) U) <= (INR (Datatypes.S n) ^ 2 * K) * (`|U|)%R.
Proof.
  intros HK y s Hy Hs U; eapply Rle_trans; [apply trace_pair_product_bound|].
  apply Rmult_le_compat_r; [growth_norm_nonneg|].
  apply Rmult_le_compat_l; [apply pow2_ge_0|apply HK; assumption].
Qed.

Lemma growth_matrix_basis_norm n i j : (`|matrix_basis n i j|)%R <= INR (S n) ^ 2.
Proof.
  unfold matrix_basis; replace (INR (S n) ^ 2) with (INR (S n) ^ 2 * 1) by ring.
  apply matrix_build_norm_bound; [lra|].
  intros r c Hr Hc; destruct (Nat.eqb r i && Nat.eqb c j)%bool;
    rewrite ?Rabs_R1 ?Rabs_R0; lra.
Qed.

Lemma quadratic_first_norm_bound n lambda (x u : vector n) :
  (`|quadratic_first n lambda x u|)%R <=
    (2 * Rabs lambda * INR (S n) ^ 2) * (`|x|)%R * (`|u|)%R.
Proof.
  unfold quadratic_first.
  replace ((2 * Rabs lambda * INR (S n) ^ 2) * (`|x|)%R * (`|u|)%R) with
    (INR (S n) ^ 2 * (2 * Rabs lambda * (`|x|)%R * (`|u|)%R)) by ring.
  apply matrix_build_norm_bound.
  - repeat apply Rmult_le_pos; try lra; try apply Rabs_pos; growth_norm_nonneg.
  - intros i j Hi Hj; rewrite Rabs_mult.
    assert (H1 : Rabs (vector_entry n u i * vector_entry n x j) <= (`|u|)%R * (`|x|)%R).
    { rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; unfold vector_entry;
        rewrite RabsE; apply (tuple_entry_norm_bound R^o). }
    assert (H2 : Rabs (vector_entry n x i * vector_entry n u j) <= (`|x|)%R * (`|u|)%R).
    { rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; unfold vector_entry;
        rewrite RabsE; apply (tuple_entry_norm_bound R^o). }
    pose proof (Rabs_triang (vector_entry n u i * vector_entry n x j)
      (vector_entry n x i * vector_entry n u j)) as H3.
    pose proof (Rabs_pos lambda) as H4; nra.
Qed.

Lemma quadratic_second_norm_bound n lambda (u v : vector n) :
  (`|quadratic_second n lambda u v|)%R <=
    (2 * Rabs lambda * INR (S n) ^ 2) * (`|u|)%R * (`|v|)%R.
Proof.
  replace (quadratic_second n lambda u v) with (quadratic_first n lambda u v).
  - apply quadratic_first_norm_bound.
  - apply matrix_ext; intros i j Hi Hj; unfold quadratic_first, quadratic_second.
    rewrite (matrix_entry_build n _ i j Hi Hj) (matrix_entry_build n _ i j Hi Hj); ring.
Qed.

Theorem growth_gradient_entry_bound n beta gamma offset coeff Y S (A : matrix n) i j K :
  Y <> [] -> S <> [] -> (i <= n)%coq_nat -> (j <= n)%coq_nat ->
  (forall y s, In y Y -> In s S -> (`|coeff y s|)%R <= K) ->
  Rabs (matrix_entry n (matrix_nested_gradient n beta gamma offset coeff Y S A) i j) <= K.
Proof.
  intros HY HS Hi Hj HK.
  rewrite (matrix_nested_gradient_entry n beta gamma offset coeff Y S A i j Hi Hj).
  unfold matrix_nested_derivative; apply growth_gibbs_mean_bound; [exact HY|].
  intros y Hy; unfold matrix_inner_derivative; apply growth_gibbs_mean_bound; [exact HS|].
  intros s Hs; rewrite (trace_pair_basis n (coeff y s) i j Hi Hj).
  eapply Rle_trans; [apply matrix_entry_norm_bound|apply HK; assumption].
Qed.

Theorem growth_gradient_first_entry_bound n beta gamma offset coeff Y S (A U : matrix n) i j K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (i <= n)%coq_nat -> (j <= n)%coq_nat -> 0 <= K ->
  (forall y s, In y Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff y s) P) <= K * (`|P|)%R) ->
  Rabs (matrix_entry n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S A U) i j) <=
    (INR (Datatypes.S n) ^ 2 * (2 * K ^ 2 * (beta + gamma))) * (`|U|)%R.
Proof.
  intros Hb Hg HY HS Hi Hj HK HC; unfold matrix_nested_gradient_derivative.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  eapply Rle_trans; [apply growth_matrix_second_bound; eassumption|].
  replace (INR (Datatypes.S n) ^ 2 * (2 * K ^ 2 * (beta + gamma)) * (`|U|)%R) with
    (2 * K ^ 2 * (beta + gamma) * INR (Datatypes.S n) ^ 2 * (`|U|)%R) by ring.
  apply Rmult_le_compat_r; [growth_norm_nonneg|].
  apply Rmult_le_compat_l; [pose proof (pow2_ge_0 K); nra|apply growth_matrix_basis_norm].
Qed.

Theorem growth_gradient_second_entry_bound n beta gamma offset coeff Y S (A U V : matrix n) i j K :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (i <= n)%coq_nat -> (j <= n)%coq_nat -> 0 <= K ->
  (forall y s, In y Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff y s) P) <= K * (`|P|)%R) ->
  Rabs (matrix_entry n
    (matrix_nested_gradient_second_derivative n beta gamma offset coeff Y S A U V) i j) <=
    (INR (Datatypes.S n) ^ 2 * (8 * K ^ 3 * (beta + gamma) ^ 2)) * (`|U|)%R * (`|V|)%R.
Proof.
  intros Hb Hg HY HS Hi Hj HK HC; unfold matrix_nested_gradient_second_derivative.
  rewrite (matrix_entry_build n _ i j Hi Hj).
  eapply Rle_trans; [apply growth_matrix_third_bound; eassumption|].
  replace (INR (Datatypes.S n) ^ 2 * (8 * K ^ 3 * (beta + gamma) ^ 2) * (`|U|)%R * (`|V|)%R)
    with (8 * K ^ 3 * (beta + gamma) ^ 2 * INR (Datatypes.S n) ^ 2 * (`|U|)%R * (`|V|)%R)
    by ring.
  apply Rmult_le_compat_r; [growth_norm_nonneg|].
  apply Rmult_le_compat_r; [growth_norm_nonneg|].
  apply Rmult_le_compat_l.
  - repeat apply Rmult_le_pos; try lra; apply pow_le; lra.
  - apply growth_matrix_basis_norm.
Qed.

Theorem quadratic_gradient_entries_polynomial_growth n beta gamma offset coeff Y S lambda C
    (u v : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  exists K0 K1 K2 : R, 0 <= K0 /\ 0 <= K1 /\ 0 <= K2 /\ forall x : vector n,
    Rabs (matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)
      <= K0 * (1 + (`|x|)%R) ^ 0 /\
    Rabs (matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b)
      <= K1 * (1 + (`|x|)%R) ^ 1 /\
    Rabs (matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u v) a b)
      <= K2 * (1 + (`|x|)%R) ^ 2.
Proof.
  intros Hb Hg HY HS Ha Hbb.
  destruct (growth_finite_coefficient_bound n coeff Y S) as [K [HK HC]].
  set (D := INR (Datatypes.S n) ^ 2 * K).
  assert (HD : 0 <= D) by (unfold D; apply Rmult_le_pos; [apply pow2_ge_0|exact HK]).
  assert (HL : forall y s, In y Y -> In s S -> forall P : matrix n,
    Rabs (trace_pair n (coeff y s) P) <= D * (`|P|)%R).
  { apply growth_trace_coefficient_bound; exact HC. }
  set (B1 := INR (Datatypes.S n) ^ 2 * (2 * D ^ 2 * (beta + gamma))).
  set (B2 := INR (Datatypes.S n) ^ 2 * (8 * D ^ 3 * (beta + gamma) ^ 2)).
  set (J := 2 * Rabs lambda * INR (Datatypes.S n) ^ 2).
  assert (HB1 : 0 <= B1).
  { unfold B1; apply Rmult_le_pos; [apply pow2_ge_0|].
    apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|lra]. }
  assert (HB2 : 0 <= B2).
  { unfold B2; apply Rmult_le_pos; [apply pow2_ge_0|].
    apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact HD]|apply pow2_ge_0]. }
  assert (HJ : 0 <= J).
  { unfold J; apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply Rabs_pos]|apply pow2_ge_0]. }
  assert (Hu : 0 <= (`|u|)%R) by growth_norm_nonneg.
  assert (Hv : 0 <= (`|v|)%R) by growth_norm_nonneg.
  set (K1 := B1 * J * (`|u|)%R).
  set (K21 := B2 * J ^ 2 * (`|u|)%R * (`|v|)%R).
  set (K22 := B1 * J * (`|u|)%R * (`|v|)%R).
  assert (HK1 : 0 <= K1) by (unfold K1; apply Rmult_le_pos; [apply Rmult_le_pos; assumption|exact Hu]).
  assert (HK21 : 0 <= K21).
  { unfold K21; apply Rmult_le_pos; [|exact Hv].
    apply Rmult_le_pos; [|exact Hu].
    apply Rmult_le_pos; [exact HB2|apply pow2_ge_0]. }
  assert (HK22 : 0 <= K22) by (change (0 <= K1 * (`|v|)%R); apply Rmult_le_pos; [exact HK1|exact Hv]).
  exists K, K1, (K21 + K22); split; [exact HK|]; split; [exact HK1|]; split; [lra|].
  intros x; assert (Hx : 0 <= (`|x|)%R) by growth_norm_nonneg; split.
  - replace (K * (1 + (`|x|)%R) ^ 0) with K by ring.
    unfold quadratic_gradient; apply growth_gradient_entry_bound; assumption.
  - split.
    + unfold quadratic_gradient_first.
      rewrite (matrix_nested_hessian_action n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x u) Hb Hg HY HS).
      pose proof (growth_gradient_first_entry_bound n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x u) a b D
        Hb Hg HY HS Ha Hbb HD HL) as HF.
      change (Rabs (matrix_entry n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x u)) a b) <=
        B1 * (`|quadratic_first n lambda x u|)%R) in HF.
      eapply Rle_trans; [exact HF|].
      eapply Rle_trans with (B1 * (J * (`|x|)%R * (`|u|)%R)).
      * apply Rmult_le_compat_l; [exact HB1|apply quadratic_first_norm_bound].
      * replace (B1 * (J * (`|x|)%R * (`|u|)%R)) with (K1 * (`|x|)%R) by (unfold K1; ring).
        apply Rmult_le_compat_l; [exact HK1|].
        replace ((1 + (`|x|)%R) ^ 1) with (1 + (`|x|)%R) by ring; lra.
    + unfold quadratic_gradient_second.
      rewrite (matrix_nested_hessian_derivative_action n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x u)
        (quadratic_first n lambda x v) Hb Hg HY HS).
      rewrite (matrix_nested_hessian_action n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_second n lambda u v) Hb Hg HY HS).
      rewrite matrix_entry_add.
      pose proof (growth_gradient_second_entry_bound n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_first n lambda x u)
        (quadratic_first n lambda x v) a b D Hb Hg HY HS Ha Hbb HD HL) as HT.
      pose proof (growth_gradient_first_entry_bound n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_second n lambda u v)
        a b D Hb Hg HY HS Ha Hbb HD HL) as HF.
      change (Rabs (matrix_entry n (matrix_nested_gradient_second_derivative n beta gamma
        offset coeff Y S (quadratic_matrix n lambda C x) (quadratic_first n lambda x u)
        (quadratic_first n lambda x v)) a b) <=
        B2 * (`|quadratic_first n lambda x u|)%R * (`|quadratic_first n lambda x v|)%R) in HT.
      change (Rabs (matrix_entry n (matrix_nested_gradient_derivative n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C x) (quadratic_second n lambda u v)) a b) <=
        B1 * (`|quadratic_second n lambda u v|)%R) in HF.
      assert (HTB : B2 * (`|quadratic_first n lambda x u|)%R *
          (`|quadratic_first n lambda x v|)%R <= K21 * (`|x|)%R ^ 2).
      { replace (K21 * (`|x|)%R ^ 2) with
          (B2 * ((J * (`|x|)%R * (`|u|)%R) * (J * (`|x|)%R * (`|v|)%R))) by (unfold K21; ring).
        rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact HB2|].
        apply Rmult_le_compat; try growth_norm_nonneg; apply quadratic_first_norm_bound. }
      assert (HFB : B1 * (`|quadratic_second n lambda u v|)%R <= K22).
      { replace K22 with (B1 * (J * (`|u|)%R * (`|v|)%R)) by (unfold K22; ring).
        apply Rmult_le_compat_l; [exact HB1|apply quadratic_second_norm_bound]. }
      eapply Rle_trans; [apply Rabs_triang|].
      eapply Rle_trans with (K21 * (`|x|)%R ^ 2 + K22).
      * apply Rplus_le_compat;
          [eapply Rle_trans; [exact HT|exact HTB]|eapply Rle_trans; [exact HF|exact HFB]].
      * replace ((K21 + K22) * (1 + (`|x|)%R) ^ 2) with
          (K21 * (1 + (`|x|)%R) ^ 2 + K22 * (1 + (`|x|)%R) ^ 2) by ring.
        apply Rplus_le_compat.
        -- apply Rmult_le_compat_l; [exact HK21|nra].
        -- replace K22 with (K22 * 1) at 1 by ring.
           apply Rmult_le_compat_l; [exact HK22|nra].
Qed.

End QuadraticPolynomialGrowth.

Module QuadraticGrowthContinuity.
Import MatrixDefinitions MatrixCoordinates OperatorDefinitions GradientDefinitions
  HessianDefinitions ContinuityDefinitions CoefficientDefinitions CoefficientMaps
  FiniteGibbsContinuity MatrixHessian MatrixThirdContinuity QuadraticDefinitions
  QuadraticCalculus QuadraticGradient.

(* A bounded linear map, stated as in MatrixCoordinates, is continuous. *)
Lemma growth_linear_continuous {E V : normedModType R} (F : E -> V) x :
  (linear F /\ exists M : R, 0 < M /\ forall y : E, (`|F y|)%R <= M * (`|y|)%R) ->
  {for x, continuous F}.
Proof. intros H; exact (matrix_linear_continuous F H x). Qed.

Lemma growth_coordinate_sum_continuous {E : topologicalType} n (F : nat -> E -> R) x :
  (forall i, (i <= n)%coq_nat -> {for x, continuous (F i)}) ->
  {for x, continuous (fun z => coordinate_sum n (fun i => F i z))}.
Proof.
  revert F; induction n as [|n IH]; intros F HF; simpl.
  - apply HF; lia.
  - apply continuous_Rplus_fct; [apply HF; lia|apply IH; intros; apply HF; lia].
Qed.

Lemma growth_trace_pair_continuous {E : topologicalType} n (F G : E -> matrix n) x :
  {for x, continuous F} -> {for x, continuous G} ->
  {for x, continuous (fun z => trace_pair n (F z) (G z))}.
Proof.
  intros HF HG; unfold trace_pair; apply growth_coordinate_sum_continuous; intros i Hi.
  apply growth_coordinate_sum_continuous; intros j Hj; apply continuous_Rmult_fct.
  - apply (@continuous_comp E (matrix n) R F (fun M => matrix_entry n M i j) x); [exact HF|].
    exact (@growth_linear_continuous (matrix_NormedModule n) R^o
      (fun M => matrix_entry n M i j) (F x) (matrix_entry_linear n i j)).
  - apply (@continuous_comp E (matrix n) R G (fun M => matrix_entry n M j i) x); [exact HG|].
    exact (@growth_linear_continuous (matrix_NormedModule n) R^o
      (fun M => matrix_entry n M j i) (G x) (matrix_entry_linear n j i)).
Qed.

Lemma growth_hessian_action_continuous {E : topologicalType} n
    (F : E -> hessian_array n) (G : E -> matrix n) x :
  {for x, continuous F} -> {for x, continuous G} ->
  {for x, continuous (fun z => hessian_action n (F z) (G z))}.
Proof.
  intros HF HG; unfold hessian_action; apply matrix_build_continuous; intros i j Hi Hj.
  apply growth_trace_pair_continuous; [|exact HG].
  apply (@continuous_comp E (hessian_array n) (matrix n) F
    (fun H => hessian_entry n H i j) x); [exact HF|].
  exact (@growth_linear_continuous (hessian_NormedModule n) (matrix_NormedModule n)
    (fun H => hessian_entry n H i j) (F x) (hessian_entry_linear n i j)).
Qed.

Lemma growth_module_sum_continuous {E : topologicalType} (V : normedModType R)
    n (F : nat -> E -> V) x :
  (forall i, (i <= n)%coq_nat -> {for x, continuous (F i)}) ->
  {for x, continuous (fun z => module_coordinate_sum V n (fun i => F i z))}.
Proof.
  revert F; induction n as [|n IH]; intros F HF; simpl.
  - apply HF; lia.
  - have H0 : {for x, continuous (F O)} by apply HF; lia.
    have H1 : {for x, continuous (fun z => module_coordinate_sum V n (fun i => F (S i) z))}.
    { apply IH; intros; apply HF; lia. }
    exact (@continuousD R V E (F O)
      (fun z => module_coordinate_sum V n (fun i => F (S i) z)) x H0 H1).
Qed.

Lemma growth_third_action_continuous {E : topologicalType} n
    (F : E -> third_array n) (G : E -> matrix n) x :
  {for x, continuous F} -> {for x, continuous G} ->
  {for x, continuous (fun z => third_action n (F z) (G z))}.
Proof.
  intros HF HG; unfold third_action, coefficient_contract.
  apply growth_module_sum_continuous; intros i Hi.
  apply growth_module_sum_continuous; intros j Hj.
  have HS : {for x, continuous (fun z => matrix_entry n (G z) j i)}.
  { apply (@continuous_comp E (matrix n) R G (fun M => matrix_entry n M j i) x); [exact HG|].
    exact (@growth_linear_continuous (matrix_NormedModule n) R^o
      (fun M => matrix_entry n M j i) (G x) (matrix_entry_linear n j i)). }
  have HT : {for x, continuous (fun z => third_entry n (F z) i j)}.
  { apply (@continuous_comp E (third_array n) (hessian_array n) F
      (fun T => third_entry n T i j) x); [exact HF|].
    exact (@growth_linear_continuous (third_NormedModule n) (hessian_NormedModule n)
      (fun T => third_entry n T i j) (F x) (third_entry_linear n i j)). }
  exact (@continuousZ R (hessian_NormedModule n) E
    (fun z => matrix_entry n (G z) j i) (fun z => third_entry n (F z) i j) x HS HT).
Qed.

Theorem quadratic_gradient_continuous n beta gamma offset coeff Y S lambda C (x : vector n) :
  0 < beta -> 0 < gamma -> Y <> nil -> S <> nil ->
  {for x, continuous (quadratic_gradient n beta gamma offset coeff Y S lambda C)}.
Proof.
  intros Hb Hg HY HS.
  have [HD _] := quadratic_gradient_frechet n beta gamma offset coeff Y S lambda C x Hb Hg HY HS.
  exact (differentiable_continuous HD).
Qed.

Theorem quadratic_gradient_first_continuous n beta gamma offset coeff Y S lambda C (x u : vector n) :
  0 < beta -> 0 < gamma -> Y <> nil -> S <> nil ->
  {for x, continuous (fun z => quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u)}.
Proof.
  intros Hb Hg HY HS.
  have [HD _] := quadratic_gradient_first_frechet n beta gamma offset coeff Y S lambda C x u
    Hb Hg HY HS.
  exact (differentiable_continuous HD).
Qed.

Theorem quadratic_gradient_second_continuous n beta gamma offset coeff Y S lambda C
    (x u v : vector n) :
  0 < beta -> 0 < gamma -> Y <> nil -> S <> nil ->
  {for x, continuous
    (fun z => quadratic_gradient_second n beta gamma offset coeff Y S lambda C z u v)}.
Proof.
  intros Hb Hg HY HS.
  assert (HQ : {for x, continuous (quadratic_matrix n lambda C)}).
  { have [HD _] := quadratic_matrix_frechet n lambda C x.
    exact (differentiable_continuous HD). }
  assert (HFirst : forall w, {for x, continuous (fun z => quadratic_first n lambda z w)}).
  { intros w; have [HD _] := quadratic_first_frechet n lambda x w.
    exact (differentiable_continuous HD). }
  assert (HH : {for x, continuous (fun z =>
    matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C z))}).
  { apply (@continuous_comp (vector n) (matrix n) (hessian_array n)
      (quadratic_matrix n lambda C) (matrix_nested_hessian n beta gamma offset coeff Y S) x);
      [exact HQ|].
    have [HD _] := matrix_nested_hessian_frechet n beta gamma offset coeff Y S Hb Hg HY HS
      (quadratic_matrix n lambda C x).
    exact (differentiable_continuous HD). }
  assert (HT : {for x, continuous (fun z =>
    matrix_nested_third_coefficients n beta gamma offset coeff Y S (quadratic_matrix n lambda C z))}).
  { apply (@continuous_comp (vector n) (matrix n) (third_array n)
      (quadratic_matrix n lambda C)
      (matrix_nested_third_coefficients n beta gamma offset coeff Y S) x); [exact HQ|].
    apply matrix_third_coefficients_continuous; assumption. }
  (* The map is rewritten with actual_third_action. *)
  have E : (fun z => quadratic_gradient_second n beta gamma offset coeff Y S lambda C z u v) =
    (fun z => matrix_add n
      (hessian_action n
        (third_action n (matrix_nested_third_coefficients n beta gamma offset coeff Y S
          (quadratic_matrix n lambda C z)) (quadratic_first n lambda z v))
        (quadratic_first n lambda z u))
      (hessian_action n (matrix_nested_hessian n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C z)) (quadratic_second n lambda u v))).
  { apply: funext => z; unfold quadratic_gradient_second.
    rewrite (actual_third_action n beta gamma offset coeff Y S
      (quadratic_matrix n lambda C z) (quadratic_first n lambda z v) Hb Hg HY HS).
    reflexivity. }
  rewrite E.
  have H1 : {for x, continuous (fun z => hessian_action n
      (third_action n (matrix_nested_third_coefficients n beta gamma offset coeff Y S
        (quadratic_matrix n lambda C z)) (quadratic_first n lambda z v))
      (quadratic_first n lambda z u))}.
  { apply: growth_hessian_action_continuous; [|apply HFirst].
    apply: growth_third_action_continuous; [exact HT|apply HFirst]. }
  have H2 : {for x, continuous (fun z => hessian_action n
      (matrix_nested_hessian n beta gamma offset coeff Y S (quadratic_matrix n lambda C z))
      (quadratic_second n lambda u v))}.
  { apply: growth_hessian_action_continuous; [exact HH|apply: cst_continuous]. }
  exact (@continuousD R (matrix_NormedModule n) (vector n) _ _ x H1 H2).
Qed.

Theorem quadratic_gradient_entries_continuous n beta gamma offset coeff Y S lambda C
    (u v : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> nil -> S <> nil -> forall x : vector n,
  {for x, continuous (fun z =>
    matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C z) a b)} /\
  {for x, continuous (fun z =>
    matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u) a b)} /\
  {for x, continuous (fun z =>
    matrix_entry n (quadratic_gradient_second n beta gamma offset coeff Y S lambda C z u v) a b)}.
Proof.
  intros Hb Hg HY HS x; split.
  - apply (@continuous_comp (vector n) (matrix n) R
      (quadratic_gradient n beta gamma offset coeff Y S lambda C)
      (fun M => matrix_entry n M a b) x).
    + apply quadratic_gradient_continuous; assumption.
    + exact (@growth_linear_continuous (matrix_NormedModule n) R^o
        (fun M => matrix_entry n M a b) _ (matrix_entry_linear n a b)).
  - split.
    + apply (@continuous_comp (vector n) (matrix n) R
        (fun z => quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u)
        (fun M => matrix_entry n M a b) x).
      * apply quadratic_gradient_first_continuous; assumption.
      * exact (@growth_linear_continuous (matrix_NormedModule n) R^o
          (fun M => matrix_entry n M a b) _ (matrix_entry_linear n a b)).
    + apply (@continuous_comp (vector n) (matrix n) R
        (fun z => quadratic_gradient_second n beta gamma offset coeff Y S lambda C z u v)
        (fun M => matrix_entry n M a b) x).
      * apply quadratic_gradient_second_continuous; assumption.
      * exact (@growth_linear_continuous (matrix_NormedModule n) R^o
          (fun M => matrix_entry n M a b) _ (matrix_entry_linear n a b)).
Qed.

End QuadraticGrowthContinuity.

Module QuadraticGrowth.
Import MatrixDefinitions MatrixCoordinates OperatorDefinitions QuadraticDefinitions
  QuadraticGradient QuadraticGrowthContinuity QuadraticPolynomialGrowth.

Theorem quadratic_growth_entry_frechet n beta gamma offset coeff Y S lambda C
    (x : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff x
    ((fun z => matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C z) a b)
      : vector n -> R^o)
    (fun u => matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b).
Proof.
  intros Hb Hg HY HS.
  exact (is_diff_comp
    (quadratic_gradient_frechet n beta gamma offset coeff Y S lambda C x Hb Hg HY HS)
    (matrix_entry_frechet n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)).
Qed.

Theorem quadratic_growth_first_entry_frechet n beta gamma offset coeff Y S lambda C
    (x u : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  is_diff x
    ((fun z => matrix_entry n
      (quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u) a b)
      : vector n -> R^o)
    (fun v => matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u v) a b).
Proof.
  intros Hb Hg HY HS.
  exact (is_diff_comp
    (quadratic_gradient_first_frechet n beta gamma offset coeff Y S lambda C x u Hb Hg HY HS)
    (matrix_entry_frechet n
      (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b)).
Qed.

Theorem quadratic_gradient_entry_polynomial_regular n beta gamma offset coeff Y S lambda C
    (u v : vector n) a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  exists K0 K1 K2 : R, 0 <= K0 /\ 0 <= K1 /\ 0 <= K2 /\ forall x : vector n,
    is_diff x
      ((fun z => matrix_entry n
        (quadratic_gradient n beta gamma offset coeff Y S lambda C z) a b) : vector n -> R^o)
      (fun w => matrix_entry n
        (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x w) a b) /\
    is_diff x
      ((fun z => matrix_entry n
        (quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u) a b)
        : vector n -> R^o)
      (fun w => matrix_entry n
        (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u w) a b) /\
    {for x, continuous (fun z => matrix_entry n
      (quadratic_gradient n beta gamma offset coeff Y S lambda C z) a b)} /\
    {for x, continuous (fun z => matrix_entry n
      (quadratic_gradient_first n beta gamma offset coeff Y S lambda C z u) a b)} /\
    {for x, continuous (fun z => matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C z u v) a b)} /\
    Rabs (matrix_entry n (quadratic_gradient n beta gamma offset coeff Y S lambda C x) a b)
      <= K0 * (1 + (`|x|)%R) ^ 0 /\
    Rabs (matrix_entry n (quadratic_gradient_first n beta gamma offset coeff Y S lambda C x u) a b)
      <= K1 * (1 + (`|x|)%R) ^ 1 /\
    Rabs (matrix_entry n
      (quadratic_gradient_second n beta gamma offset coeff Y S lambda C x u v) a b)
      <= K2 * (1 + (`|x|)%R) ^ 2.
Proof.
  intros Hb Hg HY HS Ha Hbb.
  destruct (quadratic_gradient_entries_polynomial_growth n beta gamma offset coeff Y S lambda C
    u v a b Hb Hg HY HS Ha Hbb) as [K0 [K1 [K2 [H0 [H1 [H2 HG]]]]]].
  exists K0, K1, K2; split; [exact H0|]; split; [exact H1|]; split; [exact H2|].
  intros x; split; [apply quadratic_growth_entry_frechet; assumption|].
  split; [apply quadratic_growth_first_entry_frechet; assumption|].
  destruct (quadratic_gradient_entries_continuous n beta gamma offset coeff Y S lambda C u v a b
    Hb Hg HY HS x) as [HC0 [HC1 HC2]].
  split; [exact HC0|]; split; [exact HC1|]; split; [exact HC2|exact (HG x)].
Qed.

End QuadraticGrowth.
