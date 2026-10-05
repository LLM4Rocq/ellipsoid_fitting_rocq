(* The logarithmic head and tail decomposition (lem:regularity of the paper),
   stated with the finite_sum and euclidean_norm of the soft margins.
   The cardinality bound itself is head_tail_decomposition_explicit of
   HeadTail, with the explicit constant
   head_tail_constant theta = 16 / (theta^2 ln 2). This module adds:
   - the bridge vector_norm = euclidean_norm and squared_energy = squared_norm;
   - the normalized tail vector on all indices (paper_main_tail_list_vector),
     with unit norm on seq 0 n and |entry| <= theta / sqrt d everywhere when
     the tail is positive;
   - the head and tail mass split (paper_main_head_tail_mass_split).
   paper_main_head_tail_regularity: for theta > 0, d >= 1 and a unit y on
   seq 0 n there is a duplicate-free head J inside seq 0 n with
   length J <= (16 / (theta^2 ln 2)) d ln d. Either the tail norm is at most
   d^-2, or it is positive and the normalized tail is capped by
   theta / sqrt d. *)
From Stdlib Require Import Reals List Lia Lra Psatz Permutation PeanoNat.
From EllipsoidFitting Require Import Definitions Peeling FiniteSets HeadTail SoftDefinitions
  GaussianCovarianceSums.
Import ListNotations.
Open Scope R_scope.

(* 1. The two definitions of the norm agree. *)
Lemma pmhtl_energy_finite_sum (w : nat -> R) (A : list nat) :
  energy w A = finite_sum w A.
Proof. induction A as [|i A IH]; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma pmhtl_squared (y : nat -> R) (A : list nat) :
  squared_energy y A = squared_norm y A.
Proof. unfold squared_energy, squared_norm; apply pmhtl_energy_finite_sum. Qed.

Lemma pmhtl_vector_norm (y : nat -> R) (A : list nat) :
  vector_norm y A = euclidean_norm y A.
Proof. unfold vector_norm, euclidean_norm; now rewrite pmhtl_squared. Qed.

Lemma pmhtl_unit (y : nat -> R) (A : list nat) :
  euclidean_norm y A = 1 -> squared_norm y A = 1.
Proof.
  unfold euclidean_norm; intro H.
  assert (H0 : 0 <= squared_norm y A).
  { rewrite <- pmhtl_squared; apply squared_energy_nonneg. }
  rewrite <- (sqrt_def _ H0), H; ring.
Qed.

(* 2. Splitting seq 0 n into the head J and the tail. *)
Definition pmhtl_out (J : list nat) (i : nat) : bool :=
  if in_dec Nat.eq_dec i J then false else true.

Lemma pmhtl_tail_filter (n : nat) (J : list nat) :
  tail_indices n J = filter (pmhtl_out J) (seq 0 n).
Proof. reflexivity. Qed.

Lemma pmhtl_split (w : nat -> R) (n : nat) (J : list nat) :
  finite_sum w (seq 0 n) =
  finite_sum w (tail_indices n J) +
  finite_sum w (filter (fun i => negb (pmhtl_out J i)) (seq 0 n)).
Proof.
  rewrite <- !pmhtl_energy_finite_sum, pmhtl_tail_filter.
  apply energy_filter_split.
Qed.

Lemma pmhtl_head_permutation (n : nat) (J : list nat) :
  NoDup J -> incl J (seq 0 n) ->
  Permutation (filter (fun i => negb (pmhtl_out J i)) (seq 0 n)) J.
Proof.
  intros HJ Hincl.
  apply NoDup_Permutation; [apply NoDup_filter, seq_NoDup | exact HJ |].
  intro i; rewrite filter_In; unfold pmhtl_out.
  destruct (in_dec Nat.eq_dec i J) as [Hi|Hi]; simpl; split.
  - intros _; exact Hi.
  - intros _; split; [exact (Hincl i Hi) | reflexivity].
  - intros [_ H]; discriminate.
  - intro H; contradiction.
Qed.

Theorem paper_main_head_tail_mass_split (y : nat -> R) (n : nat) (J : list nat) :
  NoDup J -> incl J (seq 0 n) ->
  squared_norm y J + squared_norm y (tail_indices n J) = squared_norm y (seq 0 n).
Proof.
  intros HJ Hincl; unfold squared_norm.
  rewrite (pmhtl_split (fun i => y i ^ 2) n J).
  rewrite <- (pmhtl_energy_finite_sum _ (filter _ _)).
  rewrite (energy_permutation _ _ _ (pmhtl_head_permutation n J HJ Hincl)).
  rewrite (pmhtl_energy_finite_sum (fun i => y i ^ 2) J); ring.
Qed.

(* 3. The normalized tail vector. *)
Definition paper_main_tail_list_vector (y : nat -> R) (n : nat) (J : list nat) (i : nat) : R :=
  if in_dec Nat.eq_dec i (tail_indices n J)
  then y i / euclidean_norm y (tail_indices n J) else 0.

Lemma pmhtl_head_zero (y : nat -> R) (n : nat) (J : list nat) :
  finite_sum (fun i => paper_main_tail_list_vector y n J i ^ 2)
    (filter (fun i => negb (pmhtl_out J i)) (seq 0 n)) = 0.
Proof.
  rewrite <- (finite_sum_zero (filter (fun i => negb (pmhtl_out J i)) (seq 0 n))).
  apply finite_sum_ext; intros i Hi.
  apply filter_In in Hi as [_ Hi]; unfold pmhtl_out in Hi.
  destruct (in_dec Nat.eq_dec i J) as [HiJ|HiJ]; [|discriminate].
  unfold paper_main_tail_list_vector.
  destruct (in_dec Nat.eq_dec i (tail_indices n J)) as [HT|HT]; [|ring].
  apply outside_in in HT as [_ HT]; contradiction.
Qed.

Theorem paper_main_tail_list_vector_unit (y : nat -> R) (n : nat) (J : list nat) :
  0 < euclidean_norm y (tail_indices n J) ->
  euclidean_norm (paper_main_tail_list_vector y n J) (seq 0 n) = 1.
Proof.
  intro Hr; set (r := euclidean_norm y (tail_indices n J)) in *.
  unfold euclidean_norm at 1, squared_norm.
  rewrite (pmhtl_split _ n J), pmhtl_head_zero, Rplus_0_r.
  assert (E : finite_sum (fun i => paper_main_tail_list_vector y n J i ^ 2) (tail_indices n J) =
    finite_sum (fun i => y i ^ 2) (tail_indices n J) * / r ^ 2).
  { rewrite <- finite_sum_scale_r; apply finite_sum_ext; intros i Hi.
    unfold paper_main_tail_list_vector.
    destruct (in_dec Nat.eq_dec i (tail_indices n J)) as [_|HT]; [|contradiction].
    fold r; unfold Rdiv; rewrite Rpow_mult_distr, pow_inv; reflexivity. }
  rewrite E.
  assert (Hs : finite_sum (fun i => y i ^ 2) (tail_indices n J) = r ^ 2).
  { unfold r, euclidean_norm, squared_norm; rewrite pow2_sqrt; [reflexivity|].
    apply finite_sum_nonneg; intros i _; apply pow2_ge_0. }
  rewrite Hs, Rinv_r, sqrt_1; [reflexivity|].
  apply pow_nonzero; lra.
Qed.

Theorem paper_main_tail_list_vector_cap (y : nat -> R) (n : nat) (J : list nat) (c : R) :
  0 <= c ->
  (forall i, In i (tail_indices n J) ->
    Rabs (y i / euclidean_norm y (tail_indices n J)) <= c) ->
  forall i, Rabs (paper_main_tail_list_vector y n J i) <= c.
Proof.
  intros Hc Hcap i; unfold paper_main_tail_list_vector.
  destruct (in_dec Nat.eq_dec i (tail_indices n J)) as [HT|HT].
  - exact (Hcap i HT).
  - rewrite Rabs_R0; exact Hc.
Qed.

(* 4. The decomposition, from head_tail_decomposition_explicit. *)
Theorem paper_main_head_tail_regularity (theta : R) (d n : nat) (y : nat -> R) :
  0 < theta -> (1 <= d)%nat -> euclidean_norm y (seq 0 n) = 1 ->
  exists J : list nat,
    NoDup J /\ incl J (seq 0 n) /\
    INR (length J) <= head_tail_constant theta * INR d * ln (INR d) /\
    squared_norm y J + squared_norm y (tail_indices n J) = 1 /\
    (euclidean_norm y (tail_indices n J) <= 1 / INR d ^ 2 \/
     (0 < euclidean_norm y (tail_indices n J) /\
      euclidean_norm (paper_main_tail_list_vector y n J) (seq 0 n) = 1 /\
      forall i, Rabs (paper_main_tail_list_vector y n J i) <= theta / sqrt (INR d))).
Proof.
  intros Htheta Hd Hy.
  assert (Hy2 : squared_energy y (seq 0 n) = 1).
  { rewrite pmhtl_squared; exact (pmhtl_unit y _ Hy). }
  destruct (head_tail_decomposition_explicit theta d n y Htheta Hd Hy2)
    as [J [HJ [Hincl [Hlen Hcase]]]].
  exists J; split; [exact HJ|]; split; [exact Hincl|]; split; [exact Hlen|].
  split.
  { rewrite paper_main_head_tail_mass_split by assumption; exact (pmhtl_unit y _ Hy). }
  rewrite !pmhtl_vector_norm in Hcase.
  destruct Hcase as [Hsmall | [Hpos Hcap]]; [left; exact Hsmall | right].
  split; [exact Hpos|]; split; [exact (paper_main_tail_list_vector_unit y n J Hpos)|].
  apply paper_main_tail_list_vector_cap; [|exact Hcap].
  assert (Hsd : 0 < sqrt (INR d)) by (apply sqrt_lt_R0, lt_0_INR; lia).
  apply Rlt_le, Rdiv_lt_0_compat; assumption.
Qed.
