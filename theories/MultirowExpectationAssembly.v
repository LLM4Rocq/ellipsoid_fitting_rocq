(* The four clauses of the challenge multirow_expectation_derivative, one
   lemma each, with the notation and imports of its Challenge.v first, so
   that the results module can conclude with exact.

   D = S m (S n + S (goe_vector_index n)) coordinates, f t is the iterated
   Gaussian expectation of Phi(Z(t)) = gaussian_array_value ... t.

   - mexp_clause_domain (clause 1): for t in [0,1], Phi(Z(t)) is continuous
     and bounded by a polynomial weight (MultirowExpectationBounds), so it
     has a Gaussian domain (gaussian_list_domain_polynomial).
   - mexp_clause_derivative (clause 2): finite_gaussian_parameter_differentiation
     with F t = Phi(Z(t)), D t = the sum of the row velocities (derivative in
     t from MultirowTimeCalculusResults) and D2 t = the sum of the row
     accelerations (derivative from MultirowExpectationCalculus, with the
     mixed-row terms through Z(t)), on the interval |t - a| <= rho,
     rho = min(a, 1-a)/2, where all bounds are uniform. The domains of the
     remainders and the Stein identity come from MultirowFullSteinResults.
   - mexp_value_expectation_continuous (clause 3):
     gaussian_iterated_expectation_continuous_modulus_within with the
     modulus L (|sqrt t - sqrt a| + |sqrt (1-t) - sqrt (1-a)|).
   - mexp_clause_endpoints (clause 4): Z(0) keeps only the GOE blocks and
     Z(1) only the quadratic blocks. So Phi(Z(0)) is the GOE value of the
     row suffixes and Phi(Z(1)) the quadratic value of the row prefixes,
     whose expectations are those over the fewer coordinates
     (mexp_row_suffixes_gaussian_expectation,
     row_prefixes_gaussian_expectation). Continuity and bounds of the
     endpoint functions come from those of Phi(Z(0)) and Phi(Z(1)) through
     the zero-padding lifts. The limits are clause 3 at 0 and at 1.

   The hypotheses used are 0 < beta, 0 < gamma, Y <> [], S <> [], the
   symmetry of the B s (for the Stein identity only) and the range of the
   time. No Axiom, Parameter or Admitted. *)

From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum classical_sets.
From mathcomp Require Import Rstruct topology normedtype derive Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions SoftDefinitions OperatorDefinitions
  GaussianProductDefinitions GaussianVectorDefinitions GoeDefinitions
  TensorDefinitions JointDefinitions
  RowTimeDefinitions RowObservableDefinitions MultirowEndpointDefinitions.
From Stdlib Require Import Lia Lra.
From EllipsoidFitting Require Import RowArrayDefinitions RowCoordinateDefinitions RowMarginalDefinitions
  LowerDefinitions GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  VectorCoordinateDefinitions
  MultirowExpectationCalculus MultirowExpectationMarginal MultirowExpectationBounds.
From EllipsoidFitting Require JointEndpointContinuity GaussianExpectationContinuity
  FiniteGaussianParameter GaussianBlockExchange GaussianRowMarginal GaussianFiniteSums
  RowObservableContinuity MultirowFullSteinBounds MultirowFullSteinResults
  MultirowTimeCalculusResults GaussianCoordinateTopology GaussianProduct RowCoordinates
  RowPrefixes.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Endpoint values. *)

Lemma mexp_skipn_zeros (k : nat) (l : list R) : skipn k (repeat 0 k ++ l) = l.
Proof. elim: k => [|k IH] //=. Qed.

Lemma mexp_firstn_zeros (k j : nat) (l : list R) :
  length l = k -> firstn k (l ++ repeat 0 j) = l.
Proof. move=> <-; exact: mexp_firstn_app_length. Qed.

Theorem mexp_value_zero_suffixes n m beta gamma y B Y S xs :
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  gaussian_array_value n m beta gamma y B Y S 0 xs =
  multirow_goe_value n m beta gamma y B Y S
    (mexp_row_suffixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs).
Proof.
  move=> HL; rewrite /gaussian_array_value /multirow_goe_value; f_equal.
  rewrite /gaussian_row_array /multirow_goe_array.
  apply: mexp_tuple_build_ext => i Hi.
  rewrite /gaussian_row_matrix JointEndpointContinuity.joint_matrix_at_zero.
  rewrite /matrix_add /matrix_zero add0r.
  have Hi' : (i < Datatypes.S m)%coq_nat by lia.
  rewrite (mexp_row_suffixes_row_chunk (Datatypes.S m) _ _ i xs HL Hi').
  reflexivity.
Qed.

Theorem mexp_value_one_prefixes n m beta gamma y B Y S xs :
  length xs = (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat ->
  gaussian_array_value n m beta gamma y B Y S 1 xs =
  multirow_quadratic_value n m beta gamma y B Y S
    (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs).
Proof.
  move=> HL; rewrite /gaussian_array_value /multirow_quadratic_value; f_equal.
  rewrite /gaussian_row_array /multirow_quadratic_array.
  apply: mexp_tuple_build_ext => i Hi.
  rewrite /gaussian_row_matrix JointEndpointContinuity.joint_matrix_at_one.
  rewrite /matrix_add /matrix_zero add0r.
  have Hi' : (i < Datatypes.S m)%coq_nat by lia.
  rewrite (RowPrefixes.row_prefixes_row_chunk (Datatypes.S m) _ _ i xs HL Hi').
  reflexivity.
Qed.

Theorem mexp_value_zero_lift n m beta gamma y B Y S zs :
  length zs = (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat ->
  gaussian_array_value n m beta gamma y B Y S 0
    (mexp_goe_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) zs) =
  multirow_goe_value n m beta gamma y B Y S zs.
Proof.
  move=> HL; rewrite /gaussian_array_value /multirow_goe_value; f_equal.
  rewrite /gaussian_row_array /multirow_goe_array.
  apply: mexp_tuple_build_ext => i Hi.
  rewrite /gaussian_row_matrix JointEndpointContinuity.joint_matrix_at_zero.
  rewrite /matrix_add /matrix_zero add0r.
  have Hi' : (i < Datatypes.S m)%coq_nat by lia.
  set L := mexp_goe_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) zs.
  change (snd (gaussian_row_pair n i L)) with
    (vector_of_list (goe_vector_index n)
      (skipn (Datatypes.S n)
        (row_chunk (Datatypes.S n + Datatypes.S (goe_vector_index n)) i L))).
  rewrite /L (mexp_goe_lift_row_chunk (Datatypes.S m) _ _ i zs HL Hi') mexp_skipn_zeros.
  reflexivity.
Qed.

Theorem mexp_value_one_lift n m beta gamma y B Y S xs :
  length xs = (Datatypes.S m * Datatypes.S n)%coq_nat ->
  gaussian_array_value n m beta gamma y B Y S 1
    (mexp_quadratic_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs) =
  multirow_quadratic_value n m beta gamma y B Y S xs.
Proof.
  move=> HL; rewrite /gaussian_array_value /multirow_quadratic_value; f_equal.
  rewrite /gaussian_row_array /multirow_quadratic_array.
  apply: mexp_tuple_build_ext => i Hi.
  rewrite /gaussian_row_matrix JointEndpointContinuity.joint_matrix_at_one.
  rewrite /matrix_add /matrix_zero add0r.
  have Hi' : (i < Datatypes.S m)%coq_nat by lia.
  set L := mexp_quadratic_lift (Datatypes.S m) (Datatypes.S n)
    (Datatypes.S (goe_vector_index n)) xs.
  change (fst (gaussian_row_pair n i L)) with
    (vector_of_list n
      (firstn (Datatypes.S n)
        (row_chunk (Datatypes.S n + Datatypes.S (goe_vector_index n)) i L))).
  rewrite /L (mexp_quadratic_lift_row_chunk (Datatypes.S m) _ _ i xs HL Hi').
  rewrite (mexp_firstn_zeros (Datatypes.S n) _ _
    (RowCoordinates.row_chunk_length (Datatypes.S m) (Datatypes.S n) i xs HL Hi')).
  reflexivity.
Qed.

Lemma mexp_bound_ext d C p (F G : list R -> R) :
  (forall xs, length xs = d -> F xs = G xs) ->
  finite_polynomial_bound d C p F -> finite_polynomial_bound d C p G.
Proof. move=> E [HC HF]; split => // xs HL; rewrite -E //; exact: HF. Qed.

(* Clause 1. *)

Theorem mexp_clause_domain n m beta gamma y B Y S t :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= t <= 1 ->
  gaussian_list_domain
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_array_value n m beta gamma y B Y S t).
Proof.
  move=> Hb Hg HY HS Ht.
  destruct (mexp_value_polynomial n m beta gamma y B Y S Hb Hg HY HS) as [C [HC HP]].
  exact: (GaussianBlockExchange.gaussian_list_domain_polynomial _ _ C 2
    (mexp_value_continuous n m beta gamma y B Y S t Hb Hg HY HS) (HP t Ht)).
Qed.

(* Clause 3. *)

Theorem mexp_value_expectation_continuous n m beta gamma y B Y S a :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] -> 0 <= a <= 1 ->
  ((fun t => gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S t))
    @ within (fun t : R => 0 <= t <= 1) (nbhs a) -->
    gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S a))%classic.
Proof.
  move=> Hb Hg HY HS Ha.
  destruct (mexp_value_polynomial n m beta gamma y B Y S Hb Hg HY HS) as [C [HC HP]].
  destruct (mexp_value_difference n m beta gamma y B Y S Hb Hg HY HS) as [L [HL HD]].
  refine (proj1 (GaussianExpectationContinuity.gaussian_iterated_expectation_continuous_modulus_within
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (fun t => gaussian_array_value n m beta gamma y B Y S t) (fun t => 0 <= t <= 1) a C 2 2
    (fun t => L * (Rabs (sqrt t - sqrt a) + Rabs (sqrt (1-t) - sqrt (1-a))))
    Ha (HP a Ha) _ _ _ _)).
  - exists 1; split; [lra|]; move=> b _ _; exact: mexp_value_continuous.
  - exact: JointEndpointContinuity.joint_endpoint_modulus_continuous.
  - cbv beta.
    replace (sqrt a - sqrt a) with 0 by ring.
    replace (sqrt (1-a) - sqrt (1-a)) with 0 by ring.
    rewrite Rabs_R0 Rplus_0_r Rmult_0_r; reflexivity.
  - exists 1; split; [lra|]; move=> b Hb' _; split.
    + apply Rmult_le_pos; [exact HL|].
      apply Rplus_le_le_0_compat; apply Rabs_pos.
    + move=> xs Hxs; exact: (HD a b xs (proj1 Ha) (proj1 Hb') Hxs).
Qed.

(* Clause 2. *)

Theorem mexp_clause_derivative n m beta gamma y B Y S a :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall s, In s S -> symmetric_matrix n (B s)) -> 0 < a < 1 ->
  gaussian_list_domain
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (fun xs => finite_sum
      (fun i => gaussian_row_velocity n m beta gamma y B Y S a i xs)
      (List.seq 0 (Datatypes.S m))) /\
  (forall i, (i < Datatypes.S m)%coq_nat ->
    gaussian_list_domain
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_row_remainder n m beta gamma y B Y S a i)) /\
  @is_derive R R^o R^o a 1
    (fun t => gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S t))
    (gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (fun xs => finite_sum
        (fun i => gaussian_row_velocity n m beta gamma y B Y S a i xs)
        (List.seq 0 (Datatypes.S m)))) /\
  gaussian_iterated_expectation
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (fun xs => finite_sum
      (fun i => gaussian_row_velocity n m beta gamma y B Y S a i xs)
      (List.seq 0 (Datatypes.S m))) =
    (sqrt a / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) *
      finite_sum (fun i => gaussian_iterated_expectation
        (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
        (gaussian_row_remainder n m beta gamma y B Y S a i))
      (List.seq 0 (Datatypes.S m)) /\
  @is_derive R R^o R^o a 1
    (fun t => gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S t))
    ((sqrt a / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) *
      finite_sum (fun i => gaussian_iterated_expectation
        (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
        (gaussian_row_remainder n m beta gamma y B Y S a i))
      (List.seq 0 (Datatypes.S m))).
Proof.
  move=> Hb Hg HY HS Hsym Ha.
  set d := (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat.
  set I := List.seq 0 (Datatypes.S m).
  set rho := Rmin a (1-a) / 2.
  have Hmin : 0 < Rmin a (1-a) by apply Rmin_glb_lt; lra.
  have Hra := Rmin_l a (1-a).
  have Hrb := Rmin_r a (1-a).
  have Hrho : 0 < rho by rewrite /rho; lra.
  have Hnear : forall t, Rabs (t-a) <= rho -> rho <= t <= 1 - rho.
  { move=> t Ht.
    have H1 := Rle_trans _ _ _ (RRle_abs (t-a)) Ht.
    have H2 : a - t <= rho.
    { rewrite Rabs_minus_sym in Ht; exact: Rle_trans _ _ _ (RRle_abs (a-t)) Ht. }
    rewrite /rho in H1 H2 *; lra. }
  have Hopen : forall t, Rabs (t-a) <= rho -> 0 < t < 1.
  { move=> t Ht; have := Hnear t Ht; lra. }
  have Hclosed : forall t, Rabs (t-a) <= rho -> 0 <= t <= 1.
  { move=> t Ht; have := Hnear t Ht; lra. }
  have HinI : forall i, In i I -> (i <= m)%coq_nat.
  { move=> i Hi; apply in_seq in Hi; lia. }
  set F := fun u xs => gaussian_array_value n m beta gamma y B Y S u xs.
  set Dv := fun u xs => finite_sum (fun i => gaussian_row_velocity n m beta gamma y B Y S u i xs) I.
  set D2 := fun u xs => finite_sum (fun i => mexp_row_acceleration n m beta gamma y B Y S u i xs) I.
  have HD : forall t xs, Rabs (t-a) <= rho -> length xs = d ->
      @is_derive R R^o R^o t 1 (fun u => F u xs) (Dv t xs).
  { move=> t xs Ht _.
    exact: (proj2 (proj2 (proj2 (MultirowTimeCalculusResults.paper_multirow_time_calculus_results
      n m beta gamma y B Y S t xs Hb Hg (Hopen t Ht))))). }
  have HD2 : forall t xs, Rabs (t-a) <= rho -> length xs = d ->
      @is_derive R R^o R^o t 1 (fun u => Dv u xs) (D2 t xs).
  { move=> t xs Ht _.
    exact: (mexp_velocity_sum_derivative n m beta gamma y B Y S t xs I Hb Hg HY HS (Hopen t Ht)). }
  destruct (mexp_acceleration_sum_bound n m beta gamma y B Y S rho Hb Hg HY HS Hrho) as [C2 HC2].
  have Hpoly2 : forall t, Rabs (t-a) <= rho -> finite_polynomial_bound d C2 4 (D2 t).
  { move=> t Ht; exact: (HC2 t (Hnear t Ht)). }
  have HCF : forall t, Rabs (t-a) <= rho -> finite_joint_continuous d (F t).
  { move=> t _; exact: mexp_value_continuous. }
  have HCD : finite_joint_continuous d (Dv a).
  { apply: (GaussianFiniteSums.finite_joint_continuous_sum d I
      (fun i xs => gaussian_row_velocity n m beta gamma y B Y S a i xs)).
    move=> i Hi.
    exact: (RowObservableContinuity.gaussian_row_velocity_continuous n m beta gamma y B Y S a i
      Hg HY HS (HinI i Hi)). }
  destruct (mexp_value_polynomial n m beta gamma y B Y S Hb Hg HY HS) as [C0 [HC0 HP0]].
  have HpolyF : forall t, Rabs (t-a) <= rho -> finite_polynomial_bound d C0 2 (F t).
  { move=> t Ht; exact: (HP0 t (Hclosed t Ht)). }
  have HBsum : forall i, In i I -> exists C,
      finite_polynomial_bound d C 2 (fun xs => gaussian_row_velocity n m beta gamma y B Y S a i xs).
  { move=> i Hi.
    destruct (MultirowFullSteinBounds.multirow_row_observables_polynomial_bounds
      n m beta gamma y B Y S a i Hb Hg HY HS (HinI i Hi)) as [CV [CR [HV _]]].
    exists CV; exact HV. }
  destruct (GaussianFiniteSums.finite_polynomial_bound_sum d I
    (fun i xs => gaussian_row_velocity n m beta gamma y B Y S a i xs) 2 HBsum) as [B1 HB1].
  destruct (FiniteGaussianParameter.finite_gaussian_parameter_differentiation d F Dv D2 a rho
    C2 4 C0 2 B1 2 Hrho HD HD2 Hpoly2 HCF HCD HpolyF HB1) as [_ [HDdom HE]].
  destruct (MultirowFullSteinResults.paper_multirow_full_stein_results) as [FS1 FS2].
  have Hcancel : gaussian_iterated_expectation d
      (fun xs => finite_sum
        (fun i => gaussian_row_velocity n m beta gamma y B Y S a i xs) I) =
    (sqrt a / (2 * INR (Datatypes.S n) * sqrt (INR (Datatypes.S n)))) *
      finite_sum (fun i => gaussian_iterated_expectation d
        (gaussian_row_remainder n m beta gamma y B Y S a i)) I.
  { exact: (proj2 (proj2 (proj2 (proj2
      (FS2 n m beta gamma y B Y S a Hb Hg HY HS Hsym Ha))))). }
  have HE' : @is_derive R R^o R^o a 1
      (fun t => gaussian_iterated_expectation d (gaussian_array_value n m beta gamma y B Y S t))
      (gaussian_iterated_expectation d
        (fun xs => finite_sum
          (fun i => gaussian_row_velocity n m beta gamma y B Y S a i xs) I)) := HE.
  split; [exact: HDdom|].
  split.
  { move=> i Hi.
    have Hi' : (i <= m)%coq_nat by lia.
    exact: (proj1 (proj2 (FS1 n m beta gamma y B Y S a i Hb Hg HY HS Hsym Ha Hi'))). }
  split; [exact: HE'|].
  split; [exact: Hcancel|].
  rewrite -Hcancel; exact: HE'.
Qed.

(* Clause 4. *)

Theorem mexp_clause_endpoints n m beta gamma y B Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  gaussian_list_domain (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat
    (multirow_goe_value n m beta gamma y B Y S) /\
  gaussian_list_domain (Datatypes.S m * Datatypes.S n)%coq_nat
    (multirow_quadratic_value n m beta gamma y B Y S) /\
  gaussian_iterated_expectation
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_array_value n m beta gamma y B Y S 0) =
  gaussian_iterated_expectation (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat
    (multirow_goe_value n m beta gamma y B Y S) /\
  gaussian_iterated_expectation
    (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
    (gaussian_array_value n m beta gamma y B Y S 1) =
  gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
    (multirow_quadratic_value n m beta gamma y B Y S) /\
  ((fun t => gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S t))
    @ within (fun t : R => 0 <= t <= 1) (nbhs (0 : R)) -->
    gaussian_iterated_expectation (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat
      (multirow_goe_value n m beta gamma y B Y S))%classic /\
  ((fun t => gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S t))
    @ within (fun t : R => 0 <= t <= 1) (nbhs (1 : R)) -->
    gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
      (multirow_quadratic_value n m beta gamma y B Y S))%classic.
Proof.
  move=> Hb Hg HY HS.
  destruct (mexp_value_polynomial n m beta gamma y B Y S Hb Hg HY HS) as [C [HC HP]].
  have H01 : 0 <= 0 <= 1 by lra.
  have H11 : 0 <= 1 <= 1 by lra.
  have HdomG : gaussian_list_domain (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat
      (multirow_goe_value n m beta gamma y B Y S).
  { apply: (GaussianBlockExchange.gaussian_list_domain_polynomial _ _ C 2).
    - apply: (GaussianCoordinateTopology.finite_joint_continuous_ext _
        (fun zs => gaussian_array_value n m beta gamma y B Y S 0
          (mexp_goe_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) zs))).
      + move=> zs HL; exact: mexp_value_zero_lift.
      + apply: mexp_goe_lift_continuous; exact: mexp_value_continuous.
    - apply: (mexp_bound_ext _ _ _
        (fun zs => gaussian_array_value n m beta gamma y B Y S 0
          (mexp_goe_lift (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) zs))).
      + move=> zs HL; exact: mexp_value_zero_lift.
      + apply: mexp_goe_lift_polynomial; exact: (HP 0 H01). }
  have HdomW : gaussian_list_domain (Datatypes.S m * Datatypes.S n)%coq_nat
      (multirow_quadratic_value n m beta gamma y B Y S).
  { apply: (GaussianBlockExchange.gaussian_list_domain_polynomial _ _ C 2).
    - apply: (GaussianCoordinateTopology.finite_joint_continuous_ext _
        (fun xs => gaussian_array_value n m beta gamma y B Y S 1
          (mexp_quadratic_lift (Datatypes.S m) (Datatypes.S n)
            (Datatypes.S (goe_vector_index n)) xs))).
      + move=> xs HL; exact: mexp_value_one_lift.
      + apply: mexp_quadratic_lift_continuous; exact: mexp_value_continuous.
    - apply: (mexp_bound_ext _ _ _
        (fun xs => gaussian_array_value n m beta gamma y B Y S 1
          (mexp_quadratic_lift (Datatypes.S m) (Datatypes.S n)
            (Datatypes.S (goe_vector_index n)) xs))).
      + move=> xs HL; exact: mexp_value_one_lift.
      + apply: mexp_quadratic_lift_polynomial; exact: (HP 1 H11). }
  have E0 : gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S 0) =
    gaussian_iterated_expectation (Datatypes.S m * Datatypes.S (goe_vector_index n))%coq_nat
      (multirow_goe_value n m beta gamma y B Y S).
  { transitivity (gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (fun xs => multirow_goe_value n m beta gamma y B Y S
        (mexp_row_suffixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs))).
    - apply: GaussianProduct.gaussian_iterated_expectation_ext => xs HL.
      exact: mexp_value_zero_suffixes.
    - exact: (mexp_row_suffixes_gaussian_expectation (Datatypes.S m) (Datatypes.S n)
        (Datatypes.S (goe_vector_index n))). }
  have E1 : gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (gaussian_array_value n m beta gamma y B Y S 1) =
    gaussian_iterated_expectation (Datatypes.S m * Datatypes.S n)%coq_nat
      (multirow_quadratic_value n m beta gamma y B Y S).
  { transitivity (gaussian_iterated_expectation
      (Datatypes.S m * (Datatypes.S n + Datatypes.S (goe_vector_index n)))%coq_nat
      (fun xs => multirow_quadratic_value n m beta gamma y B Y S
        (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S (goe_vector_index n)) xs))).
    - apply: GaussianProduct.gaussian_iterated_expectation_ext => xs HL.
      exact: mexp_value_one_prefixes.
    - exact: (GaussianRowMarginal.row_prefixes_gaussian_expectation (Datatypes.S m)
        (Datatypes.S n) (Datatypes.S (goe_vector_index n))). }
  split; [exact HdomG|]; split; [exact HdomW|]; split; [exact E0|]; split; [exact E1|].
  split.
  - rewrite -E0; exact: (mexp_value_expectation_continuous n m beta gamma y B Y S 0
      Hb Hg HY HS H01).
  - rewrite -E1; exact: (mexp_value_expectation_continuous n m beta gamma y B Y S 1
      Hb Hg HY HS H11).
Qed.
