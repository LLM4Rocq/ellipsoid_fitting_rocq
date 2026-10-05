From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions MatrixDefinitions OperatorDefinitions GoeDefinitions JointDefinitions
  SecondChaosDefinitions GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  MatrixTrace CoefficientBounds GoeSynthesis JointUniform JointGrowth
  LowerDefinitions FullThirdDefinitions LowerBounds FullThirdBlock
  BlockOperatorDefinitions BlockBasis RowArrayDefinitions RowObservableDefinitions RowDecoderRegularity.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/RowObservableBounds.v from Coquelicot to
   MathComp-Analysis.

   Imports. The original imported the bundles GaussianCoordinateProofs,
   InterpolationFoundations and InterpolationProofs, and opened five of their
   inner modules: MatrixTrace and CoefficientBounds (from
   InterpolationFoundations), JointUniform and JointGrowth (from
   InterpolationProofs.JointProofs) and GoeSynthesis (from
   InterpolationProofs.JointProofs.GoeProofs). The port imports these five
   standalone ported modules directly. It uses nothing else from the
   bundles: the original named no inner module of GaussianCoordinateProofs.
   The other imports are those of the original.

   Every lemma and theorem keeps its name and its arguments, in the same
   order. No item is added. The statements change form in the following
   ways, the ways of the ported modules this one uses. None changes meaning.

   1. Norms. Coquelicot's norm U becomes MathComp's norm (`|U|)%R. On
      vector n, matrix n and block_array n m the norms are those of the ports
      of OperatorDefinitions, MatrixDefinitions and LowerDefinitions. They
      nest euclidean_product of MatrixEuclideanProduct and keep Coquelicot's
      product norm, so they are the Euclidean norm of all entries, as in the
      original, and not MathComp's max norm (difference 1 of
      analysis/README.md). Every bound therefore means the same, constants
      included. The bounds are stated with Stdlib's order, product, sum,
      power, inverse, sqrt and INR around MathComp's norms, and Rabs stays
      Stdlib's.

   2. Joint vectors. In row_observables_uniform_pair_growth, Coquelicot's
        prod_NormedModule R_AbsRing (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n))
      becomes
        euclidean_product (vector_NormedModule n)
          (vector_NormedModule (goe_vector_index n)),
      the joint vectors of the ported JointDefinitions, JointGrowth and
      RowDecoderRegularity. Its norm is Coquelicot's product norm
      sqrt (norm (fst q) ^ 2 + norm (snd q) ^ 2), so the bounds
      (1 + norm q) ^ 2 mean what they meant.

   3. Naturals and lists. With ssreflect loaded, (i <= m)%nat means
      ssrnat's boolean leq, + and * on nat mean ssrnat's addn and muln, and
      the bare name seq means MathComp's type of sequences. The original
      means Stdlib's Peano order le, Nat.add, Nat.mul and the list
      seq 0 (S m). The statements therefore write (i <= m)%coq_nat,
      (S m * (S n + S (goe_vector_index n)))%coq_nat and
      List.seq 0 (Datatypes.S m), as in the ported RowDecoderRegularity,
      LowerBounds and FullThirdBlock. The order and the list are the terms of
      the original. The dimension elaborates to
      Nat.mul (S m) (addn (S n) (S (goe_vector_index n))), the term of
      RowDecoderRegularity: Nat.mul reads its arguments in nat_scope, so the
      inner sum is ssrnat's addn. In MathComp 2.6 addn is defined as Nat.add,
      so the term is convertible with the original one and denotes the same
      number.

   The proofs follow the original. Coquelicot's linear_norm applied to
   block_inject_linear becomes the second component of the ported
   block_inject_linear, which states the norm bound of Coquelicot's
   is_linear as a conjunct. norm_ge_0 becomes normr_ge0 through RleP, and
   norm_prod with Rmax_l and Rmax_r becomes euclidean_product_norm_fst and
   euclidean_product_norm_snd. The joint vector q is not destructed, as in
   the port of JointGrowth: a pair written (x, z) without a type annotation
   would get MathComp's max norm. Stdlib's "rewrite A, B" becomes an
   ssreflect rewrite.

   Assumptions. Print Assumptions lists the seven axioms of
   analysis/README.md for row_chaos_contraction_norm_bound, and the seven
   and Classical_Prop.classic for the three other items. Their statements
   mention lower_block_first or lower_block_third, which are built from
   soft_max and so from Stdlib's Rpower.ln; no proof here calls classic. *)

(* A norm is nonnegative, stated with Stdlib's order. *)
Local Ltac row_norm_nonneg := apply/RleP; apply normr_ge0.

Lemma row_chaos_contraction_norm_bound n (T : matrix n -> matrix n -> matrix n -> R) K x :
  0 <= K ->
  (forall U V W, Rabs (T U V W) <= K * (`|U|)%R * (`|V|)%R * (`|W|)%R) ->
  Rabs (chaos_contraction n T x) <=
    (/2 * INR (Datatypes.S n)^2 * K * (2 * INR (Datatypes.S n)^2)^3) * (1+(`|x|)%R)^2.
Proof.
  intros HK HB; set (J := 2 * INR (Datatypes.S n)^2).
  assert (HJ : 0 <= J) by (unfold J; pose proof (pow2_ge_0 (INR (Datatypes.S n))); nra).
  assert (Hx : 0 <= (`|x|)%R) by row_norm_nonneg.
  assert (HL : 0 <= K * J^3 * (`|x|)%R^2).
  { apply Rmult_le_pos; [apply Rmult_le_pos; [exact HK|apply pow_le; exact HJ]|apply pow2_ge_0]. }
  assert (HC : forall a b, (a <= n)%coq_nat -> (b <= n)%coq_nat ->
    Rabs (T (chaos_first n x a) (chaos_first n x b) (chaos_second n a b)) <=
      K * J^3 * (`|x|)%R^2).
  { intros a b Ha Hb; eapply Rle_trans; [apply HB|].
    replace (K * J^3 * (`|x|)%R^2) with
      (K * (J*(`|x|)%R) * (J*(`|x|)%R) * J) by ring.
    apply Rmult_le_compat; try row_norm_nonneg.
    - repeat apply Rmult_le_pos; try exact HK; row_norm_nonneg.
    - apply Rmult_le_compat; try row_norm_nonneg.
      + apply Rmult_le_pos; [exact HK|row_norm_nonneg].
      + apply Rmult_le_compat_l; [exact HK|apply joint_chaos_first_norm; exact Ha].
      + apply joint_chaos_first_norm; exact Hb.
    - apply joint_chaos_second_norm; assumption. }
  unfold chaos_contraction; rewrite Rabs_mult (Rabs_pos_eq (/2)); [lra|].
  apply Rle_trans with
    (/2 * (INR (Datatypes.S n) * (INR (Datatypes.S n) * (K * J^3 * (`|x|)%R^2)))).
  - apply Rmult_le_compat_l; [lra|].
    apply coordinate_sum_abs_bound; [apply Rmult_le_pos; [apply pos_INR|exact HL]|].
    intros a Ha; apply coordinate_sum_abs_bound; [exact HL|intros b Hb; apply HC; assumption].
  - change (/2 * (INR (Datatypes.S n) * (INR (Datatypes.S n) * (K * J^3 * (`|x|)%R^2))) <=
      (/2 * INR (Datatypes.S n)^2 * K * J^3) * (1+(`|x|)%R)^2).
    replace (/2 * (INR (Datatypes.S n) * (INR (Datatypes.S n) * (K * J^3 * (`|x|)%R^2)))) with
      ((/2 * INR (Datatypes.S n)^2 * K * J^3) * (`|x|)%R^2) by ring.
    apply Rmult_le_compat_l.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|exact HK]|apply pow_le; exact HJ].
    + nra.
Qed.

Lemma block_injected_uniform_bounds n m beta gamma y B Y S k i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<=k ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  exists L1 L3 : R, 0<=L1 /\ 0<=L3 /\ forall A U V W,
    Rabs (lower_block_first n m beta gamma y B Y S A (block_inject n m i U)) <= L1*(`|U|)%R /\
    Rabs (lower_block_third n m beta gamma y B Y S A
      (block_inject n m i U) (block_inject n m i V) (block_inject n m i W)) <=
      L3*(`|U|)%R*(`|V|)%R*(`|W|)%R.
Proof.
  intros Hb Hg HY HS Hk Hy HB.
  destruct (proj2 (block_inject_linear n m i)) as [L [HL Hnorm]].
  set (K1 := sqrt (INR (Datatypes.S n))*k).
  set (K3 := 8*K1^3*(beta+gamma)^2).
  assert (H1 : 0<=K1) by (unfold K1; apply Rmult_le_pos; [apply sqrt_pos|exact Hk]).
  assert (H3 : 0<=K3).
  { unfold K3; apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow_le; exact H1]|apply pow2_ge_0]. }
  exists (K1*L), (K3*L^3); split; [apply Rmult_le_pos; lra|].
  split; [apply Rmult_le_pos; [exact H3|apply pow_le; lra]|].
  intros A U V W; split.
  - eapply Rle_trans; [apply (lower_block_first_bound n m beta gamma y B Y S A _ k); assumption|].
    change (K1*(`|block_inject n m i U|)%R<=K1*L*(`|U|)%R).
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H1|apply Hnorm].
  - eapply Rle_trans; [apply (lower_block_third_bound n m beta gamma y B Y S A _ _ _ k); assumption|].
    change (K3*(`|block_inject n m i U|)%R*(`|block_inject n m i V|)%R*
      (`|block_inject n m i W|)%R<=K3*L^3*(`|U|)%R*(`|V|)%R*(`|W|)%R).
    replace (K3*L^3*(`|U|)%R*(`|V|)%R*(`|W|)%R) with
      (K3*(L*(`|U|)%R)*(L*(`|V|)%R)*(L*(`|W|)%R)) by ring.
    apply Rmult_le_compat; try row_norm_nonneg.
    + apply Rmult_le_pos; [apply Rmult_le_pos; [exact H3|row_norm_nonneg]|row_norm_nonneg].
    + apply Rmult_le_compat; try row_norm_nonneg.
      * apply Rmult_le_pos; [exact H3|row_norm_nonneg].
      * apply Rmult_le_compat_l; [exact H3|apply Hnorm].
      * apply Hnorm.
    + apply Hnorm.
Qed.

Theorem row_observables_uniform_pair_growth n m beta gamma y B Y S k t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<=k ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  exists CV CR : R, 0<=CV /\ 0<=CR /\
  forall (A : block_array n m)
    (q : euclidean_product (vector_NormedModule n) (vector_NormedModule (goe_vector_index n))),
    Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (joint_quadratic_input n (fst q))) / (2*sqrt t) -
      lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (goe_matrix n (snd q))) / (2*sqrt (1-t))) <= CV*(1+(`|q|)%R)^2 /\
    Rabs (chaos_contraction n (fun U V W => lower_block_third n m beta gamma y B Y S A
      (block_inject n m i U) (block_inject n m i V) (block_inject n m i W)) (fst q)) <=
      CR*(1+(`|q|)%R)^2.
Proof.
  intros Hb Hg HY HS Hk Hy HB.
  destruct (block_injected_uniform_bounds n m beta gamma y B Y S k i Hb Hg HY HS Hk Hy HB)
    as [L1 [L3 [H1 [H3 HC]]]].
  set (KW := INR (Datatypes.S n)^2 * Rabs (/sqrt (INR (Datatypes.S n)))).
  set (KG := goe_scale n * INR (Datatypes.S (goe_vector_index n))).
  set (KR := /2 * INR (Datatypes.S n)^2 * L3 * (2*INR (Datatypes.S n)^2)^3).
  assert (HW : 0<=KW) by (unfold KW; apply Rmult_le_pos; [apply pow2_ge_0|apply Rabs_pos]).
  assert (HG : 0<=KG) by (unfold KG; apply Rmult_le_pos; [pose proof (goe_scale_positive n); lra|apply pos_INR]).
  assert (HR : 0<=KR).
  { unfold KR; apply Rmult_le_pos.
    - apply Rmult_le_pos; [apply Rmult_le_pos; [lra|apply pow2_ge_0]|exact H3].
    - apply pow_le; apply Rmult_le_pos; [lra|apply pow2_ge_0]. }
  exists (Rabs (/(2*sqrt t))*L1*KW+Rabs (/(2*sqrt (1-t)))*L1*KG), KR.
  split.
  { apply Rplus_le_le_0_compat; apply Rmult_le_pos;
      try (apply Rmult_le_pos; [apply Rabs_pos|exact H1]); assumption. }
  split; [exact HR|]; intros A q.
  assert (HX : (`|fst q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_fst).
  assert (HZ : (`|snd q|)%R <= (`|q|)%R) by (apply/RleP; apply euclidean_product_norm_snd).
  assert (HN : 0<=(`|q|)%R) by row_norm_nonneg.
  assert (HNX : 0<=(`|fst q|)%R) by row_norm_nonneg.
  assert (HP : Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (joint_quadratic_input n (fst q))))
    <= (L1*KW)*(1+(`|q|)%R)^2).
  { eapply Rle_trans;
      [apply (proj1 (HC A (joint_quadratic_input n (fst q)) (matrix_zero n) (matrix_zero n)))|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H1|].
    eapply Rle_trans; [apply joint_quadratic_input_norm|].
    apply Rmult_le_compat_l; [exact HW|nra]. }
  assert (HQ : Rabs (lower_block_first n m beta gamma y B Y S A
      (block_inject n m i (goe_matrix n (snd q))))
    <= (L1*KG)*(1+(`|q|)%R)^2).
  { eapply Rle_trans;
      [apply (proj1 (HC A (goe_matrix n (snd q)) (matrix_zero n) (matrix_zero n)))|].
    rewrite Rmult_assoc; apply Rmult_le_compat_l; [exact H1|].
    eapply Rle_trans; [apply goe_matrix_norm_bound|].
    change (KG*(`|snd q|)%R <= KG*(1+(`|q|)%R)^2).
    apply Rmult_le_compat_l; [exact HG|nra]. }
  split.
  - eapply Rle_trans; [apply Rabs_triang|].
    unfold Rdiv; rewrite Rabs_Ropp !Rabs_mult.
    replace ((Rabs (/(2*sqrt t))*L1*KW+Rabs (/(2*sqrt (1-t)))*L1*KG)*(1+(`|q|)%R)^2) with
      (Rabs (/(2*sqrt t))*((L1*KW)*(1+(`|q|)%R)^2)+
       Rabs (/(2*sqrt (1-t)))*((L1*KG)*(1+(`|q|)%R)^2)) by ring.
    rewrite (Rmult_comm _ (Rabs (/(2*sqrt t)))) (Rmult_comm _ (Rabs (/(2*sqrt (1-t))))).
    apply Rplus_le_compat; apply Rmult_le_compat_l; try apply Rabs_pos; assumption.
  - eapply Rle_trans;
      [apply row_chaos_contraction_norm_bound; [exact H3|intros; apply (proj2 (HC A _ _ _))]|].
    change (KR*(1+(`|fst q|)%R)^2<=KR*(1+(`|q|)%R)^2).
    apply Rmult_le_compat_l; [exact HR|nra].
Qed.

Theorem gaussian_row_observables_polynomial_bounds n m beta gamma y B Y S k t i :
  0<beta -> 0<gamma -> Y<>[] -> S<>[] -> 0<=k -> (i<=m)%coq_nat ->
  (forall z, In z Y -> euclidean_norm (y z) (List.seq 0 (Datatypes.S m)) = 1) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  exists CV CR : R,
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CV 2
      (gaussian_row_velocity n m beta gamma y B Y S t i) /\
    finite_polynomial_bound (Datatypes.S m * (Datatypes.S n+Datatypes.S (goe_vector_index n)))%coq_nat CR 2
      (gaussian_row_remainder n m beta gamma y B Y S t i).
Proof.
  intros Hb Hg HY HS Hk Hi Hy HB.
  destruct (row_observables_uniform_pair_growth n m beta gamma y B Y S k t i Hb Hg HY HS Hk Hy HB)
    as [CV [CR [HV [HR HC]]]].
  exists CV, CR; split; split; try assumption; intros xs HL;
    destruct (HC (gaussian_row_array n m t xs) (gaussian_row_pair n i xs)) as [HVB HRB].
  - eapply Rle_trans; [exact HVB|apply Rmult_le_compat_l; [exact HV|apply (gaussian_row_pair_squared_weight n m i xs Hi HL)]].
  - eapply Rle_trans; [exact HRB|apply Rmult_le_compat_l; [exact HR|apply (gaussian_row_pair_squared_weight n m i xs Hi HL)]].
Qed.
