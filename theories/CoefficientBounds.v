From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates GradientDefinitions
  HessianDefinitions ContinuityDefinitions CoefficientDefinitions CoefficientMaps.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Port of theories/CoefficientBounds.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order. No item is added. The statements change form in the
   ways of the ports of MatrixCoordinates and CoefficientMaps.

   1. Norms. Coquelicot's norm x becomes MathComp's norm (`|x|)%R. The norms
      are those of MatrixDefinitions, HessianDefinitions and
      ContinuityDefinitions: the Euclidean norm of all entries on tuples,
      matrices, Hessian arrays and third-order arrays. So every bound below
      means the same as in the original, constants included. The bounds are
      stated with Stdlib's order, product, INR and power around MathComp's
      norms. The absolute value Rabs of the original stays Stdlib's Rabs,
      which is the norm of R^o (RabsE).

   2. Coquelicot's NormedModule R_AbsRing becomes normedModType R and its
      R_NormedModule becomes R^o.

   3. The pair of norm_pair_le_sum. In the original, norm (x, y) is the norm
      of Coquelicot's prod_NormedModule, sqrt (norm x ^ 2 + norm y ^ 2).
      MathComp-Analysis gives U * V the max norm instead. The port writes the
      pair as (x, y) : euclidean_product U V, the product of
      MatrixEuclideanProduct that keeps Coquelicot's norm and that
      tuple_NormedModule is built from. The statement therefore means the
      same as the original, and it applies to the tuples of
      tuple_build_norm_bound as before.

   4. Order on indices. With ssreflect loaded, (i <= n)%nat means ssrnat's
      boolean leq. The original means Stdlib's Peano order le, so the
      statements write (i <= n)%coq_nat, which is Stdlib's le.

   The proofs follow the original. Coquelicot's norm_prod, norm_triangle and
   norm_scal are replaced by euclidean_product_norm_fst,
   euclidean_product_norm_snd and euclidean_product_norm_le of
   MatrixEuclideanProduct, and by MathComp's ler_normD and normrZ. *)

Lemma tuple_entry_norm_bound (V : normedModType R) n i (x : tuple_NormedModule V n) :
  (`|tuple_entry V n i x|)%R <= (`|x|)%R.
Proof.
  revert i x; induction n as [|n IH]; intros [|i] x; simpl.
  - apply Rle_refl.
  - rewrite normr0; apply/RleP; apply normr_ge0.
  - apply/RleP; exact (euclidean_product_norm_fst x).
  - eapply Rle_trans; [apply IH |].
    apply/RleP; exact (euclidean_product_norm_snd x).
Qed.

Theorem matrix_entry_norm_bound n (A : matrix n) i j :
  Rabs (matrix_entry n A i j) <= (`|A|)%R.
Proof.
  unfold matrix_entry; rewrite RabsE.
  eapply Rle_trans; [apply (tuple_entry_norm_bound R^o) |].
  apply tuple_entry_norm_bound.
Qed.

Theorem hessian_entry_norm_bound n (H : hessian_array n) i j :
  (`|hessian_entry n H i j|)%R <= (`|H|)%R.
Proof.
  unfold hessian_entry.
  eapply Rle_trans; [apply tuple_entry_norm_bound | apply tuple_entry_norm_bound].
Qed.

Theorem third_entry_norm_bound n (T : third_array n) i j :
  (`|third_entry n T i j|)%R <= (`|T|)%R.
Proof.
  unfold third_entry.
  eapply Rle_trans; [apply tuple_entry_norm_bound | apply tuple_entry_norm_bound].
Qed.

Lemma norm_pair_le_sum {U V : normedModType R} (x : U) (y : V) :
  (`|(x, y) : euclidean_product U V|)%R <= (`|x|)%R + (`|y|)%R.
Proof.
  apply/RleP; exact (euclidean_product_norm_le ((x, y) : euclidean_product U V)).
Qed.

Lemma module_coordinate_sum_norm_bound (V : normedModType R) n f K :
  0 <= K -> (forall i, (i <= n)%coq_nat -> (`|f i|)%R <= K) ->
  (`|module_coordinate_sum V n f|)%R <= INR (S n) * K.
Proof.
  intros HK; revert f; induction n as [|n IH]; intros f HF.
  - change ((`|f O|)%R <= 1 * K); pose proof (HF O (Nat.le_refl O)); lra.
  - cbn [module_coordinate_sum].
    assert (HH : (`|f O|)%R <= K) by (apply HF; lia).
    assert (HT : (`|module_coordinate_sum V n (fun i => f (S i))|)%R <= INR (S n) * K).
    { apply IH; intros i Hi; apply HF; lia. }
    eapply Rle_trans; [apply/RleP; apply ler_normD |].
    change ((`|f O|)%R + (`|module_coordinate_sum V n (fun i => f (S i))|)%R <=
      INR (S (S n)) * K).
    rewrite S_INR; nra.
Qed.

Lemma tuple_build_norm_bound (V : normedModType R) n f K :
  0 <= K -> (forall i, (i <= n)%coq_nat -> (`|f i|)%R <= K) ->
  (`|tuple_build V n f|)%R <= INR (S n) * K.
Proof.
  intros HK; revert f; induction n as [|n IH]; intros f HF.
  - change ((`|f O|)%R <= 1 * K); pose proof (HF O (Nat.le_refl O)); lra.
  - cbn [tuple_build].
    assert (HH : (`|f O|)%R <= K) by (apply HF; lia).
    assert (HT : (`|tuple_build V n (fun i => f (S i))|)%R <= INR (S n) * K).
    { apply IH; intros i Hi; apply HF; lia. }
    eapply Rle_trans; [apply norm_pair_le_sum |].
    eapply Rle_trans with (K + INR (S n) * K).
    + apply Rplus_le_compat; [exact HH | exact HT].
    + rewrite (S_INR (S n)); nra.
Qed.

Theorem matrix_build_norm_bound n f K :
  0 <= K -> (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat -> Rabs (f i j) <= K) ->
  (`|matrix_build n f|)%R <= INR (S n) ^ 2 * K.
Proof.
  intros HK HF; unfold matrix_build.
  replace (INR (S n) ^ 2 * K) with (INR (S n) * (INR (S n) * K)) by ring.
  apply tuple_build_norm_bound.
  - apply Rmult_le_pos; [apply pos_INR | exact HK].
  - intros i Hi; apply (tuple_build_norm_bound R^o); [exact HK |].
    intros j Hj; rewrite -RabsE; apply HF; assumption.
Qed.

Lemma coordinate_sum_abs_bound n f K :
  0 <= K -> (forall i, (i <= n)%coq_nat -> Rabs (f i) <= K) ->
  Rabs (coordinate_sum n f) <= INR (S n) * K.
Proof.
  intros HK HF.
  assert (HF' : forall i, (i <= n)%coq_nat -> (`|f i : R^o|)%R <= K).
  { intros i Hi; rewrite -RabsE; apply HF; exact Hi. }
  pose proof (module_coordinate_sum_norm_bound R^o n f K HK HF') as H.
  rewrite module_coordinate_sum_real -RabsE in H; exact H.
Qed.

Theorem trace_pair_product_bound n (A B : matrix n) :
  Rabs (trace_pair n A B) <= INR (S n) ^ 2 * (`|A|)%R * (`|B|)%R.
Proof.
  unfold trace_pair.
  replace (INR (S n) ^ 2 * (`|A|)%R * (`|B|)%R) with
    (INR (S n) * (INR (S n) * ((`|A|)%R * (`|B|)%R))) by ring.
  assert (HA : 0 <= (`|A|)%R) by (apply/RleP; apply normr_ge0).
  assert (HB : 0 <= (`|B|)%R) by (apply/RleP; apply normr_ge0).
  apply coordinate_sum_abs_bound.
  - repeat apply Rmult_le_pos; try apply pos_INR; assumption.
  - intros i Hi; apply coordinate_sum_abs_bound.
    + apply Rmult_le_pos; assumption.
    + intros j Hj; rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos; apply matrix_entry_norm_bound.
Qed.

Theorem coefficient_contract_product_bound (V : normedModType R) n F W K :
  0 <= K -> (forall i j, (i <= n)%coq_nat -> (j <= n)%coq_nat -> (`|F i j|)%R <= K) ->
  (`|coefficient_contract V n F W|)%R <= INR (S n) ^ 2 * K * (`|W|)%R.
Proof.
  intros HK HF; unfold coefficient_contract.
  assert (HW : 0 <= (`|W|)%R) by (apply/RleP; apply normr_ge0).
  replace (INR (S n) ^ 2 * K * (`|W|)%R) with
    (INR (S n) * (INR (S n) * ((`|W|)%R * K))) by ring.
  apply module_coordinate_sum_norm_bound.
  - repeat apply Rmult_le_pos; try apply pos_INR; assumption.
  - intros i Hi; apply module_coordinate_sum_norm_bound.
    + apply Rmult_le_pos; assumption.
    + intros j Hj; rewrite normrZ -RmultE -RabsE.
      apply Rmult_le_compat.
      * apply Rabs_pos.
      * apply/RleP; apply normr_ge0.
      * apply matrix_entry_norm_bound.
      * apply HF; assumption.
Qed.

Theorem third_action_product_bound n (T : third_array n) (W : matrix n) :
  (`|third_action n T W|)%R <= INR (S n) ^ 2 * (`|T|)%R * (`|W|)%R.
Proof.
  unfold third_action; apply coefficient_contract_product_bound.
  - apply/RleP; apply normr_ge0.
  - intros; apply third_entry_norm_bound.
Qed.

Theorem hessian_action_product_bound n (H : hessian_array n) (V : matrix n) :
  (`|hessian_action n H V|)%R <= INR (S n) ^ 4 * (`|H|)%R * (`|V|)%R.
Proof.
  unfold hessian_action.
  assert (HH : 0 <= (`|H|)%R) by (apply/RleP; apply normr_ge0).
  assert (HV : 0 <= (`|V|)%R) by (apply/RleP; apply normr_ge0).
  replace (INR (S n) ^ 4 * (`|H|)%R * (`|V|)%R) with
    (INR (S n) ^ 2 * (INR (S n) ^ 2 * (`|H|)%R * (`|V|)%R)) by ring.
  apply matrix_build_norm_bound.
  - apply Rmult_le_pos; [apply Rmult_le_pos; [apply pow2_ge_0 | exact HH] | exact HV].
  - intros i j Hi Hj; eapply Rle_trans; [apply trace_pair_product_bound |].
    apply Rmult_le_compat_r; [exact HV |].
    apply Rmult_le_compat_l; [apply pow2_ge_0 | apply hessian_entry_norm_bound].
Qed.

Theorem hessian_evaluation_product_bound n (H : hessian_array n) (U V : matrix n) :
  Rabs (hessian_evaluation n H U V) <=
    INR (S n) ^ 6 * (`|H|)%R * (`|U|)%R * (`|V|)%R.
Proof.
  unfold hessian_evaluation; eapply Rle_trans; [apply trace_pair_product_bound |].
  assert (HU : 0 <= (`|U|)%R) by (apply/RleP; apply normr_ge0).
  replace (INR (S n) ^ 6 * (`|H|)%R * (`|U|)%R * (`|V|)%R) with
    (INR (S n) ^ 2 * (INR (S n) ^ 4 * (`|H|)%R * (`|V|)%R) * (`|U|)%R) by ring.
  apply Rmult_le_compat_r; [exact HU |].
  apply Rmult_le_compat_l; [apply pow2_ge_0 | apply hessian_action_product_bound].
Qed.

Theorem third_evaluation_product_bound n (T : third_array n) (U V W : matrix n) :
  Rabs (third_evaluation n T U V W) <=
    INR (S n) ^ 8 * (`|T|)%R * (`|U|)%R * (`|V|)%R * (`|W|)%R.
Proof.
  unfold third_evaluation, hessian_evaluation.
  assert (HU : 0 <= (`|U|)%R) by (apply/RleP; apply normr_ge0).
  assert (HV : 0 <= (`|V|)%R) by (apply/RleP; apply normr_ge0).
  eapply Rle_trans; [apply trace_pair_product_bound |].
  eapply Rle_trans with (INR (S n) ^ 2 *
    (INR (S n) ^ 4 * (`|third_action n T W|)%R * (`|V|)%R) * (`|U|)%R).
  - apply Rmult_le_compat_r; [exact HU |].
    apply Rmult_le_compat_l; [apply pow2_ge_0 | apply hessian_action_product_bound].
  - replace (INR (S n) ^ 8 * (`|T|)%R * (`|U|)%R * (`|V|)%R * (`|W|)%R) with
      (INR (S n) ^ 2 * (INR (S n) ^ 4 *
        (INR (S n) ^ 2 * (`|T|)%R * (`|W|)%R) * (`|V|)%R) * (`|U|)%R) by ring.
    apply Rmult_le_compat_r; [exact HU |].
    apply Rmult_le_compat_l; [apply pow2_ge_0 |].
    apply Rmult_le_compat_r; [exact HV |].
    apply Rmult_le_compat_l; [apply pow_le; apply pos_INR | apply third_action_product_bound].
Qed.
