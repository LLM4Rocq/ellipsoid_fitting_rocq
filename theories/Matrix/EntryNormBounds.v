From Stdlib Require Import Reals Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Gibbs.NestedGradientDefinitions
  Gibbs.HessianDefinitions Matrix.ThirdOrderArrays Tensor.ThirdArrayContraction
  Matrix.CoefficientMaps.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Bounds between the entries and the norms of tuples and matrices, for the
   Euclidean norm of Matrix.Definitions (the Frobenius norm on matrices). An
   entry is bounded by the norm (tuple_entry_norm_bound,
   matrix_entry_norm_bound). A sum or a tuple of S n terms of norm at most
   K has norm at most INR (S n) * K (module_coordinate_sum_norm_bound,
   tuple_build_norm_bound), and
   Rabs (trace_pair n A B) <= INR (S n) ^ 2 * `|A| * `|B|
   (trace_pair_product_bound). In norm_pair_le_sum the pair lives in
   euclidean_product U V, whose norm is Euclidean, not the max norm. *)

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
