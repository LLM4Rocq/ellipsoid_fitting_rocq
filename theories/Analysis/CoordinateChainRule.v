(* The chain rule for a function f of K coordinates with continuous partial
   derivatives Df a (finite_coordinate_derivative, finite_joint_continuous)
   along a path u with differentiable coordinates: s |-> f (u s) has
   derivative sum_a Df a (u t) * du a at t (finite_chain_rule). The
   difference f (u s) - f (u t) is telescoped through hybrid lists that
   take their first j coordinates from u s and the others from u t, and
   each step is handled by the mean value theorem.
   finite_coordinate_derivative_comp is the same rule for a coordinate
   section of a composite g (Lam zs). *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import Analysis.CalculusBridge.
From EllipsoidFitting Require Import Soft.Definitions
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateTuples
  Analysis.CoordinatePermutationDefinitions Analysis.CoordinatePermutations
  Gaussian.CoordinateDerivativeDefinitions Analysis.FiniteSumAlgebra.
Import ListNotations.
Open Scope R_scope.

(* Finitely many coordinate paths continuous at t are uniformly close to
   their values at t. *)
Lemma coordinates_uniform_close K (u : R -> list R) (t : R) :
  (forall a, (a < K)%coq_nat -> {for t, continuous (fun s => List.nth a (u s) 0)}) ->
  forall eps, 0 < eps -> exists delta, 0 < delta /\
    forall s, Rabs (s - t) < delta -> forall a, (a < K)%coq_nat ->
      Rabs (List.nth a (u s) 0 - List.nth a (u t) 0) < eps.
Proof.
  induction K as [|K IH]; intros Hc eps Heps.
  - exists 1; split; [lra|intros s _ a Ha; lia].
  - destruct (IH (fun a Ha => Hc a (Nat.lt_lt_succ_r _ _ Ha)) eps Heps) as [d1 [Hd1 H1]].
    destruct (proj1 (continuous_Reals _ _) (Hc K (Nat.lt_succ_diag_r K)) eps Heps)
      as [d2 [Hd2 H2]].
    exists (Rmin d1 d2); split; [apply Rmin_pos; assumption|].
    intros s Hs a Ha.
    destruct (Nat.lt_ge_cases a K) as [HaK|HaK].
    + apply H1; [apply Rlt_le_trans with (Rmin d1 d2); [exact Hs|apply Rmin_l]|exact HaK].
    + assert (a = K) by lia; subst a.
      apply H2; apply Rlt_le_trans with (Rmin d1 d2); [exact Hs|apply Rmin_r].
Qed.

(* One step: the increment G s (h s) - G s x0 of a two-variable function whose
   partial derivative in the second variable exists everywhere and is jointly
   continuous at (t, x0), along a path h with h t = x0. *)
Lemma chain_rule_step (G DG : R -> R -> R) (h : R -> R) (t x0 dh : R) :
  (forall s x, @is_derive R R^o R^o x 1 (fun y => G s y) (DG s x)) ->
  (forall eps, 0 < eps -> exists delta, 0 < delta /\
     forall s x, Rabs (s - t) < delta -> Rabs (x - x0) < delta ->
       Rabs (DG s x - DG t x0) < eps) ->
  @is_derive R R^o R^o t 1 h dh -> h t = x0 ->
  @is_derive R R^o R^o t 1 (fun s => G s (h s) - G s x0) (DG t x0 * dh).
Proof.
  intros HG HDG Hh Hht.
  apply is_derive_of_Reals.
  intros eps Heps.
  pose proof (Rabs_pos (DG t x0)) as HL0.
  pose proof (Rabs_pos dh) as Hdh0.
  set (e2 := eps / (2 * (Rabs (DG t x0) + 1))).
  assert (He2 : 0 < e2).
  { unfold e2; apply Rdiv_lt_0_compat; [exact Heps|lra]. }
  set (e1 := eps / (2 * (Rabs dh + e2))).
  assert (He1 : 0 < e1).
  { unfold e1; apply Rdiv_lt_0_compat; [exact Heps|lra]. }
  destruct (HDG e1 He1) as [d1 [Hd1 H1]].
  destruct (Reals_of_is_derive Hh e2 He2) as [d2 Hq].
  destruct (proj1 (continuous_Reals h t) (is_derive_continuous _ _ _ Hh) d1 Hd1)
    as [d3 [Hd3 H3]].
  assert (Hd : 0 < Rmin d1 (Rmin d2 d3)).
  { apply Rmin_pos; [exact Hd1|apply Rmin_pos; [apply cond_pos|exact Hd3]]. }
  exists (mkposreal _ Hd).
  intros k Hk0 Hk. simpl in Hk.
  assert (Hk1 : Rabs k < d1) by (eapply Rlt_le_trans; [exact Hk|apply Rmin_l]).
  assert (Hk2 : Rabs k < d2)
    by (eapply Rlt_le_trans; [exact Hk|eapply Rle_trans; [apply Rmin_r|apply Rmin_l]]).
  assert (Hk3 : Rabs k < d3)
    by (eapply Rlt_le_trans; [exact Hk|eapply Rle_trans; [apply Rmin_r|apply Rmin_r]]).
  specialize (Hq k Hk0 Hk2).
  assert (Hhs : Rabs (h (t + k) - x0) < d1).
  { rewrite <- Hht. apply H3. replace (t + k - t) with k by ring; exact Hk3. }
  destruct (MVT_cor4 (fun y => G (t + k) y) (DG (t + k)) x0 (Rabs (h (t + k) - x0))
    (fun c _ => HG (t + k) c) (h (t + k)) (Rle_refl _)) as [c [Hc Hcx]].
  assert (HA : Rabs (DG (t + k) c - DG t x0) < e1).
  { apply H1; [replace (t + k - t) with k by ring; exact Hk1|].
    eapply Rle_lt_trans; [exact Hcx|exact Hhs]. }
  cbv beta.
  assert (Heq : (G (t + k) (h (t + k)) - G (t + k) x0 - (G t (h t) - G t x0)) / k - DG t x0 * dh
    = (DG (t + k) c - DG t x0) * ((h (t + k) - h t) / k)
      + DG t x0 * ((h (t + k) - h t) / k - dh)).
  { rewrite Hc Hht. field. exact Hk0. }
  rewrite Heq.
  assert (HQb : Rabs ((h (t + k) - h t) / k) <= Rabs dh + e2).
  { replace ((h (t + k) - h t) / k) with (((h (t + k) - h t) / k - dh) + dh) by ring.
    eapply Rle_trans; [apply Rabs_triang|lra]. }
  assert (Hprod : e1 * (Rabs dh + e2) = eps / 2).
  { unfold e1; field; lra. }
  assert (Hr : Rabs (DG t x0) / (Rabs (DG t x0) + 1) < 1).
  { apply Rmult_lt_reg_r with (Rabs (DG t x0) + 1); [lra|].
    unfold Rdiv; rewrite Rmult_assoc Rinv_l; lra. }
  assert (Hl : Rabs (DG t x0) * e2 < eps / 2).
  { unfold e2.
    replace (Rabs (DG t x0) * (eps / (2 * (Rabs (DG t x0) + 1))))
      with ((Rabs (DG t x0) / (Rabs (DG t x0) + 1)) * (eps / 2)) by (field; lra).
    pose proof (Rmult_lt_compat_r (eps / 2) _ _ (Rdiv_lt_0_compat _ _ Heps Rlt_0_2) Hr).
    lra. }
  eapply Rle_lt_trans; [apply Rabs_triang|].
  rewrite (Rabs_mult (DG (t + k) c - DG t x0)) (Rabs_mult (DG t x0)).
  assert (H1' : Rabs (DG (t + k) c - DG t x0) * Rabs ((h (t + k) - h t) / k)
    <= e1 * (Rabs dh + e2)).
  { apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|lra|exact HQb]. }
  assert (H2' : Rabs (DG t x0) * Rabs ((h (t + k) - h t) / k - dh) <= Rabs (DG t x0) * e2).
  { apply Rmult_le_compat_l; [apply Rabs_pos|lra]. }
  clearbody e1 e2.
  apply Rle_lt_trans with (eps / 2 + Rabs (DG t x0) * e2).
  - apply Rplus_le_compat; [rewrite <- Hprod; exact H1'|exact H2'].
  - lra.
Qed.

(* The hybrid list: the first j coordinates of u s, then those of u t. *)
Definition hybrid_list (K : nat) (u : R -> list R) (t : R) (j : nat) (s : R) : list R :=
  List.map (fun a => if Nat.ltb a j then List.nth a (u s) 0 else List.nth a (u t) 0)
    (List.seq 0 K).

Lemma hybrid_list_length K u t j s : List.length (hybrid_list K u t j s) = K.
Proof. apply length_map_seq. Qed.

Lemma hybrid_list_nth K u t j s a :
  (a < K)%coq_nat ->
  List.nth a (hybrid_list K u t j s) 0 =
  if Nat.ltb a j then List.nth a (u s) 0 else List.nth a (u t) 0.
Proof. intros Ha; unfold hybrid_list; rewrite (nth_map_seq _ _ _ Ha); reflexivity. Qed.

Lemma hybrid_list_zero K u t s :
  List.length (u t) = K -> hybrid_list K u t 0 s = u t.
Proof.
  intros HL; apply list_nth_ext.
  - rewrite hybrid_list_length HL; reflexivity.
  - rewrite hybrid_list_length; intros i Hi.
    rewrite (hybrid_list_nth _ _ _ _ _ _ Hi); reflexivity.
Qed.

Lemma hybrid_list_full K u t s :
  List.length (u s) = K -> hybrid_list K u t K s = u s.
Proof.
  intros HL; apply list_nth_ext.
  - rewrite hybrid_list_length HL; reflexivity.
  - rewrite hybrid_list_length; intros i Hi.
    rewrite (hybrid_list_nth _ _ _ _ _ _ Hi).
    destruct (Nat.ltb i K) eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E; lia.
Qed.

Lemma hybrid_list_at_t K u t j :
  List.length (u t) = K -> hybrid_list K u t j t = u t.
Proof.
  intros HL; apply list_nth_ext.
  - rewrite hybrid_list_length HL; reflexivity.
  - rewrite hybrid_list_length; intros i Hi.
    rewrite (hybrid_list_nth _ _ _ _ _ _ Hi).
    destruct (Nat.ltb i j); reflexivity.
Qed.

Lemma hybrid_list_succ K u t j s :
  (j < K)%coq_nat ->
  hybrid_list K u t (S j) s =
  replace_coordinate j (List.nth j (u s) 0) (hybrid_list K u t j s).
Proof.
  intros Hj; apply list_nth_ext.
  - rewrite replace_coordinate_length !hybrid_list_length; reflexivity.
  - rewrite hybrid_list_length; intros i Hi.
    rewrite (hybrid_list_nth _ _ _ _ _ _ Hi).
    destruct (Nat.eq_dec i j) as [->|Hij].
    + assert (HjL : (j < List.length (hybrid_list K u t j s))%coq_nat)
        by (rewrite hybrid_list_length; exact Hj).
      rewrite (replace_coordinate_nth_same _ _ _ HjL).
      destruct (Nat.ltb j (S j)) eqn:E; [reflexivity|apply Nat.ltb_ge in E; lia].
    + rewrite (replace_coordinate_nth_other j i _ _ (not_eq_sym Hij)).
      rewrite (hybrid_list_nth _ _ _ _ _ _ Hi).
      destruct (Nat.ltb i (S j)) eqn:E1; destruct (Nat.ltb i j) eqn:E2; try reflexivity.
      * apply Nat.ltb_lt in E1; apply Nat.ltb_ge in E2; lia.
      * apply Nat.ltb_ge in E1; apply Nat.ltb_lt in E2; lia.
Qed.

Lemma hybrid_list_replace_same K u t j s :
  (j < K)%coq_nat ->
  replace_coordinate j (List.nth j (u t) 0) (hybrid_list K u t j s) = hybrid_list K u t j s.
Proof.
  intros Hj.
  rewrite <- (replace_coordinate_self j (hybrid_list K u t j s)) at 2.
  f_equal. rewrite (hybrid_list_nth _ _ _ _ _ _ Hj).
  destruct (Nat.ltb j j) eqn:E; [apply Nat.ltb_lt in E; lia|reflexivity].
Qed.

Lemma finite_chain_rule_hybrid K (f : list R -> R) (Df : nat -> list R -> R)
    (u : R -> list R) (du : nat -> R) (t : R) :
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a f (Df a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Df a)) ->
  (forall s, List.length (u s) = K) ->
  (forall a, (a < K)%coq_nat ->
    @is_derive R R^o R^o t 1 (fun s => List.nth a (u s) 0) (du a)) ->
  forall j, (j <= K)%coq_nat ->
  @is_derive R R^o R^o t 1 (fun s => f (hybrid_list K u t j s))
    (finite_sum (fun a => Df a (u t) * du a) (List.seq 0 j)).
Proof.
  intros HD HC HL Hdu.
  assert (Hcont : forall a, (a < K)%coq_nat ->
    {for t, continuous (fun s => List.nth a (u s) 0)}).
  { intros a Ha; exact (is_derive_continuous _ _ _ (Hdu a Ha)). }
  induction j as [|j IH]; intros Hj.
  - simpl.
    apply (is_derive_ext (fun _ => f (u t))).
    + intros s; rewrite (hybrid_list_zero _ _ _ _ (HL t)); reflexivity.
    + apply is_derive_const.
  - assert (HjK : (j < K)%coq_nat) by lia.
    specialize (IH (Nat.lt_le_incl _ _ HjK)).
    rewrite finite_sum_seq_S.
    apply (is_derive_ext (fun s => f (hybrid_list K u t j s) +
      (f (replace_coordinate j (List.nth j (u s) 0) (hybrid_list K u t j s)) -
       f (replace_coordinate j (List.nth j (u t) 0) (hybrid_list K u t j s))))).
    { intros s. rewrite (hybrid_list_replace_same _ _ _ _ _ HjK).
      rewrite (hybrid_list_succ _ _ _ _ _ HjK); ring. }
    apply is_derive_plus; [exact IH|].
    assert (Hval : Df j (u t) * du j =
      Df j (replace_coordinate j (List.nth j (u t) 0) (hybrid_list K u t j t)) * du j).
    { rewrite (hybrid_list_at_t _ _ _ _ (HL t)) replace_coordinate_self; reflexivity. }
    rewrite Hval.
    apply (chain_rule_step
      (fun s y => f (replace_coordinate j y (hybrid_list K u t j s)))
      (fun s x => Df j (replace_coordinate j x (hybrid_list K u t j s)))
      (fun s => List.nth j (u s) 0) t (List.nth j (u t) 0) (du j)).
    + intros s x.
      assert (HLx : List.length (replace_coordinate j x (hybrid_list K u t j s)) = K).
      { rewrite replace_coordinate_length hybrid_list_length; reflexivity. }
      pose proof (HD j HjK _ HLx) as H.
      assert (HjL : (j < List.length (hybrid_list K u t j s))%coq_nat)
        by (rewrite hybrid_list_length; exact HjK).
      rewrite (replace_coordinate_nth_same _ _ _ HjL) in H.
      refine (is_derive_ext _ _ _ _ _ H).
      intros y; rewrite replace_coordinate_twice; reflexivity.
    + intros eps Heps.
      destruct (HC j HjK (coordinates_of_list K (u t)) (mkposreal eps Heps)) as [delta Hdelta].
      destruct (coordinates_uniform_close K u t Hcont delta (cond_pos delta)) as [d1 [Hd1 H1]].
      exists (Rmin d1 delta); split; [apply Rmin_pos; [exact Hd1|apply cond_pos]|].
      intros s x Hs Hx.
      assert (HLx : List.length (replace_coordinate j x (hybrid_list K u t j s)) = K).
      { rewrite replace_coordinate_length hybrid_list_length; reflexivity. }
      specialize (Hdelta (coordinates_of_list K (replace_coordinate j x (hybrid_list K u t j s)))).
      rewrite (coordinates_list_roundtrip _ _ HLx) (coordinates_list_roundtrip _ _ (HL t)) in Hdelta.
      rewrite (hybrid_list_at_t _ _ _ _ (HL t)) replace_coordinate_self.
      apply Hdelta.
      apply coordinates_close_lists; [exact HLx|apply HL|].
      intros i Hi.
      destruct (Nat.eq_dec i j) as [->|Hij].
      * assert (HjL : (j < List.length (hybrid_list K u t j s))%coq_nat)
          by (rewrite hybrid_list_length; exact HjK).
        rewrite (replace_coordinate_nth_same _ _ _ HjL).
        eapply Rlt_le_trans; [exact Hx|apply Rmin_r].
      * rewrite (replace_coordinate_nth_other j i _ _ (not_eq_sym Hij)).
        rewrite (hybrid_list_nth _ _ _ _ _ _ Hi).
        destruct (Nat.ltb i j) eqn:E.
        { apply H1; [eapply Rlt_le_trans; [exact Hs|apply Rmin_l]|exact Hi]. }
        { rewrite Rminus_diag Rabs_R0; apply cond_pos. }
    + exact (Hdu j HjK).
    + reflexivity.
Qed.

Theorem finite_chain_rule K (f : list R -> R) (Df : nat -> list R -> R)
    (u : R -> list R) (du : nat -> R) (t : R) :
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a f (Df a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Df a)) ->
  (forall s, List.length (u s) = K) ->
  (forall a, (a < K)%coq_nat ->
    @is_derive R R^o R^o t 1 (fun s => List.nth a (u s) 0) (du a)) ->
  @is_derive R R^o R^o t 1 (fun s => f (u s))
    (finite_sum (fun a => Df a (u t) * du a) (List.seq 0 K)).
Proof.
  intros HD HC HL Hdu.
  apply (is_derive_ext (fun s => f (hybrid_list K u t K s))).
  - intros s; rewrite (hybrid_list_full _ _ _ _ (HL s)); reflexivity.
  - apply (finite_chain_rule_hybrid K f Df u du t HD HC HL Hdu K (Nat.le_refl K)).
Qed.

(* The coordinate sections of a composite g (Lam zs). *)
Theorem finite_coordinate_derivative_comp d K i (g : list R -> R) (Dg : nat -> list R -> R)
    (Lam : list R -> list R) (DLam : nat -> list R -> R) :
  (forall a, (a < K)%coq_nat -> finite_coordinate_derivative K a g (Dg a)) ->
  (forall a, (a < K)%coq_nat -> finite_joint_continuous K (Dg a)) ->
  (forall zs, List.length zs = d -> List.length (Lam zs) = K) ->
  (forall a, (a < K)%coq_nat ->
    finite_coordinate_derivative d i (fun zs => List.nth a (Lam zs) 0) (DLam a)) ->
  finite_coordinate_derivative d i (fun zs => g (Lam zs))
    (fun zs => finite_sum (fun a => Dg a (Lam zs) * DLam a zs) (List.seq 0 K)).
Proof.
  intros HD HC HL HDL zs Hzs.
  pose proof (finite_chain_rule K g Dg (fun s => Lam (replace_coordinate i s zs))
    (fun a => DLam a zs) (List.nth i zs 0) HD HC) as H.
  rewrite replace_coordinate_self in H.
  apply H.
  - intros s; apply HL; rewrite replace_coordinate_length; exact Hzs.
  - intros a Ha; exact (HDL a Ha zs Hzs).
Qed.
