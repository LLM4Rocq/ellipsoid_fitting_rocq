(* Quantitative finite nets: logarithmic size linear in ambient dimension.
   The indexed family may contain repetitions. No measurable selection in
   a parameter is asserted. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon Classical_Prop.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.NetExistence
  Gordon.Nets Gordon.Quantization Gordon.SignedGrid.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_mesh d eps := eps / (2 * (sqrt (INR d) + 1)).
Definition paper_main_gordon_entropy_budget d eps :=
  paper_main_gordon_ceiling (INR d * (1 + 4/eps)).
Definition paper_main_gordon_entropy_constant eps := (4 + 4/eps) * ln 2.
Definition paper_main_gordon_entropy_grid d eps :=
  paper_main_gordon_signed_grid d (paper_main_gordon_entropy_budget d eps)
    (paper_main_gordon_mesh d eps).

Lemma paper_main_gordon_unit_dimension d u :
  paper_main_gordon_dot d u u = 1 -> (0 < d)%nat.
Proof.
destruct d as [|d]; [unfold paper_main_gordon_dot; simpl; lra|lia].
Qed.

Lemma paper_main_gordon_mesh_positive d eps :
  0 < eps -> 0 < paper_main_gordon_mesh d eps.
Proof.
intros He; unfold paper_main_gordon_mesh; apply Rdiv_lt_0_compat; [exact He|].
pose proof (sqrt_pos (INR d)); lra.
Qed.

Lemma paper_main_gordon_mesh_budget d eps :
  (0 < d)%nat -> 0 < eps ->
  sqrt (INR d) / paper_main_gordon_mesh d eps + INR d <=
    INR (paper_main_gordon_entropy_budget d eps).
Proof.
intros Hd He.
assert (HdR : 1 <= INR d) by (change (INR 1 <= INR d); apply le_INR; lia).
set (a := sqrt (INR d)).
assert (Ha : 0 <= a) by (unfold a; apply sqrt_pos).
assert (Ha2 : a^2 = INR d) by (unfold a; apply pow2_sqrt, pos_INR).
assert (Had : a <= INR d) by nra.
assert (Hinv : 0 < /eps) by (apply Rinv_0_lt_compat; exact He).
assert (Hq : 0 <= INR d * (1+4/eps)) by (unfold Rdiv; nra).
pose proof (proj1 (paper_main_gordon_ceiling_bound (INR d*(1+4/eps)) Hq)) as HK.
unfold paper_main_gordon_entropy_budget.
assert (HE : a / paper_main_gordon_mesh d eps = (2*(INR d+a))/eps).
{ unfold paper_main_gordon_mesh; fold a.
  replace (INR d) with (a*a) by nra; field; lra. }
rewrite HE; unfold Rdiv in *; nra.
Qed.

Lemma paper_main_gordon_entropy_grid_cover d eps u :
  0 < eps -> paper_main_gordon_dot d u u = 1 ->
  exists xs, List.In xs (paper_main_gordon_entropy_grid d eps) /\
    forall i, (i < d)%nat ->
      Rabs (u i - List.nth i xs 0) <= paper_main_gordon_mesh d eps.
Proof.
intros He HU; unfold paper_main_gordon_entropy_grid.
apply paper_main_gordon_quantized_cover; [apply paper_main_gordon_mesh_positive; exact He|exact HU|].
apply paper_main_gordon_mesh_budget; [apply (paper_main_gordon_unit_dimension d u); exact HU|exact He].
Qed.

Lemma paper_main_gordon_entropy_cardinality d eps s :
  (0 < d)%nat -> 0 < eps -> (0 < s)%nat ->
  (s <= List.length (paper_main_gordon_entropy_grid d eps))%nat ->
  ln (INR s) <= paper_main_gordon_entropy_constant eps * INR d.
Proof.
intros Hd He Hs Hsize.
set (K := paper_main_gordon_entropy_budget d eps).
assert (HB : (s <= 2^(2*d+K))%nat).
{ eapply Nat.le_trans; [exact Hsize|]; unfold paper_main_gordon_entropy_grid, K.
  apply paper_main_gordon_signed_grid_cardinality. }
assert (HsR : 0 < INR s) by (apply lt_0_INR; exact Hs).
assert (Hpow : INR s <= 2^(2*d+K)).
{ pose proof (le_INR _ _ HB) as H; rewrite pow_INR in H; exact H. }
assert (HL : ln (INR s) <= INR (2*d+K) * ln 2).
{ rewrite <- ln_pow by lra.
  destruct (Rle_lt_or_eq_dec _ _ Hpow) as [Hlt|HE].
  - left; apply ln_increasing; assumption.
  - rewrite HE; reflexivity. }
assert (HdR : 1 <= INR d) by (change (INR 1 <= INR d); apply le_INR; lia).
assert (Hinv : 0 < /eps) by (apply Rinv_0_lt_compat; exact He).
assert (Hq : 0 <= INR d*(1+4/eps)) by (unfold Rdiv; nra).
pose proof (proj2 (paper_main_gordon_ceiling_bound (INR d*(1+4/eps)) Hq)) as HK.
change (INR K <= INR d*(1+4/eps)+1) in HK.
assert (Hln : 0 < ln 2).
{ pose proof (ln_increasing 1 2 ltac:(lra) ltac:(lra)) as H; rewrite ln_1 in H; exact H. }
rewrite plus_INR, mult_INR in HL; change (INR 2) with 2 in HL.
unfold paper_main_gordon_entropy_constant; nra.
Qed.

Theorem paper_main_gordon_entropy_net_fixed d T eps :
  0 < eps -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  let s := List.length (paper_main_gordon_entropy_grid d eps) in
  (0 < s)%nat /\ exists v,
    paper_main_gordon_finite_net d T v (List.seq 0 s) eps /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR d.
Proof.
intros He [u0 Hu0] HU.
set (a := sqrt (INR d)).
assert (Ha : 0 <= a) by (unfold a; apply sqrt_pos).
assert (Ha2 : a^2 = INR d) by (unfold a; apply pow2_sqrt, pos_INR).
set (delta := paper_main_gordon_mesh d eps).
assert (Hd : 0 < delta) by (apply paper_main_gordon_mesh_positive; exact He).
assert (Hde : 2*(a+1)*delta = eps) by (unfold delta, paper_main_gordon_mesh, a; field; pose proof (sqrt_pos (INR d)); lra).
set (C := paper_main_gordon_entropy_grid d eps).
set (near := fun (xs : list R) (u : nat -> R) =>
  forall i, (i < d)%nat -> Rabs (u i - List.nth i xs 0) <= delta).
assert (HC : forall u, T u -> exists xs, List.In xs C /\ near xs u).
{ intros u Hu; unfold C, near, delta; apply paper_main_gordon_entropy_grid_cover; [exact He|apply HU; exact Hu]. }
set (pick := fun xs : list R => epsilon (inhabits u0)
  (fun u => T u /\ ((exists w, T w /\ near xs w) -> near xs u))).
assert (HP : forall xs, T (pick xs) /\ ((exists w, T w /\ near xs w) -> near xs (pick xs))).
{ intros xs; unfold pick; apply epsilon_spec.
  destruct (classic (exists w, T w /\ near xs w)) as [[w [Hw Hnear]]|Hnone].
  - exists w; auto.
  - exists u0; split; [exact Hu0|intros H; contradiction]. }
assert (HS : (0 < List.length C)%nat).
{ destruct (HC u0 Hu0) as [xs [Hxs _]]; destruct C; [contradiction|simpl; lia]. }
split; [exact HS|].
exists (fun t => pick (List.nth t C [])); split.
- split.
  + intros t Ht; apply HP.
  + intros u Hu; destruct (HC u Hu) as [xs [Hxs Hnear]].
    destruct (In_nth C xs [] Hxs) as [t [Ht HE]].
    exists t; split; [apply lt_in_seq; exact Ht|].
    rewrite HE.
    assert (HPnear : near xs (pick xs)).
    { apply (proj2 (HP xs)); exists u; auto. }
    eapply Rle_trans.
    * apply (paper_main_gordon_coordinate_square_bound d _ (2*delta)); [lra|].
      intros i Hi.
      pose proof (Hnear i Hi) as H1; pose proof (HPnear i Hi) as H2.
      replace (u i - pick xs i) with ((u i - List.nth i xs 0) + (List.nth i xs 0 - pick xs i)) by ring.
      pose proof (Rabs_triang (u i - List.nth i xs 0) (List.nth i xs 0 - pick xs i)) as H3.
      rewrite Rabs_minus_sym in H2; lra.
    * nra.
- apply paper_main_gordon_entropy_cardinality; [|exact He|exact HS|unfold C; lia].
  apply (paper_main_gordon_unit_dimension d u0); apply HU; exact Hu0.
Qed.

Theorem paper_main_gordon_entropy_net d T eps :
  0 < eps -> (exists u, T u) ->
  (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  exists s v, (0 < s)%nat /\
    paper_main_gordon_finite_net d T v (List.seq 0 s) eps /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR d.
Proof.
intros He HT HU.
destruct (paper_main_gordon_entropy_net_fixed d T eps He HT HU) as [Hs [v [HN HL]]].
exists (List.length (paper_main_gordon_entropy_grid d eps)), v; auto.
Qed.
