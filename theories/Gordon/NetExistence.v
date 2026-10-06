(* Qualitative finite nets inside arbitrary nonempty unit-sphere subsets.
   This module does not prove a packing-cardinality or measurable-selector bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon Classical_Prop.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.Cover Gordon.Nets.
From EllipsoidFitting Require Import Gordon.Width Gordon.SetWidth.
Import ListNotations.
Open Scope R_scope.

Fixpoint paper_main_gordon_grid d (centers : list R) : list (list R) :=
  match d with
  | O => [[]]
  | S n => List.flat_map (fun c => List.map (cons c) (paper_main_gordon_grid n centers)) centers
  end.

Lemma paper_main_gordon_grid_cover d centers delta :
  (forall x, -1 <= x <= 1 -> exists c, List.In c centers /\ Rabs (x-c) < delta) ->
  forall u : nat -> R, (forall i, (i < d)%nat -> Rabs (u i) <= 1) ->
  exists xs, List.In xs (paper_main_gordon_grid d centers) /\
    forall i, (i < d)%nat -> Rabs (u i - List.nth i xs 0) < delta.
Proof.
intros Hcover; induction d as [|d IH]; intros u Hu.
- exists []; split; [simpl; auto|intros i Hi; lia].
- assert (H0 : -1 <= u 0%nat <= 1).
  { pose proof (Hu 0%nat ltac:(lia)) as H.
    pose proof (Rle_abs (u 0%nat)); pose proof (Rle_abs (-u 0%nat)) as Hneg.
    rewrite Rabs_Ropp in Hneg; lra. }
  destruct (Hcover (u 0%nat) H0) as [c [Hc HC]].
  destruct (IH (fun i => u (S i)) ltac:(intros i Hi; apply Hu; lia)) as [xs [Hxs HD]].
  exists (c::xs); split.
  + simpl; apply in_flat_map; exists c; split; [exact Hc|].
    apply in_map; exact Hxs.
  + intros [|i] Hi; simpl; [exact HC|apply HD; lia].
Qed.

Lemma paper_main_gordon_unit_coordinate d u i :
  paper_main_gordon_dot d u u = 1 -> (i < d)%nat -> Rabs (u i) <= 1.
Proof.
intros Hu Hi.
pose proof (finite_sum_member (fun j => u j * u j) (List.seq 0 d) i
  ltac:(intros; nra) (lt_in_seq i d Hi)) as HB.
change (u i * u i <= paper_main_gordon_dot d u u) in HB; rewrite Hu in HB.
pose proof (Rsqr_abs (u i)) as HE; unfold Rsqr in HE.
pose proof (Rabs_pos (u i)); nra.
Qed.

Lemma paper_main_gordon_coordinate_square_bound d u B :
  0 <= B -> (forall i, (i < d)%nat -> Rabs (u i) <= B) ->
  paper_main_gordon_dot d u u <= INR d * B^2.
Proof.
intros HB Hu; unfold paper_main_gordon_dot.
replace (INR d * B^2) with (finite_sum (fun _ => B^2) (List.seq 0 d))
  by (rewrite finite_sum_const, length_seq; reflexivity).
apply finite_sum_le; intros i Hi.
pose proof (Hu i (in_seq_lt i d Hi)) as H.
pose proof (Rsqr_abs (u i)) as HE; unfold Rsqr in HE.
pose proof (Rabs_pos (u i)); nra.
Qed.

Theorem paper_main_gordon_finite_net_exists d T eps :
  0 < eps -> (exists u, T u) -> (forall u, T u -> paper_main_gordon_dot d u u = 1) ->
  exists s v, (0 < s)%nat /\ paper_main_gordon_finite_net d T v (List.seq 0 s) eps.
Proof.
intros He [u0 Hu0] HU.
set (a := sqrt (INR d)).
assert (Ha : 0 <= a) by (unfold a; apply sqrt_pos).
assert (Ha2 : a^2 = INR d) by (unfold a; apply pow2_sqrt, pos_INR).
set (delta := eps / (2*(a+1))).
assert (Hd : 0 < delta) by (unfold delta; apply Rdiv_lt_0_compat; lra).
assert (Hde : 2*(a+1)*delta = eps) by (unfold delta; field; lra).
destruct (paper_main_gordon_interval_cover delta Hd) as [centers Hcover].
set (C := paper_main_gordon_grid d centers).
set (near := fun (xs : list R) (u : nat -> R) =>
  forall i, (i < d)%nat -> Rabs (u i - List.nth i xs 0) < delta).
assert (HC : forall u, T u -> exists xs, List.In xs C /\ near xs u).
{ intros u Hu; unfold C, near; apply paper_main_gordon_grid_cover; [exact Hcover|].
  intros i Hi; apply (paper_main_gordon_unit_coordinate d u i); [apply HU; exact Hu|exact Hi]. }
set (pick := fun xs : list R => epsilon (inhabits u0)
  (fun u => T u /\ ((exists w, T w /\ near xs w) -> near xs u))).
assert (HP : forall xs, T (pick xs) /\ ((exists w, T w /\ near xs w) -> near xs (pick xs))).
{ intros xs; unfold pick; apply epsilon_spec.
  destruct (classic (exists w, T w /\ near xs w)) as [[w [Hw Hnear]]|Hnone].
  - exists w; auto.
  - exists u0; split; [exact Hu0|intros H; contradiction]. }
assert (HS : (0 < List.length C)%nat).
{ destruct (HC u0 Hu0) as [xs [Hxs _]]; destruct C; [contradiction|simpl; lia]. }
exists (List.length C), (fun t => pick (List.nth t C [])); split; [exact HS|].
split.
- intros t Ht; apply HP.
- intros u Hu; destruct (HC u Hu) as [xs [Hxs Hnear]].
  destruct (In_nth C xs [] Hxs) as [t [Ht HE]].
  exists t; split; [apply lt_in_seq; exact Ht|].
  rewrite HE.
  assert (HPnear : near xs (pick xs)).
  { apply (proj2 (HP xs)); exists u; auto. }
  eapply Rle_trans.
  + apply (paper_main_gordon_coordinate_square_bound d _ (2*delta)); [lra|].
    intros i Hi.
    pose proof (Hnear i Hi) as H1; pose proof (HPnear i Hi) as H2.
    replace (u i - pick xs i) with ((u i - List.nth i xs 0) + (List.nth i xs 0 - pick xs i)) by ring.
    pose proof (Rabs_triang (u i - List.nth i xs 0) (List.nth i xs 0 - pick xs i)) as H3.
    rewrite Rabs_minus_sym in H2; lra.
  + nra.
Qed.
