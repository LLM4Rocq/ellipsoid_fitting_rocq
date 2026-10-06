(* The genuine rectangular operator norm and its finite-net reduction. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Gordon.ProcessCovariance Gordon.Scalar Gaussian.Lipschitz.EuclideanNorm
  Gordon.Bilinear Gordon.NetToAll Gordon.Nets Gordon.Entropy.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_operator_values N M xs a :=
  exists u v, paper_main_gordon_dot N u u <= 1 /\
    paper_main_gordon_dot M v v <= 1 /\
    a = Rabs (paper_main_gordon_matrix_value N M u v xs).

Definition paper_main_gordon_operator_norm N M xs :=
  epsilon (inhabits 0) (fun b => is_lub (paper_main_gordon_operator_values N M xs) b).

Lemma paper_main_gordon_dot_zero d :
  paper_main_gordon_dot d (fun _ => 0) (fun _ => 0) = 0.
Proof.
unfold paper_main_gordon_dot.
transitivity (finite_sum (fun _ => 0) (List.seq 0 d)).
- apply finite_sum_ext; intros; ring.
- apply finite_sum_zero.
Qed.

Lemma paper_main_gordon_operator_values_nonempty N M xs :
  exists a, paper_main_gordon_operator_values N M xs a.
Proof.
exists (Rabs (paper_main_gordon_matrix_value N M (fun _ => 0) (fun _ => 0) xs)).
exists (fun _ => 0), (fun _ => 0); rewrite !paper_main_gordon_dot_zero; repeat split; lra.
Qed.

Lemma paper_main_gordon_operator_norm_lub N M xs :
  List.length xs = (N*M)%nat ->
  is_lub (paper_main_gordon_operator_values N M xs) (paper_main_gordon_operator_norm N M xs).
Proof.
intros Hxs; unfold paper_main_gordon_operator_norm; apply epsilon_spec.
assert (HB : bound (paper_main_gordon_operator_values N M xs)).
{ exists (paper_main_gaussian_norm xs); intros a [u [v [Hu [Hv ->]]]].
  pose proof (paper_main_gordon_bilinear_ball_bound N M xs (paper_main_gaussian_norm xs) u v 1 1
    (paper_main_gordon_operator_frobenius N M xs Hxs) ltac:(lra) ltac:(lra) ltac:(nra) ltac:(nra)) as H; nra. }
destruct (completeness _ HB (paper_main_gordon_operator_values_nonempty N M xs)) as [b Hb].
exists b; exact Hb.
Qed.

Lemma paper_main_gordon_operator_norm_nonnegative N M xs :
  List.length xs = (N*M)%nat -> 0 <= paper_main_gordon_operator_norm N M xs.
Proof.
intros Hxs.
destruct (paper_main_gordon_operator_values_nonempty N M xs) as [a HA].
pose proof (proj1 (paper_main_gordon_operator_norm_lub N M xs Hxs) a HA) as HB.
destruct HA as [u [v [Hu [Hv ->]]]].
pose proof (Rabs_pos (paper_main_gordon_matrix_value N M u v xs)); lra.
Qed.

Lemma paper_main_gordon_operator_norm_bound N M xs :
  List.length xs = (N*M)%nat ->
  paper_main_gordon_operator_bound N M xs (paper_main_gordon_operator_norm N M xs).
Proof.
intros Hxs; apply paper_main_gordon_operator_from_units; [exact Hxs|apply paper_main_gordon_operator_norm_nonnegative; exact Hxs|].
intros u v Hu Hv; apply (proj1 (paper_main_gordon_operator_norm_lub N M xs Hxs)).
exists u, v; rewrite Hu, Hv; repeat split; lra.
Qed.

Lemma paper_main_gordon_operator_norm_le N M xs L :
  List.length xs = (N*M)%nat ->
  paper_main_gordon_operator_bound N M xs L -> paper_main_gordon_operator_norm N M xs <= L.
Proof.
intros Hxs HL.
apply (proj2 (paper_main_gordon_operator_norm_lub N M xs Hxs)).
intros a [u [v [Hu [Hv ->]]]].
pose proof (paper_main_gordon_bilinear_ball_bound N M xs L u v 1 1 HL
  ltac:(lra) ltac:(lra) ltac:(nra) ltac:(nra)) as H; nra.
Qed.

Lemma paper_main_gordon_operator_norm_characterization N M xs L :
  List.length xs = (N*M)%nat ->
  (paper_main_gordon_operator_bound N M xs L <-> paper_main_gordon_operator_norm N M xs <= L).
Proof.
intros Hxs; split; [apply paper_main_gordon_operator_norm_le; exact Hxs|].
intros HL; apply paper_main_gordon_operator_from_units; [exact Hxs| |].
- pose proof (paper_main_gordon_operator_norm_nonnegative N M xs Hxs); lra.
- intros u v Hu Hv; eapply Rle_trans; [|exact HL].
  apply (proj1 (paper_main_gordon_operator_norm_lub N M xs Hxs)).
  exists u, v; rewrite Hu, Hv; repeat split; lra.
Qed.

Lemma paper_main_gordon_bilinear_two_net_error N M xs L u u' v v' eps :
  paper_main_gordon_operator_bound N M xs L -> 0 <= eps ->
  paper_main_gordon_dot N u' u' = 1 -> paper_main_gordon_dot M v v = 1 ->
  paper_main_gordon_dot N (fun i => u i-u' i) (fun i => u i-u' i) <= eps^2 ->
  paper_main_gordon_dot M (fun i => v i-v' i) (fun i => v i-v' i) <= eps^2 ->
  Rabs (paper_main_gordon_matrix_value N M u v xs -
    paper_main_gordon_matrix_value N M u' v' xs) <= 2*eps*L.
Proof.
intros HL He Hu Hv Hdu Hdv.
pose proof (paper_main_gordon_bilinear_left_error N M xs L u u' v eps 1
  HL He ltac:(lra) Hdu ltac:(rewrite Hv; lra)) as H1.
pose proof (paper_main_gordon_bilinear_right_error N M xs L u' v v' 1 eps
  HL ltac:(lra) He ltac:(rewrite Hu; lra) Hdv) as H2.
replace (paper_main_gordon_matrix_value N M u v xs - paper_main_gordon_matrix_value N M u' v' xs)
  with ((paper_main_gordon_matrix_value N M u v xs-paper_main_gordon_matrix_value N M u' v xs)+
    (paper_main_gordon_matrix_value N M u' v xs-paper_main_gordon_matrix_value N M u' v' xs)) by ring.
eapply Rle_trans; [apply Rabs_triang|nra].
Qed.

Theorem paper_main_gordon_operator_net_bound r s N M z v xs eps B :
  List.length xs = (N*M)%nat -> 0 <= eps -> eps < 1/2 -> 0 <= B ->
  paper_main_gordon_finite_net N (fun u => paper_main_gordon_dot N u u = 1) z (List.seq 0 r) eps ->
  paper_main_gordon_finite_net M (fun w => paper_main_gordon_dot M w w = 1) v (List.seq 0 s) eps ->
  (forall y t, (y < r)%nat -> (t < s)%nat ->
    Rabs (paper_main_gordon_matrix_value N M (z y) (v t) xs) <= B) ->
  paper_main_gordon_operator_norm N M xs <= B/(1-2*eps).
Proof.
intros Hxs He Hehalf HB HnetZ HnetV Hsamples.
set (L := paper_main_gordon_operator_norm N M xs).
assert (HL : paper_main_gordon_operator_bound N M xs L)
  by (apply paper_main_gordon_operator_norm_bound; exact Hxs).
assert (HLp : 0 <= L) by exact (proj1 HL).
assert (HU : forall u w, paper_main_gordon_dot N u u = 1 -> paper_main_gordon_dot M w w = 1 ->
  Rabs (paper_main_gordon_matrix_value N M u w xs) <= B+2*eps*L).
{ intros u w Hu Hw.
  destruct (proj2 HnetZ u Hu) as [y [Hy Hdu]].
  destruct (proj2 HnetV w Hw) as [t [Ht Hdv]].
  assert (Hzy : paper_main_gordon_dot N (z y) (z y) = 1) by (apply (proj1 HnetZ); exact Hy).
  pose proof (paper_main_gordon_bilinear_two_net_error N M xs L u (z y) w (v t) eps
    HL He Hzy Hw Hdu Hdv) as HE.
  pose proof (Hsamples y t (in_seq_lt y r Hy) (in_seq_lt t s Ht)) as Hsample.
  replace (paper_main_gordon_matrix_value N M u w xs) with
    ((paper_main_gordon_matrix_value N M u w xs-paper_main_gordon_matrix_value N M (z y) (v t) xs)+
      paper_main_gordon_matrix_value N M (z y) (v t) xs) by ring.
  eapply Rle_trans; [apply Rabs_triang|lra]. }
assert (Hnew : paper_main_gordon_operator_bound N M xs (B+2*eps*L)).
{ apply paper_main_gordon_operator_from_units; [exact Hxs|nra|exact HU]. }
pose proof (paper_main_gordon_operator_norm_le N M xs (B+2*eps*L) Hxs Hnew) as HN; fold L in HN |- *.
assert (HD : 0 < 1-2*eps) by lra.
apply (Rmult_le_reg_r (1-2*eps)); [exact HD|].
replace (B/(1-2*eps)*(1-2*eps)) with B by (field; lra).
nra.
Qed.

Lemma paper_main_gordon_unit_sphere_nonempty d :
  (0 < d)%nat -> exists u, paper_main_gordon_dot d u u = 1.
Proof.
destruct d as [|d]; intros Hd; [lia|].
exists (fun i => if Nat.eq_dec i 0 then 1 else 0); unfold paper_main_gordon_dot.
change (1*1 + finite_sum (fun i => (if Nat.eq_dec i 0 then 1 else 0)*
  (if Nat.eq_dec i 0 then 1 else 0)) (List.seq 1 d) = 1).
assert (HE : finite_sum (fun i => (if Nat.eq_dec i 0 then 1 else 0)*
  (if Nat.eq_dec i 0 then 1 else 0)) (List.seq 1 d) = 0).
{ transitivity (finite_sum (fun _ => 0) (List.seq 1 d)); [|apply finite_sum_zero].
  apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
  destruct (Nat.eq_dec i 0); [lia|ring]. }
rewrite HE; ring.
Qed.

Theorem paper_main_gordon_operator_discretization N M :
  (0 < N)%nat -> (0 < M)%nat ->
  exists r s z v, (0 < r)%nat /\ (0 < s)%nat /\
    (forall y, (y < r)%nat -> paper_main_gordon_dot N (z y) (z y) = 1) /\
    (forall t, (t < s)%nat -> paper_main_gordon_dot M (v t) (v t) = 1) /\
    ln (INR r) + ln (INR s) <=
      paper_main_gordon_entropy_constant (1/4) * (INR N + INR M) /\
    forall xs B, List.length xs = (N*M)%nat -> 0 <= B ->
      (forall y t, (y < r)%nat -> (t < s)%nat ->
        Rabs (paper_main_gordon_matrix_value N M (z y) (v t) xs) <= B) ->
      paper_main_gordon_operator_norm N M xs <= 2*B.
Proof.
intros HN HM.
set (Y := fun u => paper_main_gordon_dot N u u = 1).
set (T := fun w => paper_main_gordon_dot M w w = 1).
assert (HY : exists u, Y u) by (apply paper_main_gordon_unit_sphere_nonempty; exact HN).
assert (HT : exists w, T w) by (apply paper_main_gordon_unit_sphere_nonempty; exact HM).
destruct (paper_main_gordon_entropy_net N Y (1/4) ltac:(lra) HY ltac:(intros; assumption))
  as [r [z [Hr [HnetZ HrE]]]].
destruct (paper_main_gordon_entropy_net M T (1/4) ltac:(lra) HT ltac:(intros; assumption))
  as [s [v [Hs [HnetV HsE]]]].
exists r, s, z, v; split; [exact Hr|]; split; [exact Hs|]; split.
- intros y Hy; apply (proj1 HnetZ); apply lt_in_seq; exact Hy.
- split.
  + intros t Ht; apply (proj1 HnetV); apply lt_in_seq; exact Ht.
  + split; [nra|].
    intros xs B Hxs HB Hsamples.
    pose proof (paper_main_gordon_operator_net_bound r s N M z v xs (1/4) B
      Hxs ltac:(lra) ltac:(lra) HB HnetZ HnetV Hsamples) as H.
    replace (B/(1-2*(1/4))) with (2*B) in H by field; exact H.
Qed.
