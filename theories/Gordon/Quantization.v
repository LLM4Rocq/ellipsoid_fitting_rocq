(* Unit vectors admit integer codes with total budget linear in dimension. *)
From Stdlib Require Import Reals List Lia Lra Psatz ZArith.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra Gordon.ProcessCovariance Gordon.Lipschitz
  Gordon.Budget Gordon.SignedGrid.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_ceiling x := Z.to_nat (up x).

Lemma paper_main_gordon_ceiling_bound x :
  0 <= x -> x < INR (paper_main_gordon_ceiling x) <= x+1.
Proof.
intros Hx; destruct (archimed x) as [HL HU].
assert (HZ : (0 <= up x)%Z) by (apply le_IZR; simpl; lra).
unfold paper_main_gordon_ceiling; rewrite INR_IZR_INZ, Z2Nat.id by exact HZ.
split; lra.
Qed.

Lemma paper_main_gordon_quantize_error x h :
  0 < h ->
  Rabs (Rabs x - h * INR (paper_main_gordon_ceiling (Rabs x / h))) <= h.
Proof.
intros Hh.
assert (HQ : 0 <= Rabs x / h) by (unfold Rdiv; apply Rmult_le_pos; [apply Rabs_pos|left; apply Rinv_0_lt_compat; exact Hh]).
destruct (paper_main_gordon_ceiling_bound (Rabs x / h) HQ) as [HL HU].
assert (HE : h*(Rabs x/h) = Rabs x) by (field; lra).
pose proof (Rmult_le_compat_l h _ _ ltac:(lra) HU) as Hupper.
pose proof (Rmult_lt_compat_l h _ _ Hh HL) as Hlower.
apply Rabs_le; nra.
Qed.

Lemma paper_main_gordon_integer_sum (q : nat -> nat) I :
  INR (List.list_sum (List.map q I)) = finite_sum (fun i => INR (q i)) I.
Proof.
induction I as [|i I IH]; [reflexivity|].
simpl; rewrite plus_INR, IH; reflexivity.
Qed.

Lemma paper_main_gordon_unit_l1 d u :
  paper_main_gordon_dot d u u = 1 ->
  finite_sum (fun i => Rabs (u i)) (List.seq 0 d) <= sqrt (INR d).
Proof.
intros HU.
pose proof (paper_main_gordon_sum_cauchy (fun i => Rabs (u i)) (fun _ => 1) (List.seq 0 d)) as HC.
assert (HE : finite_sum (fun i => Rabs (u i)*1) (List.seq 0 d) =
  finite_sum (fun i => Rabs (u i)) (List.seq 0 d)).
{ apply finite_sum_ext; intros; ring. }
assert (HA : finite_sum (fun i => Rabs (u i)^2) (List.seq 0 d) = 1).
{ rewrite <- HU; unfold paper_main_gordon_dot; apply finite_sum_ext; intros i Hi.
  pose proof (Rsqr_abs (u i)) as H; unfold Rsqr in H; nra. }
cbn beta in HC.
rewrite HE, HA, finite_sum_const, length_seq in HC.
pose proof (sqrt_pos (INR d)) as HS.
pose proof (pow2_sqrt (INR d) (pos_INR d)) as HS2.
nra.
Qed.

Lemma paper_main_gordon_quantized_budget d u h :
  0 < h -> paper_main_gordon_dot d u u = 1 ->
  INR (List.list_sum (List.map (fun i =>
    paper_main_gordon_ceiling (Rabs (u i) / h)) (List.seq 0 d))) <=
    sqrt (INR d) / h + INR d.
Proof.
intros Hh HU; rewrite paper_main_gordon_integer_sum.
eapply Rle_trans with (finite_sum (fun i => Rabs (u i)/h + 1) (List.seq 0 d)).
- apply finite_sum_le; intros i Hi; apply paper_main_gordon_ceiling_bound.
  unfold Rdiv; apply Rmult_le_pos; [apply Rabs_pos|left; apply Rinv_0_lt_compat; exact Hh].
- rewrite finite_sum_plus, finite_sum_const, length_seq.
  unfold Rdiv; rewrite finite_sum_scale_r.
  pose proof (paper_main_gordon_unit_l1 d u HU) as HL.
  pose proof (Rinv_0_lt_compat h Hh) as Hinv.
  pose proof (Rmult_le_compat_r (/h) _ _ ltac:(lra) HL); lra.
Qed.

Lemma paper_main_gordon_quantized_cover d u h K :
  0 < h -> paper_main_gordon_dot d u u = 1 ->
  sqrt (INR d) / h + INR d <= INR K ->
  exists xs, List.In xs (paper_main_gordon_signed_grid d K h) /\
    forall i, (i < d)%nat -> Rabs (u i - List.nth i xs 0) <= h.
Proof.
intros Hh HU HK.
set (q := fun i => paper_main_gordon_ceiling (Rabs (u i)/h)).
set (codes := map q (List.seq 0 d)).
assert (HL : length codes = d) by (unfold codes; rewrite length_map, length_seq; reflexivity).
assert (HB : (list_sum codes <= K)%nat).
{ apply INR_le; unfold codes, q.
  pose proof (paper_main_gordon_quantized_budget d u h Hh HU); lra. }
assert (HN : forall i, (i<d)%nat -> nth i codes 0%nat = q i).
{ intros i Hi; unfold codes.
  rewrite (@nth_indep nat (map q (List.seq 0 d)) i 0%nat (q 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi; reflexivity. }
assert (HE : forall i, (i<length codes)%nat -> Rabs (Rabs (u i)-h*INR(nth i codes 0%nat)) <= h).
{ intros i Hi; rewrite HL in Hi; rewrite HN by exact Hi; unfold q.
  apply paper_main_gordon_quantize_error; exact Hh. }
destruct (paper_main_gordon_signs_cover h codes u HE) as [ys [HY HD]].
exists ys; split.
- unfold paper_main_gordon_signed_grid; apply in_flat_map; exists codes; split; [|exact HY].
  apply paper_main_gordon_budget_grid_cover; assumption.
- intros i Hi; apply HD; rewrite HL; exact Hi.
Qed.
