From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import SoftDefinitions.
Import ListNotations.
Open Scope R_scope.

(* Soft maxima and minima compared with true maxima and minima over a
   nonempty finite family. soft_max_bounds: for gamma > 0,
     max f <= soft_max gamma f <= max f + ln |I| / gamma,
   where |I| is the length of the index list I. soft_min_bounds gives the
   mirror bounds for the soft minimum, and soft_minimax_bounds combines
   them:
     minimax H - ln |Y| / beta <= soft_minimax beta gamma H
       <= minimax H + ln |S| / gamma.
   The first lemmas are basic facts on finite sums, finite maxima and
   minima (attained at an index), and monotonicity of exp and ln. *)

Lemma finite_sum_nonnegative (f : nat -> R) I :
  (forall i, In i I -> 0 <= f i) -> 0 <= finite_sum f I.
Proof.
  induction I as [|i I IH]; simpl; intros H.
  - lra.
  - assert (0 <= f i) by (apply H; auto).
    assert (0 <= finite_sum f I) by (apply IH; intros; apply H; auto).
    lra.
Qed.


Lemma finite_sum_upper (f : nat -> R) I M :
  (forall i, In i I -> f i <= M) ->
  finite_sum f I <= INR (length I) * M.
Proof.
  induction I as [|i I IH]; intros H.
  - simpl; lra.
  - simpl finite_sum; simpl length; rewrite S_INR.
    assert (f i <= M) by (apply H; simpl; auto).
    assert (finite_sum f I <= INR (length I) * M).
    { apply IH; intros; apply H; simpl; auto. }
    nra.
Qed.

Lemma finite_sum_member (f : nat -> R) I i :
  (forall j, In j I -> 0 <= f j) -> In i I -> f i <= finite_sum f I.
Proof.
  induction I as [|j I IH]; simpl; intros H Hi.
  - contradiction.
  - assert (Hj : 0 <= f j) by (apply H; auto).
    assert (HI : forall k, In k I -> 0 <= f k) by (intros; apply H; auto).
    destruct Hi as [<-|Hi].
    + pose proof (finite_sum_nonnegative f I HI); lra.
    + specialize (IH HI Hi); lra.
Qed.

Lemma finite_max_member (f : nat -> R) I i :
  In i I -> f i <= finite_max f I.
Proof.
  induction I as [|j I IH]; intros H.
  - contradiction.
  - destruct I as [|k I].
    + simpl in *; destruct H as [<-|H]; [lra|contradiction].
    + change (f i <= Rmax (f j) (finite_max f (k :: I))).
      destruct H as [<-|H].
      * apply Rmax_l.
      * eapply Rle_trans; [apply IH; exact H|apply Rmax_r].
Qed.

Lemma finite_max_upper (f : nat -> R) I M :
  I <> [] -> (forall i, In i I -> f i <= M) -> finite_max f I <= M.
Proof.
  induction I as [|i I IH]; intros Hne H.
  - contradiction.
  - destruct I as [|j I].
    + apply H; simpl; auto.
    + change (Rmax (f i) (finite_max f (j :: I)) <= M).
      apply Rmax_case.
      * apply H; simpl; auto.
      * apply IH; [discriminate|intros; apply H; simpl; auto].
Qed.

Lemma finite_max_attained (f : nat -> R) I :
  I <> [] -> exists i, In i I /\ finite_max f I = f i.
Proof.
  induction I as [|i I IH]; intros Hne.
  - contradiction.
  - destruct I as [|j I].
    + exists i; simpl; auto.
    + destruct (IH ltac:(discriminate)) as [k [Hk Heq]].
      change (exists k, In k (i :: j :: I) /\
        Rmax (f i) (finite_max f (j :: I)) = f k).
      apply Rmax_case.
      * exists i; simpl; auto.
      * exists k; split; [right; exact Hk|exact Heq].
Qed.

Lemma exp_monotone x y : x <= y -> exp x <= exp y.
Proof.
  intros H; destruct (Rle_lt_or_eq x y H) as [Hlt | Heq].
  - pose proof (exp_increasing x y Hlt); lra.
  - subst y; lra.
Qed.

Lemma ln_monotone x y : 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros Hx H; destruct (Rle_lt_or_eq x y H) as [Hlt | Heq].
  - pose proof (ln_increasing x y Hx Hlt); lra.
  - subst y; lra.
Qed.

Lemma soft_max_bounds gamma f I :
  0 < gamma -> I <> [] ->
  finite_max f I <= soft_max gamma f I /\
  soft_max gamma f I <= finite_max f I + ln (INR (length I)) / gamma.
Proof.
  intros Hg HI.
  set (M := finite_max f I).
  set (Z := finite_sum (fun i => exp (gamma * f i)) I).
  assert (HN : 0 < INR (length I)).
  { apply lt_0_INR; destruct I; [contradiction|simpl; lia]. }
  assert (Hexp : 0 < exp (gamma * M)) by apply exp_pos.
  assert (Hlower : exp (gamma * M) <= Z).
  { destruct (finite_max_attained f I HI) as [i [Hi Heq]].
    unfold M; rewrite Heq; unfold Z.
    apply (finite_sum_member (fun j => exp (gamma * f j)) I i);
      [intros; left; apply exp_pos|exact Hi]. }
  assert (HZ : 0 < Z) by lra.
  assert (Hupper : Z <= INR (length I) * exp (gamma * M)).
  { apply finite_sum_upper; intros i Hi.
    apply exp_monotone, Rmult_le_compat_l; [lra|].
    apply finite_max_member; exact Hi. }
  assert (HL : gamma * M <= ln Z).
  { rewrite <- (ln_exp (gamma * M)); apply ln_monotone; assumption. }
  assert (HU : ln Z <= ln (INR (length I)) + gamma * M).
  { pose proof (ln_monotone Z (INR (length I) * exp (gamma * M)) HZ Hupper) as H.
    rewrite ln_mult in H by assumption.
    rewrite ln_exp in H; exact H. }
  assert (Hcancel : forall a : R, a / gamma * gamma = a).
  { intros; field; lra. }
  change (M <= ln Z / gamma /\ ln Z / gamma <= M + ln (INR (length I)) / gamma).
  split; apply (Rmult_le_reg_r gamma); try exact Hg.
  - rewrite Hcancel; nra.
  - rewrite Rmult_plus_distr_r, !Hcancel; nra.
Qed.

Lemma soft_min_bounds beta f I :
  0 < beta -> I <> [] ->
  finite_min f I - ln (INR (length I)) / beta <= soft_min beta f I /\
  soft_min beta f I <= finite_min f I.
Proof.
  intros Hb HI.
  pose proof (soft_max_bounds beta (fun i => - f i) I Hb HI).
  unfold finite_min, soft_min; lra.
Qed.

Lemma finite_min_member (f : nat -> R) I i :
  In i I -> finite_min f I <= f i.
Proof.
  intros Hi; pose proof (finite_max_member (fun j => - f j) I i Hi).
  unfold finite_min; lra.
Qed.

Lemma finite_min_lower (f : nat -> R) I m :
  I <> [] -> (forall i, In i I -> m <= f i) -> m <= finite_min f I.
Proof.
  intros HI H.
  assert (finite_max (fun i => - f i) I <= - m).
  { apply finite_max_upper; [exact HI|intros i Hi; specialize (H i Hi); lra]. }
  unfold finite_min; lra.
Qed.

Lemma finite_min_attained (f : nat -> R) I :
  I <> [] -> exists i, In i I /\ finite_min f I = f i.
Proof.
  intros HI.
  destruct (finite_max_attained (fun i => - f i) I HI) as [i [Hi Heq]].
  exists i; split; [exact Hi|unfold finite_min; rewrite Heq; lra].
Qed.

Theorem soft_minimax_bounds beta gamma H Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  finite_minimax H Y S - ln (INR (length Y)) / beta <=
    soft_minimax beta gamma H Y S /\
  soft_minimax beta gamma H Y S <=
    finite_minimax H Y S + ln (INR (length S)) / gamma.
Proof.
  intros Hb Hg HY HS.
  pose proof (soft_min_bounds beta (fun y => soft_max gamma (H y) S) Y Hb HY) as [HL HU].
  assert (HM : finite_minimax H Y S <=
    finite_min (fun y => soft_max gamma (H y) S) Y).
  { apply finite_min_lower; [exact HY|intros y Hy].
    pose proof (finite_min_member (fun y => finite_max (H y) S) Y y Hy).
    pose proof (soft_max_bounds gamma (H y) S Hg HS).
    unfold finite_minimax; lra. }
  destruct (finite_min_attained (fun y => finite_max (H y) S) Y HY)
    as [y [Hy Heq]].
  pose proof (finite_min_member (fun y => soft_max gamma (H y) S) Y y Hy) as HF.
  pose proof (soft_max_bounds gamma (H y) S Hg HS) as [_ Hrow].
  unfold finite_minimax in *; unfold soft_minimax; lra.
Qed.
