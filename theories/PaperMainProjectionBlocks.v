(* Disjoint blocks for independent quadratic and Gaussian coordinates. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianCovarianceLinear PaperMainProjectionStein PaperMainProjectionAlgebra.
Open Scope R_scope.

Definition paper_main_projection_left p (A : nat -> nat -> R) i j :=
  if Nat.ltb i p then if Nat.ltb j p then A i j else 0 else 0.
Definition paper_main_projection_right p (c : nat -> R) i :=
  if Nat.ltb i p then 0 else c (i-p)%coq_nat.

Lemma paper_main_projection_left_inside p A i j : (i<p)%coq_nat -> (j<p)%coq_nat ->
  paper_main_projection_left p A i j=A i j.
Proof.
intros Hi Hj; unfold paper_main_projection_left;
  rewrite (proj2(Nat.ltb_lt i p) Hi) (proj2(Nat.ltb_lt j p) Hj); reflexivity.
Qed.
Lemma paper_main_projection_left_outside p A i j : (p<=i)%coq_nat \/ (p<=j)%coq_nat ->
  paper_main_projection_left p A i j=0.
Proof.
intros [Hi|Hj]; unfold paper_main_projection_left.
- rewrite (proj2(Nat.ltb_ge i p) Hi); reflexivity.
- rewrite (proj2(Nat.ltb_ge j p) Hj); destruct(Nat.ltb i p); reflexivity.
Qed.
Lemma paper_main_projection_right_inside p c i : (i<p)%coq_nat ->
  paper_main_projection_right p c i=0.
Proof. intro Hi; unfold paper_main_projection_right; rewrite (proj2(Nat.ltb_lt i p) Hi); reflexivity. Qed.
Lemma paper_main_projection_right_shift p c i :
  paper_main_projection_right p c ((Nat.add p i))%coq_nat=c i.
Proof.
unfold paper_main_projection_right; rewrite (proj2(Nat.ltb_ge ((Nat.add p i))%coq_nat p) ltac:(lia)).
f_equal; lia.
Qed.

Lemma paper_main_projection_sum_prefix p q f g :
  (forall i, (i<p)%coq_nat -> g i=f i) ->
  (forall i, (p<=i)%coq_nat -> (i<(Nat.add p q))%coq_nat -> g i=0) ->
  finite_sum g (List.seq 0 ((Nat.add p q)))=finite_sum f (List.seq 0 p).
Proof.
intros HF HG; rewrite finite_sum_seq_split.
assert (H1 : finite_sum g (List.seq 0 p)=finite_sum f (List.seq 0 p)).
{ apply finite_sum_ext; intros i Hi; apply HF; apply in_seq in Hi; lia. }
assert (H2 : finite_sum (fun k => g ((Nat.add p k))%coq_nat) (List.seq 0 q)=0).
{ rewrite <- (finite_sum_zero (List.seq 0 q)); apply finite_sum_ext; intros k Hk; apply in_seq in Hk; apply HG; lia. }
rewrite H1 H2; ring.
Qed.

Lemma paper_main_projection_right_linear p q c xs :
  linear_form ((Nat.add p q))%coq_nat (paper_main_projection_right p c) xs=linear_form q c (List.skipn p xs).
Proof.
unfold linear_form; rewrite finite_sum_seq_split.
assert (H0 : finite_sum (fun i => paper_main_projection_right p c i*List.nth i xs 0) (List.seq 0 p)=0).
{ rewrite <- (finite_sum_zero (List.seq 0 p)); apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
  rewrite (paper_main_projection_right_inside p c i ltac:(lia)); ring. }
rewrite H0 Rplus_0_l; apply finite_sum_ext; intros i Hi.
rewrite paper_main_projection_right_shift nth_skipn_add; reflexivity.
Qed.

Lemma paper_main_projection_left_quadratic p q A xs :
  paper_main_projection_quadratic ((Nat.add p q))%coq_nat (paper_main_projection_left p A) xs=
    paper_main_projection_quadratic p A (List.firstn p xs).
Proof.
unfold paper_main_projection_quadratic; apply paper_main_projection_sum_prefix.
- intros i Hi; apply paper_main_projection_sum_prefix.
  + intros j Hj; rewrite (paper_main_projection_left_inside p A i j Hi Hj).
    unfold paper_main_projection_entry; rewrite (nth_firstn_lt xs p i Hi) (nth_firstn_lt xs p j Hj); reflexivity.
  + intros j Hj HjD; rewrite (paper_main_projection_left_outside p A i j (or_intror Hj)); ring.
- intros i Hi HiD; rewrite <- (finite_sum_zero (List.seq 0 ((Nat.add p q)))).
  apply finite_sum_ext; intros j Hj; rewrite (paper_main_projection_left_outside p A i j (or_introl Hi)); ring.
Qed.

Theorem paper_main_projection_blocks_orthogonal p q A c xs :
  paper_main_projection_cross ((Nat.add p q))%coq_nat (paper_main_projection_left p A)
    (paper_main_projection_right p c) xs=0.
Proof.
unfold paper_main_projection_cross; rewrite <- (finite_sum_zero (List.seq 0 ((Nat.add p q)))).
apply finite_sum_ext; intros i Hi; destruct(Nat.lt_ge_cases i p) as [Hip|Hip].
- rewrite (paper_main_projection_right_inside p c i Hip); ring.
- assert (H0 : linear_form ((Nat.add p q))%coq_nat (paper_main_projection_left p A i) xs=0).
  { unfold linear_form; rewrite <- (finite_sum_zero (List.seq 0 ((Nat.add p q)))).
    apply finite_sum_ext; intros j Hj; rewrite (paper_main_projection_left_outside p A i j (or_introl Hip)); ring. }
  rewrite H0; ring.
Qed.
