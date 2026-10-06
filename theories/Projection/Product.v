(* Center the contraction and bound its coefficient norm by an operator bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.CovarianceLinearImages
  Data.FeatureMomentsCoordinates Projection.Stein Projection.Quadratic
  Projection.Algebra Projection.Variance.
Open Scope R_scope.

Definition paper_main_projection_product d (A B : nat -> nat -> R) i j :=
  finite_sum (fun k => A k i*B k j) (List.seq 0 d).
Definition paper_main_projection_trace d (A : nat -> nat -> R) :=
  finite_sum (fun i => A i i) (List.seq 0 d).
Definition paper_main_projection_pairing d (A B : nat -> nat -> R) :=
  finite_sum (fun i => finite_sum (fun j => A i j*B i j) (List.seq 0 d)) (List.seq 0 d).
Definition paper_main_projection_operator_bound d (A : nat -> nat -> R) eps :=
  forall z : nat -> R, finite_sum (fun i => (finite_sum (fun j => A i j*z j) (List.seq 0 d))^2) (List.seq 0 d)<=
    eps^2*finite_sum (fun j => z j^2) (List.seq 0 d).

Lemma paper_main_projection_sum_product I J f g :
  finite_sum f I*finite_sum g J=
    finite_sum (fun i => finite_sum (fun j => f i*g j) J) I.
Proof.
rewrite -finite_sum_scale_r; apply finite_sum_ext; intros i Hi; symmetry; apply finite_sum_scale.
Qed.

Lemma paper_main_projection_quadratic_expand d A xs :
  paper_main_projection_quadratic d A xs=
    finite_sum (fun i => finite_sum (fun j => A i j*(List.nth i xs 0*List.nth j xs 0)) (List.seq 0 d)) (List.seq 0 d)-
      paper_main_projection_trace d A.
Proof.
unfold paper_main_projection_quadratic,paper_main_projection_trace.
rewrite -finite_sum_minus; apply finite_sum_ext; intros i Hi; apply in_seq in Hi.
transitivity (finite_sum (fun j => A i j*(List.nth i xs 0*List.nth j xs 0)-pmdf_kron i j*A i j) (List.seq 0 d)).
- apply finite_sum_ext; intros j Hj; unfold paper_main_projection_entry,pmdf_kron; ring.
- rewrite finite_sum_minus (paper_main_projection_delta_sum d i (A i) ltac:(lia)); reflexivity.
Qed.

Lemma paper_main_projection_product_gram d A B xs :
  paper_main_projection_gram d A B xs=
    finite_sum (fun i => finite_sum (fun j => paper_main_projection_product d A B i j*
      (List.nth i xs 0*List.nth j xs 0)) (List.seq 0 d)) (List.seq 0 d).
Proof.
unfold paper_main_projection_gram,linear_form,paper_main_projection_product.
transitivity (finite_sum (fun k => finite_sum (fun i => finite_sum
  (fun j => (A k i*List.nth i xs 0)*(B k j*List.nth j xs 0)) (List.seq 0 d)) (List.seq 0 d)) (List.seq 0 d)).
- apply finite_sum_ext; intros k Hk; apply paper_main_projection_sum_product.
- rewrite finite_sum_swap; apply finite_sum_ext; intros i Hi.
  rewrite finite_sum_swap; apply finite_sum_ext; intros j Hj.
  rewrite -finite_sum_scale_r; apply finite_sum_ext; intros k Hk; ring.
Qed.

Lemma paper_main_projection_product_trace d A B :
  paper_main_projection_trace d (paper_main_projection_product d A B)=paper_main_projection_pairing d A B.
Proof.
unfold paper_main_projection_trace,paper_main_projection_product,paper_main_projection_pairing.
rewrite finite_sum_swap; reflexivity.
Qed.

Theorem paper_main_projection_centered_product d A B xs :
  paper_main_projection_gram d A B xs-paper_main_projection_pairing d A B=
    paper_main_projection_quadratic d (paper_main_projection_product d A B) xs.
Proof.
rewrite paper_main_projection_quadratic_expand paper_main_projection_product_trace.
rewrite paper_main_projection_product_gram; reflexivity.
Qed.

Theorem paper_main_projection_product_bound d A B eps :
  (forall i j, (i<d)%coq_nat -> (j<d)%coq_nat -> A i j=A j i) ->
  paper_main_projection_operator_bound d A eps ->
  paper_main_projection_square_coefficients d (paper_main_projection_product d A B)<=
    eps^2*paper_main_projection_square_coefficients d B.
Proof.
intros HA HO; unfold paper_main_projection_square_coefficients.
rewrite finite_sum_swap.
eapply Rle_trans with (finite_sum (fun j => eps^2*finite_sum (fun i => B i j^2) (List.seq 0 d)) (List.seq 0 d)).
- apply finite_sum_le; intros j Hj.
  assert (HE : forall i, (i<d)%coq_nat -> paper_main_projection_product d A B i j=
    finite_sum (fun k => A i k*B k j) (List.seq 0 d)).
  { intros i Hi; unfold paper_main_projection_product; apply finite_sum_ext; intros k Hk; apply in_seq in Hk.
    rewrite (HA k i ltac:(lia) Hi); reflexivity. }
  transitivity (finite_sum (fun i => (finite_sum (fun k => A i k*B k j) (List.seq 0 d))^2) (List.seq 0 d)).
  + right; apply finite_sum_ext; intros i Hi; apply in_seq in Hi; rewrite (HE i ltac:(lia)); reflexivity.
  + apply HO.
- rewrite finite_sum_scale finite_sum_swap; right; reflexivity.
Qed.
