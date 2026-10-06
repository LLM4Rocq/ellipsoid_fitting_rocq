(* Residual tails for every row of the actual Gaussian data sample. The
   sample x : paper_main_sample N d has the law gaussian_product_law (N * d).
   Its features are W_i = paper_main_head_feature x i = (x_i x_i^T - I)/sqrt d
   with x_i = paper_main_point x i.
   - Row law (paper_main_gaussian_residual_row_law). For symmetric P and
     i < N, the event {r <= |<W_i, P>|} is measurable and has the
     probability of the one-point event of PaperMainGaussianResidual under
     gaussian_product_law d. Proof by induction on N with the coordinate
     split d + (N - 1) d: row 0 is a function of the first d coordinates
     (paper_main_take_coordinates_law) and row i + 1 is row i of the last
     (N - 1) d coordinates (paper_main_drop_coordinates_law). The moment
     transport concerns regular functions, not indicators, so the event law
     is proved here from the exact coordinate laws.
   - Finite union (paper_main_gaussian_residual_union), with the union
     bound of PaperMainGaussianUnion: the event "exists i < N, r <= |<W_i, P>|"
     is measurable and has probability at most N q when every one-point
     probability is at most q. N = 0 gives the empty event.
   - For d = S n, symmetric P with paper_main_pairing P P = 1, 0 <= kappa and
     paper_main_cone_opnorm_le P (kappa / sqrt d), and r > 0:
       P[r <= |<W_i, P>|] <= 2 exp (- d r^2 / (4 + 4 kappa r)),
       P[exists i < N, r <= |<W_i, P>|]
         <= N 2 exp (- d r^2 / (4 + 4 kappa r)). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHeadFeature
  PaperMainConeConditionOperator PaperMainSampling PaperMainHeadLaw
  PaperMainGaussianUnion PaperMainGaussianDataRadius
  PaperMainSymmetricDiagonalizationBridge PaperMainGaussianQuadraticTail
  PaperMainGaussianResidual.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* Points and features after the coordinate split. *)

Lemma paper_main_gaussian_residual_point_take d k (x : paper_main_sample (S k) d) :
  paper_main_point x 0%N =
  paper_main_symmetric_column (tval (paper_main_take_coordinates d (Nat.mul k d) x)).
Proof.
apply/matrixP => j c; rewrite [c]ord1 !mxE.
by rewrite (paper_main_data_take_nth d (Nat.mul k d) x j (elimT ssrnat.ltP (ltn_ord j))).
Qed.

Lemma paper_main_gaussian_residual_point_drop d k (x : paper_main_sample (S k) d) i :
  paper_main_point x (S i) =
  paper_main_point (paper_main_drop_coordinates d (Nat.mul k d) x : paper_main_sample k d) i.
Proof.
apply/matrixP => j c; rewrite [c]ord1 !mxE paper_main_drop_coordinates_nth.
congr (List.nth _ _ _).
rewrite /= -!plusE -!multE; lia.
Qed.

Lemma paper_main_gaussian_residual_feature_take d k (x : paper_main_sample (S k) d) :
  paper_main_head_feature x 0%N =
  paper_main_gaussian_residual_feature (tval (paper_main_take_coordinates d (Nat.mul k d) x)).
Proof. by rewrite /paper_main_head_feature paper_main_gaussian_residual_point_take. Qed.

Lemma paper_main_gaussian_residual_feature_drop d k (x : paper_main_sample (S k) d) i :
  paper_main_head_feature x (S i) =
  paper_main_head_feature
    (paper_main_drop_coordinates d (Nat.mul k d) x : paper_main_sample k d) i.
Proof. by rewrite /paper_main_head_feature paper_main_gaussian_residual_point_drop. Qed.

(* Events. *)

Definition paper_main_gaussian_residual_one (d : nat) (P : 'M[R]_d) (r : R) :
    set (d.-tuple T) :=
  [set y | Rle r (Rabs (paper_main_pairing (paper_main_gaussian_residual_feature (tval y)) P))].

Definition paper_main_gaussian_residual_row_event (N d : nat) (P : 'M[R]_d) (r : R)
    (i : nat) : set (paper_main_sample N d) :=
  [set x | Rle r (Rabs (paper_main_pairing (paper_main_head_feature x i) P))].

Definition paper_main_gaussian_residual_event (N d : nat) (P : 'M[R]_d) (r : R) :
    set (paper_main_sample N d) :=
  [set x | exists i, (i < N)%coq_nat /\
    Rle r (Rabs (paper_main_pairing (paper_main_head_feature x i) P))].

(* The law of one row. *)

Theorem paper_main_gaussian_residual_row_law N d (P : 'M[R]_d) r i :
  paper_main_symmetric P -> (i < N)%coq_nat ->
  measurable (paper_main_gaussian_residual_row_event N d P r i) /\
  gaussian_product_law (N * d)%N (paper_main_gaussian_residual_row_event N d P r i) =
  gaussian_product_law d (paper_main_gaussian_residual_one d P r).
Proof.
move=> HP; elim: N i => [|k IH] i Hi; first lia.
have mA : measurable (paper_main_gaussian_residual_one d P r).
  exact: paper_main_gaussian_residual_measurable.
case: i Hi => [|i] Hi.
- have -> : paper_main_gaussian_residual_row_event (S k) d P r 0%N =
      paper_main_take_coordinates d (Nat.mul k d) @^-1` paper_main_gaussian_residual_one d P r.
    by apply/seteqP; split=> x; rewrite /paper_main_gaussian_residual_row_event
      /paper_main_gaussian_residual_one /= paper_main_gaussian_residual_feature_take.
  split.
    have H := paper_main_take_coordinates_measurable d (Nat.mul k d) measurableT _ mA.
    by rewrite setTI in H.
  exact: (paper_main_take_coordinates_law d (Nat.mul k d) _ mA).
- have [mE HE] := IH i ltac:(lia).
  have -> : paper_main_gaussian_residual_row_event (S k) d P r (S i) =
      paper_main_drop_coordinates d (Nat.mul k d) @^-1`
        paper_main_gaussian_residual_row_event k d P r i.
    by apply/seteqP; split=> x; rewrite /paper_main_gaussian_residual_row_event /=
      paper_main_gaussian_residual_feature_drop.
  split.
    have H := paper_main_drop_coordinates_measurable d (Nat.mul k d) measurableT _ mE.
    by rewrite setTI in H.
  rewrite -HE.
  exact: (paper_main_drop_coordinates_law d (Nat.mul k d) _ mE).
Qed.

(* The finite union over the rows. *)

Lemma paper_main_gaussian_residual_eventE N d (P : 'M[R]_d) r :
  paper_main_gaussian_residual_event N d P r =
  paper_main_finite_event_union (List.seq 0 N) (paper_main_gaussian_residual_row_event N d P r).
Proof.
apply/seteqP; split=> x /=.
- move=> [i [Hi Hr]]; apply/paper_main_finite_event_union_member.
  by exists i; split; [apply/List.in_seq; lia | exact: Hr].
- move/paper_main_finite_event_union_member => [i [Hi Hr]].
  by exists i; split; [move/List.in_seq: Hi; lia | exact: Hr].
Qed.

Theorem paper_main_gaussian_residual_union N d (P : 'M[R]_d) r (q : R) :
  paper_main_symmetric P ->
  (gaussian_product_law d (paper_main_gaussian_residual_one d P r) <= q%:E)%E ->
  measurable (paper_main_gaussian_residual_event N d P r) /\
  (gaussian_product_law (N * d)%N (paper_main_gaussian_residual_event N d P r) <=
    (Rmult (INR N) q)%:E)%E.
Proof.
move=> HP Hq.
rewrite paper_main_gaussian_residual_eventE.
have HM : forall i, List.In i (List.seq 0 N) ->
    measurable (paper_main_gaussian_residual_row_event N d P r i).
  move=> i Hi; move/List.in_seq: Hi => Hi.
  exact: (proj1 (paper_main_gaussian_residual_row_law N d P r i HP ltac:(lia))).
split; first exact: paper_main_gaussian_union_measurable.
have HB : forall i, List.In i (List.seq 0 N) ->
    (gaussian_product_law (N * d)%N (paper_main_gaussian_residual_row_event N d P r i)
      <= q%:E)%E.
  move=> i Hi; move/List.in_seq: Hi => Hi.
  by rewrite (proj2 (paper_main_gaussian_residual_row_law N d P r i HP ltac:(lia))).
have H := paper_main_gaussian_union_bound (N * d)%N (List.seq 0 N) _ q HM HB.
by rewrite List.length_seq in H.
Qed.

(* The tails for d = S n. *)

Theorem paper_main_gaussian_residual_rows_tail N n (P : 'M[R]_(S n)) (kappa r : R) :
  paper_main_symmetric P -> paper_main_pairing P P = 1 -> 0 <= kappa ->
  paper_main_cone_opnorm_le P (kappa / Num.sqrt (S n)%:R) -> 0 < r ->
  measurable (paper_main_gaussian_residual_event N (S n) P r) /\
  (gaussian_product_law (N * S n)%N (paper_main_gaussian_residual_event N (S n) P r)
    <= (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
      (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> HP HP1 Hk HB Hr.
exact: (paper_main_gaussian_residual_union N (S n) P r _ HP
  (paper_main_gaussian_residual_tail n P kappa r HP HP1 Hk HB Hr)).
Qed.
