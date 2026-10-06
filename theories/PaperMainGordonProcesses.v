(* Finite unit-vector families in the Gaussian processes of paper section 2.2.
   For unit vectors z y of R^N and v t of R^M, the min-max over y and t of
   the bilinear form z y ^T A v t of an N x M Gaussian matrix A dominates in
   mean the min-max of the auxiliary process <g, z y> + <h, v t>
   (paper_main_gordon_process_comparison). The proof reads both processes on
   row vectors through GaussianLawBridge and applies auxT_bilT_minmax of the
   library, an instance of Gordon's inequality. *)
From Stdlib Require Import Reals List Lia Lra FunctionalExtensionality.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions
  GaussianCovarianceDefinitions GaussianCovarianceSums PaperMainGordonCoordinates
  PaperMainGordonFinite PaperMainGordonProcessCovariance.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_auxiliary N M (u v : nat -> R) xs :=
  paper_main_gordon_dot N u (fun i => List.nth i xs 0) +
  paper_main_gordon_dot M v (fun j => List.nth (N + j)%nat xs 0).

Lemma paper_main_gordon_vector_row N M Z V a xs :
  gaussian_covariance_row (N + M)
    (paper_main_gordon_vector_loading N Z V) a xs =
  paper_main_gordon_auxiliary N M (Z a) (V a) xs.
Proof.
unfold gaussian_covariance_row, paper_main_gordon_auxiliary, paper_main_gordon_dot.
rewrite finite_sum_seq_split.
unfold paper_main_gordon_vector_loading; f_equal.
- apply finite_sum_ext; intros k Hk; apply in_seq_lt in Hk.
  assert (E : (k <? N)%nat = true) by (apply Nat.ltb_lt; exact Hk).
  rewrite E; reflexivity.
- apply finite_sum_ext; intros k Hk.
  assert (E : ((N + k) <? N)%nat = false) by (apply Nat.ltb_ge; lia).
  rewrite E; replace (N + k - N)%nat with k by lia; reflexivity.
Qed.

Lemma paper_main_gordon_finite_max_ext f g I :
  (forall i, In i I -> f i = g i) -> finite_max f I = finite_max g I.
Proof.
induction I as [|i I IH]; intros H; [reflexivity|].
destruct I as [|j I].
- simpl; apply H; simpl; auto.
- change (Rmax (f i) (finite_max f (j :: I)) = Rmax (g i) (finite_max g (j :: I))).
  rewrite (H i (or_introl eq_refl)).
  f_equal; apply IH; intros k Hk; apply H; right; exact Hk.
Qed.

Lemma paper_main_gordon_finite_minimax_ext F G Y S :
  (forall y s, In y Y -> In s S -> F y s = G y s) ->
  finite_minimax F Y S = finite_minimax G Y S.
Proof.
intros H; unfold finite_minimax, finite_min.
f_equal; apply paper_main_gordon_finite_max_ext; intros y Hy.
f_equal; apply paper_main_gordon_finite_max_ext; intros s Hs.
apply H; assumption.
Qed.

From EllipsoidFitting Require Import GaussianCoordinateDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity GaussianFiniteSums.

(* Continuity and domain of the min-max of the auxiliary process. *)
Lemma paper_main_gordon_minimax_continuous d (H : nat -> nat -> list R -> R) Y S :
  (forall y t, In y Y -> In t S -> finite_joint_continuous d (H y t)) ->
  finite_joint_continuous d (fun xs => finite_minimax (fun y t => H y t xs) Y S).
Proof.
intros HC; unfold finite_minimax, finite_min.
apply finite_joint_continuous_ext with
  (F := fun xs => -1 * finite_max (fun y => -1 * finite_max (fun t => H y t xs) S) Y).
- intros xs _.
  assert (HE : (fun y => -1 * finite_max (fun t => H y t xs) S) =
    (fun y => - finite_max (fun t => H y t xs) S)).
  { extensionality y; ring. }
  rewrite HE; ring.
- apply finite_joint_continuous_scale.
  apply (paper_main_gordon_finite_max_continuous d
    (fun xs y => -1 * finite_max (fun t => H y t xs) S)); intros y Hy.
  apply finite_joint_continuous_scale.
  apply (paper_main_gordon_finite_max_continuous d (fun xs t => H y t xs)); intros t Ht.
  apply HC; assumption.
Qed.

Lemma paper_main_gordon_auxiliary_continuous N M u v :
  finite_joint_continuous (N + M) (paper_main_gordon_auxiliary N M u v).
Proof.
unfold paper_main_gordon_auxiliary, paper_main_gordon_dot.
apply finite_joint_continuous_add.
- apply (finite_joint_continuous_sum (N + M) (seq 0 N)
    (fun i xs => u i * nth i xs 0)); intros i Hi.
  apply finite_joint_continuous_scale, finite_joint_continuous_nth.
  apply in_seq_lt in Hi; lia.
- apply (finite_joint_continuous_sum (N + M) (seq 0 M)
    (fun j xs => v j * nth (N + j) xs 0)); intros j Hj.
  apply finite_joint_continuous_scale, finite_joint_continuous_nth.
  apply in_seq_lt in Hj; lia.
Qed.

Lemma paper_main_gordon_matrix_form_continuous N M (u v : nat -> R) :
  finite_joint_continuous (N * M) (fun xs => finite_sum (fun i => finite_sum (fun j =>
    u i * v j * nth (i * M + j)%nat xs 0) (seq 0 M)) (seq 0 N)).
Proof.
apply (finite_joint_continuous_sum (N * M) (seq 0 N) (fun i xs => finite_sum (fun j =>
  u i * v j * nth (i * M + j)%nat xs 0) (seq 0 M))); intros i Hi.
apply (finite_joint_continuous_sum (N * M) (seq 0 M)
  (fun j xs => u i * v j * nth (i * M + j)%nat xs 0)); intros j Hj.
apply finite_joint_continuous_scale, finite_joint_continuous_nth.
apply in_seq_lt in Hi; apply in_seq_lt in Hj; nia.
Qed.

Lemma paper_main_gordon_auxiliary_domain r s N M z v :
  (0 < r)%nat -> (0 < s)%nat ->
  gaussian_covariance_domain (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)).
Proof.
intros Hr Hs.
set (J := fun y t => (y * s + t)%nat).
set (Z := fun a => z (a / s)%nat).
set (V := fun a => v (a mod s)%nat).
set (Q := paper_main_gordon_vector_loading N Z V).
assert (HY : List.seq 0 r <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HS : List.seq 0 s <> []).
{ intros H; apply (f_equal (@List.length nat)) in H; rewrite length_seq in H; simpl in H; lia. }
assert (HJ : forall y t, In y (List.seq 0 r) -> In t (List.seq 0 s) -> (J y t < r * s)%nat).
{ intros y t Hy Ht; apply in_seq_lt in Hy; apply in_seq_lt in Ht; unfold J; nia. }
pose proof (paper_main_gordon_finite_domain (r * s) (N + M) Q J
  (List.seq 0 r) (List.seq 0 s) HY HS HJ) as HD.
assert (HQ : (fun xs => paper_main_gordon_finite J (List.seq 0 r) (List.seq 0 s)
  (gaussian_covariance_image (r * s) (N + M) Q xs)) =
  (fun xs => finite_minimax (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s))).
{ extensionality xs.
  unfold paper_main_gordon_finite, paper_main_gordon_scores, gaussian_covariance_image.
  apply paper_main_gordon_finite_minimax_ext; intros y t Hy Ht.
  rewrite nth_map_seq by (apply HJ; assumption).
  unfold Q; rewrite paper_main_gordon_vector_row.
  apply in_seq_lt in Ht; unfold Z, V, J.
  rewrite paper_main_gordon_row_major_div, paper_main_gordon_row_major_mod by exact Ht.
  reflexivity. }
rewrite HQ in HD; exact HD.
Qed.

(* Gordon's comparison of the two processes, from the library. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean slepian gordon escape.
From EllipsoidFitting Require Import SoftExtrema GaussianLawBridge.
From EllipsoidFitting Require Import RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.

Section gordon_library.
Local Notation RR := (R : realType).

Lemma paper_main_gordon_finite_max_rmax n (f : nat -> R) :
  finite_max f (List.seq 0 n.+1) = rmax (\row_(t < n.+1) (f t : RR)).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  have [i [Hi ->]] := finite_max_attained f (List.seq 0 n.+1) ltac:(discriminate).
  have ilt : ltn i n.+1 by apply/ssrnat.ltP; exact: in_seq_lt.
  by have := le_rmax (\row_(t < n.+1) (f t : RR)) (Ordinal ilt); rewrite mxE.
apply: rmax_le => t; rewrite mxE; apply/RleP; apply: finite_max_member.
by apply: lt_in_seq; apply/ssrnat.ltP.
Qed.

Lemma paper_main_gordon_minimax_minmax r s (H : nat -> nat -> R) :
  finite_minimax H (List.seq 0 r.+1) (List.seq 0 s.+1) =
  minmax (\matrix_(u < r.+1, t < s.+1) (H u t : RR)).
Proof.
rewrite /finite_minimax /finite_min /minmax paper_main_gordon_finite_max_rmax RoppE.
congr (- rmax _)%R; apply/rowP => u; rewrite !mxE paper_main_gordon_finite_max_rmax.
by rewrite RoppE; congr (- rmax _)%R; apply/rowP => t; rewrite !mxE.
Qed.

Theorem paper_main_gordon_process_comparison r s N M (z v : nat -> nat -> R) :
  (0 < r)%coq_nat -> (0 < s)%coq_nat ->
  (forall y, (y < r)%coq_nat -> paper_main_gordon_dot N (z y) (z y) = 1) ->
  (forall t, (t < s)%coq_nat -> paper_main_gordon_dot M (v t) (v t) = 1) ->
  gaussian_covariance_domain (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) ->
  gaussian_covariance_domain (N * M) (fun xs => finite_minimax
    (fun y t => finite_sum (fun i => finite_sum (fun j =>
       z y i * v t j * List.nth (i * M + j)%coq_nat xs 0) (List.seq 0 M)) (List.seq 0 N))
    (List.seq 0 r) (List.seq 0 s)) ->
  gaussian_iterated_expectation (N + M) (fun xs => finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) xs)
    (List.seq 0 r) (List.seq 0 s)) <=
  gaussian_iterated_expectation (N * M) (fun xs => finite_minimax
    (fun y t => finite_sum (fun i => finite_sum (fun j =>
       z y i * v t j * List.nth (i * M + j)%coq_nat xs 0) (List.seq 0 M)) (List.seq 0 N))
    (List.seq 0 r) (List.seq 0 s)).
Proof.
case: r => [|r] Hr; first by inversion Hr.
case: s => [|s] Hs; first by inversion Hs.
move=> Hz Hv [IA [AA _]] [IM [AM _]].
have CA := paper_main_gordon_minimax_continuous (N + M)
  (fun y t xs => paper_main_gordon_auxiliary N M (z y) (v t) xs)
  (List.seq 0 r.+1) (List.seq 0 s.+1)
  (fun y t _ _ => paper_main_gordon_auxiliary_continuous N M (z y) (v t)).
have CM := paper_main_gordon_minimax_continuous (N * M)
  (fun y t xs => finite_sum (fun i => finite_sum (fun j =>
     z y i * v t j * List.nth (i * M + j)%coq_nat xs 0) (List.seq 0 M)) (List.seq 0 N))
  (List.seq 0 r.+1) (List.seq 0 s.+1)
  (fun y t _ _ => paper_main_gordon_matrix_form_continuous N M (z y) (v t)).
have [_ ->] := @gaussian_iterated_expectation_gauss _ _ CA IA AA.
have [_ ->] := @gaussian_iterated_expectation_gauss _ _ CM IM AM.
pose zs (u : 'I_r.+1) : 'cV[RR]_N := (\col_i z u i)%R.
pose vs (t : 'I_s.+1) : 'cV[RR]_M := (\col_j v t j)%R.
have dotE n (w : nat -> R) :
    paper_main_gordon_dot n w w = mxdot (\col_(i < n) (w i : RR))%R (\col_i w i)%R.
  rewrite /paper_main_gordon_dot finite_sum_seqE /mxdot.
  by apply: eq_bigr => i _; rewrite big_ord1 !mxE.
have zs1 u : frobenius (zs u) = 1%R.
  have uz : lt u r.+1 by apply/ssrnat.ltP.
  by rewrite /frobenius -dotE Hz// R1E sqrtr1.
have vs1 t : frobenius (vs t) = 1%R.
  have tv : lt t s.+1 by apply/ssrnat.ltP.
  by rewrite /frobenius -dotE Hv// R1E sqrtr1.
have h := auxT_bilT_minmax zs1 vs1.
have EA (w : 'rV[RR]_(N + M)) : finite_minimax
    (fun y t => paper_main_gordon_auxiliary N M (z y) (v t) (list_of_row w))
    (List.seq 0 r.+1) (List.seq 0 s.+1) = minmax (vec_mx (w *m auxT_mx zs vs)).
  rewrite paper_main_gordon_minimax_minmax; congr minmax; apply/matrixP => u t.
  rewrite mxE auxT_mxE /paper_main_gordon_auxiliary /paper_main_gordon_dot.
  rewrite !finite_sum_seqE /mxdot.
  congr (_ + _)%R; apply: eq_bigr => i _; rewrite big_ord1 !mxE.
    by rewrite (list_of_row_nth w (lshift M i)) mulrC.
  by rewrite (list_of_row_nth w (rshift N i)) mulrC.
have EM (a : 'rV[RR]_(N * M)) : finite_minimax
    (fun y t => finite_sum (fun i => finite_sum (fun j =>
       z y i * v t j * List.nth (i * M + j)%coq_nat (list_of_row a) 0)
       (List.seq 0 M)) (List.seq 0 N))
    (List.seq 0 r.+1) (List.seq 0 s.+1) = minmax (vec_mx (a *m bilT_mx zs vs)).
  rewrite paper_main_gordon_minimax_minmax; congr minmax; apply/matrixP => u t.
  rewrite mxE bilT_mxE finite_sum_seqE /mxdot.
  apply: eq_bigr => i _; rewrite big_ord1 !mxE finite_sum_seqE.
  rewrite mulr_sumr; apply: eq_bigr => j _; rewrite !mxE.
  have -> : List.nth (i * M + j)%coq_nat (list_of_row a) 0 = (a 0 (mxvec_index i j))%R.
    by rewrite -(list_of_row_nth a (mxvec_index i j)) mxvec_index_val.
  by rewrite !RmultE mulrAC -mulrA.
under eq_Rintegral do rewrite EA.
under [X in _ <= X]eq_Rintegral do rewrite EM.
apply/RleP; apply: fine_le.
- exact: integrable_fin_num (integrable_gauss_minmax _).
- exact: integrable_fin_num (integrable_gauss_minmax _).
- exact: h.
Qed.

End gordon_library.
