(* The A26 data loss as the public quadratic risk of a block matrix.

   Row losses of PaperMainHybridFiniteArray with m = mi + 1 and fixed triples
   (H_j, B_j, b_j):
   1. pmdf_quad B y = y^T B y - Tr B, so on a row (g, y) the data row loss is
      phi ((g, y)^T (block_mx H_j 0 0 B_j) (g, y) - Tr (block_mx H_j 0 0 B_j) - b_j)
      (block form and trace of PaperMainBlockGeometry).
   2. Row i of a sample x of N rows of r + m coordinates is paper_main_point x i,
      so the loss array of state j equals
      INR N * paper_main_quadratic_risk N (r + m) x (block_mx H_j 0 0 B_j) b_j.
   3. On the rotated sample paper_main_orientation_rotate N (r + m) O x the
      array is INR N times the quadratic risk of x for the conjugated matrix
      O^T (block_mx H_j 0 0 B_j) O.
   4. A state of the prior with risk at most a gives normalized finite soft
      loss at most a + ln |I| / (beta N) (M110 witness bound), on the sample
      and on the rotated sample. All positivity premises are explicit. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums PaperMainMatrixDuality
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments PaperMainTranslatedLoss
  PaperMainLossArray PaperMainLossSoftNormalized PaperMainLossNormalizedArray PaperMainLossEmpirical
  PaperMainFeatureLossControl PaperMainHeadSmallBallNet PaperMainBlockGeometry
  GaussianProbabilityProductContinuity PaperMainHybridFiniteArray PaperMainOrientationRotation.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The centered quadratic of a row block. *)

Lemma paper_main_orientation_pmdf_quad mi (B : 'M[R]_(S mi)) (ys : list R) :
  pmdf_quad mi B ys =
  (paper_main_quadratic_form B (\col_(k < S mi) List.nth k ys 0) - paper_main_trace B)%Rcoq.
Proof.
rewrite /pmdf_quad /paper_main_quadratic_form /paper_main_trace RminusE -sumrB.
apply: eq_bigr => a _.
have -> : \sum_(b < S mi) B a b * pmdf_centered a b ys =
    \sum_(b < S mi) ((\col_k List.nth k ys 0) a 0 * B a b * (\col_k List.nth k ys 0) b 0) -
    \sum_(b < S mi) (a == b)%:R * B a b.
  rewrite -sumrB; apply: eq_bigr => b _.
  rewrite /pmdf_centered (pmdf_kron_ord mi) !mxE -RminusE -!RmultE.
  have E : forall p q u v : R, (p * (u * v - q) = u * p * v - q * p)%Rcoq by move=> *; ring.
  exact: E.
by rewrite pmdf_sum_kron.
Qed.

(* 2. Rows of the sample and the array identity. *)

Lemma paper_main_orientation_point_block N r mi
    (x : (N * (r + S mi)).-tuple (measurableTypeR R)) (i : nat) :
  paper_main_point x i =
  col_mx (paper_main_hybrid_finite_head r
      (List.firstn (r + S mi)%coq_nat (List.skipn (i * (r + S mi)%coq_nat)%N (tval x))))
    (\col_(k < S mi) List.nth k (List.skipn r
      (List.firstn (r + S mi)%coq_nat (List.skipn (i * (r + S mi)%coq_nat)%N (tval x)))) 0).
Proof.
apply/matrixP => k l; rewrite [l]ord1 !mxE.
case: splitP => t Ht; rewrite !mxE.
  have Htr : (t < (r + S mi)%coq_nat)%N by rewrite plusE ltn_addr.
  by rewrite (paper_main_hybrid_finite_row_nth _ _ _ _ Htr) Ht.
rewrite List.nth_skipn.
have Hrt : ((r + t)%coq_nat < (r + S mi)%coq_nat)%N by rewrite !plusE ltn_add2l.
by rewrite (paper_main_hybrid_finite_row_nth _ _ _ _ Hrt) Ht plusE.
Qed.

Theorem paper_main_orientation_data_array N r mi (Hs : nat -> 'M[R]_r) (bs : nat -> R)
    (Bs : nat -> 'M[R]_(S mi)) (x : (N * (r + S mi)).-tuple (measurableTypeR R)) (j : nat) :
  paper_main_loss_array (r + S mi)%coq_nat N (paper_main_hybrid_finite_data_loss r mi Hs bs Bs)
    (tval x) j =
  (INR N * paper_main_quadratic_risk N (r + S mi) x (block_mx (Hs j) 0 0 (Bs j)) (bs j))%Rcoq.
Proof.
rewrite paper_main_hybrid_finite_array_sum /paper_main_quadratic_risk /paper_main_loss_empirical
  paper_main_finite_sum_public.
have Hrow : forall i : 'I_N, paper_main_hybrid_finite_data_loss r mi Hs bs Bs i j
    (List.firstn (r + S mi)%coq_nat (List.skipn (i * (r + S mi)%coq_nat)%N (tval x))) =
    paper_main_loss (paper_main_quadratic_form (block_mx (Hs j) 0 0 (Bs j)) (paper_main_point x i) -
      paper_main_trace (block_mx (Hs j) 0 0 (Bs j)) - bs j)%Rcoq.
  move=> i.
  rewrite /paper_main_hybrid_finite_data_loss /paper_main_hybrid_finite_offset
    /paper_main_head_small_ball_value paper_main_orientation_pmdf_quad.
  rewrite (paper_main_orientation_point_block N r mi x i) paper_main_block_form
    paper_main_block_trace.
  congr paper_main_loss.
  rewrite -!RplusE.
  have E : forall a b c d e : R, (a - b - e + (c - d) = a + c - (b + d) - e)%Rcoq
    by move=> *; ring.
  exact: E.
rewrite (eq_bigr _ (fun i _ => Hrow i)).
have key : forall (n : nat) (f : 'I_n -> R),
    \sum_(i < n) f i = (INR n * (/ INR n * \sum_(i < n) f i))%Rcoq.
  move=> [|n] f; first by rewrite big_ord0 /= Rmult_0_l.
  have Hn : INR n.+1 <> 0%Rcoq by apply: not_0_INR.
  have E : forall s a : R, (a <> 0 -> s = a * (/ a * s))%Rcoq by move=> s a Ha; field.
  exact: E.
exact: key.
Qed.

(* 3. The rotated sample: the risk of x for the conjugated block matrix. *)

Lemma paper_main_orientation_rotate_point_nat N d (O : 'M[R]_d)
    (x : (N * d).-tuple (measurableTypeR R)) (i : nat) :
  (i < N)%N ->
  paper_main_point (paper_main_orientation_rotate N d O x) i = O *m paper_main_point x i.
Proof.
move=> Hi; apply/matrixP => a b; rewrite [b]ord1 !mxE paper_main_orientation_rotate_nth //.
by apply: eq_bigr => c _; rewrite mxE.
Qed.

Lemma paper_main_orientation_risk_rotate N d (O S : 'M[R]_d)
    (x : (N * d).-tuple (measurableTypeR R)) (b : R) :
  O^T *m O = 1%:M ->
  paper_main_quadratic_risk N d (paper_main_orientation_rotate N d O x) S b =
  paper_main_quadratic_risk N d x (O^T *m S *m O) b.
Proof.
move=> HO.
rewrite /paper_main_quadratic_risk /paper_main_loss_empirical.
congr (_ * _)%Rcoq; apply: finite_sum_ext => i Hi.
have Hi' : (i < N)%N by apply/ssrnat.ltP; have := proj2 (proj1 (List.in_seq _ _ _) Hi); lia.
rewrite paper_main_orientation_rotate_point_nat //.
congr paper_main_loss.
exact: (paper_main_orientation_head_value O S b _ HO).
Qed.

(* 4. A good candidate bounds the normalized finite soft loss. *)

Theorem paper_main_orientation_candidate_bound N r mi beta (I : list nat)
    (Hs : nat -> 'M[R]_r) (bs : nat -> R) (Bs : nat -> 'M[R]_(S mi))
    (x : (N * (r + S mi)).-tuple (measurableTypeR R)) (j : nat) (a : R) :
  (0 < N)%coq_nat -> I <> nil -> (0 < beta)%Rcoq -> In j I ->
  (paper_main_quadratic_risk N (r + S mi) x (block_mx (Hs j) 0 0 (Bs j)) (bs j) <= a)%Rcoq ->
  (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
   a + ln (INR (length I)) / (beta * INR N))%Rcoq.
Proof.
move=> HN HI Hb Hj Ha.
have W := paper_main_loss_normalized_array_witness (r + S mi)%coq_nat N beta I
  (paper_main_hybrid_finite_data_loss r mi Hs bs Bs) (tval x) j HN HI Hb Hj.
rewrite paper_main_orientation_data_array in W.
have HNpos : (0 < INR N)%Rcoq by apply: lt_0_INR.
have E : forall s q : R, (s <> 0 -> / s * (s * q) = q)%Rcoq by move=> s q Hs0; field.
rewrite (E _ _ (Rgt_not_eq _ _ HNpos)) in W.
rewrite /paper_main_hybrid_finite_data; lra.
Qed.

Theorem paper_main_orientation_candidate_bound_rotate N r mi beta (I : list nat)
    (Hs : nat -> 'M[R]_r) (bs : nat -> R) (Bs : nat -> 'M[R]_(S mi)) (O : 'M[R]_(r + S mi))
    (x : (N * (r + S mi)).-tuple (measurableTypeR R)) (j : nat) (a : R) :
  O^T *m O = 1%:M -> (0 < N)%coq_nat -> I <> nil -> (0 < beta)%Rcoq -> In j I ->
  (paper_main_quadratic_risk N (r + S mi) x (O^T *m block_mx (Hs j) 0 0 (Bs j) *m O) (bs j)
     <= a)%Rcoq ->
  (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs
     (tval (paper_main_orientation_rotate N (r + S mi) O x)) <=
   a + ln (INR (length I)) / (beta * INR N))%Rcoq.
Proof.
move=> HO HN HI Hb Hj Ha.
apply: (paper_main_orientation_candidate_bound N r mi beta I Hs bs Bs _ j a HN HI Hb Hj).
by rewrite paper_main_orientation_risk_rotate.
Qed.
