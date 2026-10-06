(* Finite orientation nets measured by the rank-r head projector.

   Conventions (master): S = O^T diag(a) O with O^T O = 1, and the head
   directions are the first r ROWS of O. The head projector is
     P_r(O) = O^T diag(1_{i<r}) O = W^T W,  W = diag(1_{i<r}) O,
   where W keeps the first r rows of O and is zero below them.
   1. P_r(O) = W^T W, and ||W||_F^2 = r when r <= d.
   2. ||P_r(O) - P_r(O')||_F <= 2 sqrt r ||W - W'||_F, by the product
      inequality (Projection.Frobenius).
   3. The code of O is the row-major list of the r d entries of its first r
      rows divided by sqrt r. Codes are unit vectors, and the squared code
      distance is ||W - W'||_F^2 / r.
   4. The checked ball net (Loss.BallNet) on the image of all
      orthogonal matrices, with a chosen orthogonal representative for each
      net point, gives for r >= 1, d >= r and tau > 0 a finite list of
      orthogonal matrices such that every orthogonal O has a member O' with
      ||P_r(O) - P_r(O')||_F <= tau, and
        ln (number) <= (4 + 8 r / tau) ln 2 (r + 1) (d + 1),
      a constant independent of d times d + 1. No full completion is
      constructed: each member is an actual orthogonal matrix. For r = 0 the
      single matrix 1 works, since P_0 = 0. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Gordon.ProcessCovariance Gordon.Nets Gordon.Entropy Loss.BallNet
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Geometry.HeadFrobenius
  Projection.Frobenius Spectral.Duality Analysis.ContinuousTupleMeasurability
  Orientation.Rotation.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The head projector and the head frame. *)

Definition paper_main_orientation_mask {d : nat} (r : nat) : 'rV[R]_d :=
  \row_(i < d) (if (i < r)%N then 1 else 0).

Definition paper_main_orientation_projector {d : nat} (r : nat) (O : 'M[R]_d) : 'M[R]_d :=
  O^T *m diag_mx (paper_main_orientation_mask r) *m O.

Definition paper_main_orientation_frame {d : nat} (r : nat) (O : 'M[R]_d) : 'M[R]_d :=
  diag_mx (paper_main_orientation_mask r) *m O.

Lemma paper_main_orientation_mask_idem {d : nat} (r : nat) :
  diag_mx (paper_main_orientation_mask r) *m diag_mx (paper_main_orientation_mask r) =
  diag_mx (paper_main_orientation_mask (d := d) r).
Proof.
apply/matrixP => i j; rewrite mul_diag_mx !mxE.
case: (eqVneq i j) => [->|Hij]; last by rewrite !mulr0n mulr0.
by rewrite !mulr1n; case: (j < r)%N; rewrite ?mulr1 ?mulr0.
Qed.

Lemma paper_main_orientation_frame_projector {d : nat} (r : nat) (O : 'M[R]_d) :
  paper_main_orientation_projector r O =
  (paper_main_orientation_frame r O)^T *m paper_main_orientation_frame r O.
Proof.
rewrite /paper_main_orientation_projector /paper_main_orientation_frame trmx_mul tr_diag_mx.
by rewrite [RHS]mulmxA -[in RHS](mulmxA O^T) paper_main_orientation_mask_idem.
Qed.

Lemma paper_main_orientation_mask_sum {d : nat} (r : nat) :
  (r <= d)%N -> \sum_(i < d) (paper_main_orientation_mask (d := d) r) 0 i = r%:R.
Proof.
move=> Hrd.
under eq_bigr do rewrite mxE.
rewrite -big_mkcond /= -(big_ord_widen d (fun _ => 1) Hrd) sumr_const card_ord.
by [].
Qed.

Lemma paper_main_orientation_frame_frobenius {d : nat} (r : nat) (O : 'M[R]_d) :
  (r <= d)%N -> O^T *m O = 1%:M ->
  paper_main_frobenius (paper_main_orientation_frame r O) ^+ 2 = r%:R.
Proof.
move=> Hrd HO; have HO' : O *m O^T = 1%:M by apply: mulmx1C.
rewrite paper_main_frobenius_trace -paper_main_orientation_frame_projector.
rewrite /paper_main_orientation_projector mxtrace_mulC mulmxA HO' mul1mx mxtrace_diag.
exact: paper_main_orientation_mask_sum.
Qed.

(* 2. Close head frames give close head projectors. *)

Lemma paper_main_orientation_projector_dist {d : nat} (r : nat) (O O' : 'M[R]_d) :
  (r <= d)%N -> O^T *m O = 1%:M -> O'^T *m O' = 1%:M ->
  paper_main_frobenius (paper_main_orientation_projector r O -
    paper_main_orientation_projector r O') <=
  2 * Num.sqrt r%:R *
    paper_main_frobenius (paper_main_orientation_frame r O - paper_main_orientation_frame r O').
Proof.
move=> Hrd HO HO'.
set W := paper_main_orientation_frame r O; set W' := paper_main_orientation_frame r O'.
have Ef : forall A : 'M[R]_d, paper_main_frobenius A ^+ 2 = r%:R ->
    paper_main_frobenius A = Num.sqrt r%:R.
  move=> A H; rewrite -H sqrtr_sqr ger0_norm //; exact: pmh_frobenius_ge0.
have EW := Ef W (paper_main_orientation_frame_frobenius r O Hrd HO).
have EW' := Ef W' (paper_main_orientation_frame_frobenius r O' Hrd HO').
rewrite !paper_main_orientation_frame_projector -/W -/W'.
have -> : W^T *m W - W'^T *m W' = W^T *m (W - W') + (W - W')^T *m W'.
  by rewrite mulmxBr linearB /= mulmxBl addrA subrK.
apply: le_trans (pmh_frobenius_triangle _ _ _) _.
have H1 := paper_main_frobenius_product d W^T (W - W').
have H2 := paper_main_frobenius_product d (W - W')^T W'.
rewrite paper_main_frobenius_transpose EW in H1.
rewrite paper_main_frobenius_transpose EW' in H2.
apply: le_trans (lerD H1 H2) _.
have E : forall a b : R, a * b + b * a = 2 * a * b.
  by move=> a b; rewrite -mulrA mulr_natl mulr2n [b * a]mulrC.
by rewrite E.
Qed.

(* 3. The code of the head frame in r d coordinates. *)

Definition paper_main_orientation_code (r d : nat) (O : 'M[R]_d) (k : nat) : R :=
  (paper_main_orientation_entry O (k %/ d) (k %% d) / sqrt (INR r))%Rcoq.

Lemma paper_main_orientation_frame_sqsum {d : nat} (r : nat) (A : 'M[R]_d) :
  (r <= d)%N ->
  paper_main_frobenius (paper_main_orientation_frame r A) ^+ 2 =
  finite_sum (fun i => finite_sum (fun q =>
    (paper_main_orientation_entry A i q * paper_main_orientation_entry A i q)%Rcoq)
    (List.seq 0 d)) (List.seq 0 r).
Proof.
move=> Hrd.
rewrite pmh_frobenius_sqr /paper_main_pairing /paper_main_orientation_frame mul_diag_mx.
rewrite finite_sum_seqE.
under [RHS]eq_bigr do rewrite finite_sum_seqE.
rewrite (big_ord_widen d (fun i => \sum_(q < d) (paper_main_orientation_entry A i q *
  paper_main_orientation_entry A i q)%Rcoq) Hrd).
rewrite big_mkcond /=.
rewrite [RHS]big_mkcond /=.
apply: eq_bigr => i _.
case Hir: (i < r)%N.
  apply: eq_bigr => j _; rewrite !mxE Hir mul1r !paper_main_orientation_entry_ord.
  by rewrite RmultE.
by rewrite big1 // => j _; rewrite !mxE Hir mul0r mul0r.
Qed.

Lemma paper_main_orientation_entryB {d : nat} (O O' : 'M[R]_d) (i j : nat) :
  paper_main_orientation_entry (O - O') i j =
  (paper_main_orientation_entry O i j - paper_main_orientation_entry O' i j)%Rcoq.
Proof.
rewrite /paper_main_orientation_entry.
case: insubP => [a _ _|_]; last by rewrite Rminus_0_r.
case: insubP => [b _ _|_]; last by rewrite Rminus_0_r.
by rewrite !mxE RminusE.
Qed.

Lemma paper_main_orientation_code_dist (r d : nat) (O O' : 'M[R]_d) :
  (0 < r)%N -> (r <= d)%N ->
  paper_main_gordon_dot (r * d)
    (fun k => (paper_main_orientation_code r d O k - paper_main_orientation_code r d O' k)%Rcoq)
    (fun k => (paper_main_orientation_code r d O k - paper_main_orientation_code r d O' k)%Rcoq) =
  (paper_main_frobenius (paper_main_orientation_frame r (O - O')) ^+ 2 / INR r)%Rcoq.
Proof.
move=> Hr Hrd.
have Hrpos : (0 < INR r)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have Hsq : (sqrt (INR r) * sqrt (INR r) = INR r)%Rcoq by apply: sqrt_sqrt; lra.
have Hs0 : (sqrt (INR r) <> 0)%Rcoq by apply: Rgt_not_eq; apply: sqrt_lt_R0.
rewrite (paper_main_orientation_frame_sqsum r (O - O') Hrd).
rewrite /paper_main_gordon_dot paper_main_orientation_block_sum.
transitivity (finite_sum (fun i => finite_sum (fun q => / INR r *
   (paper_main_orientation_entry (O - O') i q * paper_main_orientation_entry (O - O') i q))
   (List.seq 0 d)) (List.seq 0 r))%Rcoq.
  apply: finite_sum_ext => i Hi; apply: finite_sum_ext => q Hq.
  have Hqd : (q < d)%N by apply/ssrnat.ltP; have := proj2 (proj1 (List.in_seq _ _ _) Hq); lia.
  have [Ea Eb] := paper_main_orientation_divmod i q d Hqd.
  have E : forall a b s : R, s <> 0%Rcoq ->
      ((a / s - b / s) * (a / s - b / s) = / (s * s) * ((a - b) * (a - b)))%Rcoq.
    by move=> a b s Hs; field.
  rewrite /paper_main_orientation_code Ea Eb paper_main_orientation_entryB (E _ _ _ Hs0) Hsq.
  by [].
rewrite (finite_sum_ext _ _ _ (fun i _ => finite_sum_scale _ _ _)) finite_sum_scale.
by rewrite Rmult_comm.
Qed.

Lemma paper_main_orientation_code_norm (r d : nat) (O : 'M[R]_d) :
  (0 < r)%N -> (r <= d)%N -> O^T *m O = 1%:M ->
  paper_main_gordon_dot (r * d) (paper_main_orientation_code r d O)
    (paper_main_orientation_code r d O) = 1%Rcoq.
Proof.
move=> Hr Hrd HO.
have Hrpos : (0 < INR r)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
have H := paper_main_orientation_code_dist r d O 0 Hr Hrd.
have E0 : (fun k => (paper_main_orientation_code r d O k -
    paper_main_orientation_code r d 0 k)%Rcoq) = paper_main_orientation_code r d O.
  apply: funext => k.
  rewrite /paper_main_orientation_code /paper_main_orientation_entry.
  case: insubP => [a _ _|_]; last by rewrite /Rdiv Rmult_0_l Rminus_0_r.
  case: insubP => [b _ _|_]; last by rewrite /Rdiv Rmult_0_l Rminus_0_r.
  by rewrite mxE /Rdiv Rmult_0_l Rminus_0_r.
rewrite E0 subr0 (paper_main_orientation_frame_frobenius r O Hrd HO) in H.
rewrite H -INRE; field; lra.
Qed.

(* 4. The orientation net. *)

Definition paper_main_orientation_entropy (r : nat) (tau : R) : R :=
  ((4 + 8 * INR r / tau) * ln 2 * INR (r + 1))%Rcoq.

Theorem paper_main_orientation_net (r d : nat) (tau : R) :
  (r <= d)%N -> (0 < tau)%Rcoq ->
  exists (s : nat) (Os : nat -> 'M[R]_d),
    (0 < s)%N /\
    (forall k, (k < s)%N -> (Os k)^T *m Os k = 1%:M) /\
    (forall O : 'M[R]_d, O^T *m O = 1%:M ->
       exists k, (k < s)%N /\
         paper_main_frobenius (paper_main_orientation_projector r O -
           paper_main_orientation_projector r (Os k)) <= tau) /\
    (ln (INR s) <= paper_main_orientation_entropy r tau * INR (d + 1))%Rcoq.
Proof.
move=> Hrd Ht.
have Hln2 : (0 < ln 2)%Rcoq by rewrite -ln_1; apply: ln_increasing; lra.
have Hent0 : forall r', (0 <= paper_main_orientation_entropy r' tau)%Rcoq.
  move=> r'; rewrite /paper_main_orientation_entropy.
  have H1 : (0 <= 8 * INR r' / tau)%Rcoq.
    apply: Rmult_le_pos; [apply: Rmult_le_pos; [lra|exact: pos_INR]|].
    by apply: Rlt_le; apply: Rinv_0_lt_compat.
  apply: Rmult_le_pos; [apply: Rmult_le_pos; lra|exact: pos_INR].
case: (posnP r) => [Hr0|Hr].
  exists 1%N, (fun _ => 1%:M); split => //; split.
    by move=> k _; rewrite trmx1 mulmx1.
  split.
    move=> O HO; exists 0%N; split => //.
    have P0 : forall O' : 'M[R]_d, paper_main_orientation_projector r O' = 0.
      move=> O'; rewrite /paper_main_orientation_projector.
      have -> : diag_mx (paper_main_orientation_mask r) = 0 :> 'M[R]_d.
        by apply/matrixP => i j; rewrite !mxE Hr0 ltn0 mul0rn.
      by rewrite mulmx0 mul0mx.
    rewrite !P0 subr0 pmh_frobenius0; exact/RleP/Rlt_le.
  rewrite /= ln_1.
  by apply: Rmult_le_pos; [exact: Hent0|exact: pos_INR].
have HrR : (0 < INR r)%Rcoq by apply: lt_0_INR; apply/ssrnat.ltP.
set eps := (tau / (2 * INR r))%Rcoq.
have Heps : (0 < eps)%Rcoq by apply: Rdiv_lt_0_compat; lra.
set T := fun u : nat -> R => exists O : 'M[R]_d, O^T *m O = 1%:M /\
  u = paper_main_orientation_code r d O.
have HT0 : exists u, T u.
  by exists (paper_main_orientation_code r d 1%:M), 1%:M; split; [rewrite trmx1 mulmx1|].
have HT1 : forall u, T u -> (paper_main_gordon_dot (r * d) u u <= 1)%Rcoq.
  by move=> u [O [HO ->]]; rewrite paper_main_orientation_code_norm //; lra.
have [s [v [Hs [[Hin Hcov] Hcard]]]] := paper_main_loss_ball_net (r * d) T eps Heps HT0 HT1.
set Os := fun t => epsilon (inhabits (1%:M : 'M[R]_d))
  (fun O => O^T *m O = 1%:M /\ v t = paper_main_orientation_code r d O).
have HOs : forall t, List.In t (List.seq 0 s) ->
    (Os t)^T *m Os t = 1%:M /\ v t = paper_main_orientation_code r d (Os t).
  move=> t Ht'.
  apply: (epsilon_spec (inhabits (1%:M : 'M[R]_d))
    (fun O : 'M[R]_d => O^T *m O = 1%:M /\ v t = paper_main_orientation_code r d O)).
  by have [O [HO E]] := Hin t Ht'; exists O.
have Hseq : forall t, (t < s)%N -> List.In t (List.seq 0 s).
  by move=> t /ssrnat.ltP Hts; apply/List.in_seq; lia.
exists s, Os; split; first by apply/ssrnat.ltP.
split; first by move=> k Hk; exact: (HOs k (Hseq k Hk)).1.
split.
  move=> O HO.
  have HTO : T (paper_main_orientation_code r d O) by exists O.
  have [t [Ht' Hd]] := Hcov _ HTO.
  have [HOt Evt] := HOs t Ht'.
  exists t; split.
    by apply/ssrnat.ltP; have := proj2 (proj1 (List.in_seq _ _ _) Ht'); lia.
  rewrite Evt (paper_main_orientation_code_dist r d O (Os t) Hr Hrd) in Hd.
  have Hframe : paper_main_orientation_frame r (O - Os t) =
      paper_main_orientation_frame r O - paper_main_orientation_frame r (Os t).
    by rewrite /paper_main_orientation_frame mulmxBr.
  rewrite Hframe in Hd.
  set f := paper_main_frobenius (paper_main_orientation_frame r O -
    paper_main_orientation_frame r (Os t)) in Hd *.
  have Hf0 : (0 <= f)%Rcoq by apply/RleP; exact: pmh_frobenius_ge0.
  have Hf2 : (f * f <= INR r * eps ^ 2)%Rcoq.
    have E2 : f ^+ 2 = (f * f)%Rcoq by rewrite expr2 RmultE.
    rewrite E2 in Hd.
    have H := Rmult_le_compat_l (INR r) _ _ (Rlt_le _ _ HrR) Hd.
    have E3 : (INR r * (f * f / INR r) = f * f)%Rcoq by field; lra.
    by rewrite E3 in H.
  have Hsr := sqrt_pos (INR r).
  have Hss : (sqrt (INR r) * sqrt (INR r) = INR r)%Rcoq by apply: sqrt_sqrt; lra.
  have Hf : (f <= sqrt (INR r) * eps)%Rcoq.
    apply: Rnot_lt_le => Hlt.
    have Hp : (0 <= sqrt (INR r) * eps)%Rcoq by apply: Rmult_le_pos; lra.
    have : (sqrt (INR r) * eps * (sqrt (INR r) * eps) < f * f)%Rcoq.
      by apply: Rmult_le_0_lt_compat.
    have -> : (sqrt (INR r) * eps * (sqrt (INR r) * eps) = INR r * eps ^ 2)%Rcoq.
      have E : forall a b : R, (a * b * (a * b) = (a * a) * b ^ 2)%Rcoq by move=> a b; ring.
      by rewrite E Hss.
    lra.
  apply: le_trans (paper_main_orientation_projector_dist r O (Os t) Hrd HO HOt) _.
  rewrite -/f -INRE -RsqrtE; apply/RleP.
  have E4 : (2 * sqrt (INR r) * (sqrt (INR r) * eps) = tau)%Rcoq.
    have E : forall a b : R, (2 * a * (a * b) = 2 * (a * a) * b)%Rcoq by move=> a b; ring.
    rewrite E Hss /eps; field; lra.
  rewrite -RmultE -RmultE.
  have := Rmult_le_compat_l (2 * sqrt (INR r)) _ _ ltac:(lra) Hf.
  move=> H; rewrite -(INRE r) (INR_IZR_INZ 2) /=; lra.
apply: Rle_trans Hcard _.
rewrite /paper_main_gordon_entropy_constant /paper_main_orientation_entropy.
have E5 : (4 / eps = 8 * INR r / tau)%Rcoq by rewrite /eps; field; lra.
rewrite E5.
have H8 : (0 <= 8 * INR r / tau)%Rcoq.
  apply: Rmult_le_pos; [apply: Rmult_le_pos; [lra|exact: pos_INR]|].
  by apply: Rlt_le; apply: Rinv_0_lt_compat.
have HK : (0 <= (4 + 8 * INR r / tau) * ln 2)%Rcoq by apply: Rmult_le_pos; lra.
have Hb : (INR (r * d).+1 <= INR (r + 1) * INR (d + 1))%Rcoq.
  rewrite -mult_INR; apply: le_INR.
  rewrite -?multE -?plusE; nia.
have := Rmult_le_compat_l _ _ _ HK Hb.
lra.
Qed.
