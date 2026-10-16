From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets functions reals topology normedtype.
From mathcomp Require Import measure lebesgue_stieltjes_measure measurable_realfun.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral nuclear condition_cone psd_part psd_splitting psd_duality.
From GaussianAnalysis.convex Require Import image_projection logdet_barrier.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
(**md**************************************************************************)
(* # Positive semidefinite residual geometry                                  *)
(*                                                                            *)
(* psd_trace_vectors tau is the PSD trace-tau slice in vector coordinates.     *)
(* psd_residual_projection tau A is the closest image point of that slice;    *)
(* psd_residual_direction tau A is its normalized direction, zero at zero.    *)
(* psd_residual_adjoint A y unvectorizes the adjoint image y A^T.             *)
(* Symmetric columns make this adjoint symmetric. The projection inequality  *)
(* bounds it below by (|projection|_F / tau) I when tau > 0.                  *)
(* Directions annihilate every vector in the kernel of A.                    *)
(* This module is deterministic and contains no probability or sample model. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section Kernel.
Context {R : realType} {m n : nat}.
Lemma image_projection_kernel (K : set 'rV[R]_m) (A : 'M[R]_(m,n)) (v : 'cV[R]_n) :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 -> K (x+t*:(y-x))) ->
  A *m v = 0 -> image_projection K A *m v = 0.
Proof.
move=> Kcp K0 Kcvx Av.
have [[x Kx <-] _] := image_projectionP A Kcp K0 Kcvx.
by rewrite -mulmxA Av mulmx0.
Qed.
Lemma image_direction_kernel (K : set 'rV[R]_m) (A : 'M[R]_(m,n)) (v : 'cV[R]_n) :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 -> K (x+t*:(y-x))) ->
  A *m v = 0 -> image_direction K A *m v = 0.
Proof.
move=> Kcp K0 Kcvx Av.
by rewrite /image_direction -scalemxAl (image_projection_kernel Kcp K0 Kcvx Av) scaler0.
Qed.
Lemma image_direction_sum0 (K : set 'rV[R]_m) (A : 'M[R]_(m,n)) :
  compact K -> K !=set0 ->
  (forall x y (t : R), K x -> K y -> 0 <= t <= 1 -> K (x+t*:(y-x))) ->
  A *m (\col_(_ < n) 1) = 0 -> \sum_(j < n) image_direction K A 0 j = 0.
Proof.
move=> Kcp K0 Kcvx A1.
have := congr1 (fun M : 'M[R]_1 => M 0 0)
  (image_direction_kernel Kcp K0 Kcvx A1).
rewrite !mxE.
by under eq_bigr do rewrite mxE mulr1.
Qed.
End Kernel.

Section PsdTraceSlice.
Context {R : realType} {d : nat}.
Definition psd_trace_vectors (tau : R) : set 'rV[R]_(d*d) :=
  [set v | psdmx (vec_mx v) /\ \tr (vec_mx v) = tau].
Lemma psd_trace_vectors_bound (tau : R) (x : 'rV[R]_(d*d)) :
  psd_trace_vectors tau x -> frobenius x <= tau.
Proof.
move=> [xp <-].
rewrite /frobenius -mxdot_vec_mx.
exact: psdmx_frobenius_le_trace.
Qed.
Lemma psd_trace_vectors_bounded (tau : R) : bounded_set (psd_trace_vectors tau).
Proof.
exists tau; split; first exact: num_real.
move=> M tM x hx; apply: le_trans (ltW tM).
apply: le_trans (mx_norm_le_frobenius x) _.
exact: psd_trace_vectors_bound hx.
Qed.
Lemma psd_trace_vectors_closed (tau : R) : closed (psd_trace_vectors tau).
Proof.
have hs (c : 'rV[R]_(d*d)) : closed [set v | 0 <= mxdot v c].
  exact: ((continuous_closedP (fun v : 'rV[R]_(d*d) => mxdot v c)).1
    (@continuous_mxdotv _ _ c) _ (@closed_ge R 0)).
have he (c : 'rV[R]_(d*d)) : closed [set v | mxdot v c = tau].
  apply: (@preimage_closed _ _ (fun v : 'rV[R]_(d*d) => mxdot v c) [set tau]).
    by move=> x _; exact: continuous_mxdotv.
  exact: closed_eq.
pose E (ij : 'I_d * 'I_d) : 'M[R]_d := delta_mx ij.1 ij.2 - delta_mx ij.2 ij.1.
have pE (v : 'rV[R]_(d*d)) ij :
    mxdot v (mxvec (E ij)) = vec_mx v ij.1 ij.2 - vec_mx v ij.2 ij.1.
  by rewrite mxdotC -mxdot_vec_mxr mxdotC mxdotBr !mxdot_delta.
have tE (v : 'rV[R]_(d*d)) : \tr (vec_mx v) = mxdot v (mxvec 1%:M).
  by rewrite mxdotC -mxdot_vec_mxr mxdot_trace mul1mx mxtrace_tr.
have -> : psd_trace_vectors tau =
    (\bigcap_(ij in [set: 'I_d * 'I_d])
       ([set v | 0 <= mxdot v (mxvec (E ij))] `&`
        [set v | 0 <= mxdot v (- mxvec (E ij))])) `&`
    (\bigcap_(x in [set: 'cV[R]_d])
       [set v | 0 <= mxdot v (mxvec (x *m x^T))]) `&`
    [set v | mxdot v (mxvec 1%:M) = tau].
  apply/seteqP; split => v.
    move=> [[vs vp] vt]; split; first split.
    - move=> ij _; rewrite /= mxdotNr pE; have /symmetricmxP Ve := vs.
      have := congr1 (fun A : 'M[R]_d => A ij.2 ij.1) Ve; rewrite mxE => ->.
      by rewrite subrr oppr0 lexx.
    - by move=> x _; rewrite /= -mxdot_quad_vec.
    - by rewrite /= -tE.
  move=> [[HE Hx] Ht]; split; first split.
  - apply/symmetricmxP/matrixP => i j; rewrite mxE.
    have [h1 h2] := HE (j,i) I; move: h1 h2; rewrite /= mxdotNr pE /=.
    rewrite oppr_ge0 subr_ge0 subr_le0 => h1 h2.
    by apply/eqP; rewrite eq_le h1 h2.
  - by move=> x; rewrite mxdot_quad_vec; exact: Hx x I.
  - by rewrite tE.
apply: closedI; first apply: closedI.
- by apply: closed_bigI => ij _; apply: closedI; exact: hs.
- by apply: closed_bigI => x _; exact: hs.
- exact: he.
Qed.
Lemma psd_trace_vectors_compact (tau : R) : compact (psd_trace_vectors tau).
Proof. by apply: bounded_closed_compact; [exact: psd_trace_vectors_bounded | exact: psd_trace_vectors_closed]. Qed.
Lemma psd_trace_vectors_nonempty (tau : R) :
  (0 < d)%N -> 0 <= tau -> psd_trace_vectors tau !=set0.
Proof.
move=> d0 t0; exists (mxvec ((tau / d%:R)%:M : 'M[R]_d)).
rewrite /psd_trace_vectors /= mxvecK; split.
- split; first by apply/symmetricmxP; rewrite tr_scalar_mx.
  move=> x; rewrite mul_scalar_mx mxdotZr.
  by apply: mulr_ge0; rewrite ?divr_ge0 ?mxdot_ge0.
- by rewrite mxtrace_scalar -[(_ / _) *+ d]mulr_natr divfK // pnatr_eq0 -lt0n.
Qed.
Lemma psd_trace_vectors_convex (tau : R) (x y : 'rV[R]_(d*d)) (t : R) :
  psd_trace_vectors tau x -> psd_trace_vectors tau y -> 0 <= t <= 1 ->
  psd_trace_vectors tau (x + t *: (y-x)).
Proof.
move=> [xp xt] [yp yt] /andP[t0 t1]; split.
- rewrite linearD linearZ linearB /=.
  have -> : vec_mx x + t *: (vec_mx y - vec_mx x) =
      (1-t) *: vec_mx x + t *: vec_mx y.
    by rewrite scalerBr scalerBl scale1r addrAC addrA.
  by apply: psdmxD; apply: psdmxZ; rewrite ?subr_ge0.
- rewrite linearD linearZ linearB /= mxtraceD mxtraceZ raddfB /=.
  by rewrite xt yt subrr mulr0 addr0.
Qed.
End PsdTraceSlice.

Section ResidualAlgebra.
Context {R : realType} {d n : nat}.
Lemma vec_mx_adjoint_symmetric (A : 'M[R]_(d*d,n)) (y : 'rV[R]_n) :
  (forall i, (vec_mx ((col i A)^T) : 'M[R]_d) \is symmetricmx) ->
  (vec_mx (y *m A^T) : 'M[R]_d) \is symmetricmx.
Proof.
move=> As; apply/symmetricmxP.
rewrite mulmx_sum_row linear_sum /= linear_sum /=.
apply: eq_bigr => i _.
by rewrite !linearZ /= -tr_col (symmetricmxP _ (As i)).
Qed.
Lemma vec_mx_adjoint_pairing (A : 'M[R]_(d*d,n)) (y : 'rV[R]_n) (S : 'M[R]_d) :
  mxdot (vec_mx (y *m A^T)) S = mxdot y (mxvec S *m A).
Proof.
by rewrite mxdotC mxdot_vec_mxr -mxdot_mulmxr mxdotC.
Qed.
Lemma psd_trace_support_margin (tau a : R) (B : 'M[R]_d) :
  0 < tau -> B \is symmetricmx ->
  (forall S : 'M[R]_d, psdmx S -> \tr S = tau -> a <= mxdot B S) ->
  psdmx (B - (a / tau)%:M).
Proof.
move=> tau0 Bs h; split.
- apply/symmetricmxP; rewrite linearB /= (symmetricmxP _ Bs) tr_scalar_mx.
  done.
- move=> x.
  have [->|x0] := eqVneq x 0; first by rewrite mulmx0 mxdot0l.
  have xx0 : 0 < mxdot x x by rewrite mxdot_gt0.
  pose S := (tau / mxdot x x) *: (x *m x^T).
  have Sp : psdmx S.
    apply: psdmxZ; last exact: psdmx_outer.
    by rewrite divr_ge0 ?ltW.
  have St : \tr S = tau.
    by rewrite /S mxtraceZ -mxdot_trace divfK // gt_eqF.
  have := h S Sp St.
  rewrite /S mxdotZr mxdot_outer -mulmxA -mxdot_colE => hm.
  rewrite mulmxBl mul_scalar_mx mxdotBr mxdotZr subr_ge0.
  rewrite mulrAC ler_pdivlMr // in hm.
  by rewrite mulrAC ler_pdivrMr // [leRHS]mulrC.
Qed.
End ResidualAlgebra.

Section psd_residual.
Context {R : realType} {d N : nat}.
Definition psd_residual_projection (tau : R) (A : 'M[R]_(d*d,N)) :=
  image_projection (psd_trace_vectors tau) A.
Definition psd_residual_direction (tau : R) (A : 'M[R]_(d*d,N)) :=
  image_direction (psd_trace_vectors tau) A.

Definition psd_residual_adjoint (A : 'M[R]_(d*d,N)) (y : 'rV[R]_N) : 'M[R]_d :=
  vec_mx (y *m A^T).

Lemma psd_residual_adjoint_symmetric (A : 'M[R]_(d*d,N)) (y : 'rV[R]_N) :
  (forall j, vec_mx ((col j A)^T) \is symmetricmx) ->
  psd_residual_adjoint A y \is symmetricmx.
Proof. exact: vec_mx_adjoint_symmetric. Qed.

Lemma psd_residual_psd (tau : R) (A : 'M[R]_(d*d,N)) :
  (0 < d)%N -> 0 < tau ->
  (forall j, vec_mx ((col j A)^T) \is symmetricmx) ->
  psdmx (psd_residual_adjoint A (psd_residual_direction tau A) -
    (frobenius (psd_residual_projection tau A) / tau)%:M).
Proof.
move=> d0 tau0 As.
apply: psd_trace_support_margin => //.
  exact: psd_residual_adjoint_symmetric.
move=> S Sp St.
rewrite /psd_residual_adjoint vec_mx_adjoint_pairing.
apply: image_direction_support.
- exact: psd_trace_vectors_compact.
- exact: psd_trace_vectors_nonempty d0 (ltW tau0).
- exact: psd_trace_vectors_convex.
- by rewrite /psd_trace_vectors /= mxvecK.
Qed.

Lemma psd_residual_projection_continuous (tau : R) :
  (0 < d)%N -> 0 <= tau -> continuous (psd_residual_projection tau).
Proof.
move=> d0 tau0.
exact (image_projection_continuous (@psd_trace_vectors_compact R d tau)
  (@psd_trace_vectors_nonempty R d tau d0 tau0) (@psd_trace_vectors_convex R d tau)).
Qed.
Lemma psd_residual_projection_measurable (tau : R) :
  (0 < d)%N -> 0 <= tau ->
  measurable_fun [set: 'M[R]_(d*d,N)] (psd_residual_projection tau).
Proof.
move=> d0 tau0.
exact (image_projection_measurable (@psd_trace_vectors_compact R d tau)
  (@psd_trace_vectors_nonempty R d tau d0 tau0) (@psd_trace_vectors_convex R d tau)).
Qed.
Lemma psd_residual_direction_measurable (tau : R) :
  (0 < d)%N -> 0 <= tau ->
  measurable_fun [set: 'M[R]_(d*d,N)] (psd_residual_direction tau).
Proof.
move=> d0 tau0.
exact (image_direction_measurable (@psd_trace_vectors_compact R d tau)
  (@psd_trace_vectors_nonempty R d tau d0 tau0) (@psd_trace_vectors_convex R d tau)).
Qed.
Lemma psd_residual_sum0 (tau : R) (A : 'M[R]_(d*d,N)) :
  (0 < d)%N -> 0 < tau -> A *m (\col_(_ < N) 1) = 0 ->
  \sum_(j < N) psd_residual_direction tau A 0 j = 0.
Proof.
move=> d0 tau0.
exact (image_direction_sum0 (@psd_trace_vectors_compact R d tau)
  (@psd_trace_vectors_nonempty R d tau d0 (ltW tau0)) (@psd_trace_vectors_convex R d tau)).
Qed.
End psd_residual.

(* Example: in dimension one, the trace slice is a singleton. *)
Section psd_residual_scalar_example.
Context {R : realType}.
Lemma psd_trace_vectors_scalar (tau : R) : 0 <= tau ->
  @psd_trace_vectors R 1 tau = [set mxvec (tau%:M : 'M[R]_1)].
Proof.
move=> tau0; apply/seteqP; split=> x.
- move=> [_ ht].
  have hS : vec_mx x = tau%:M :> 'M[R]_1.
    apply/matrixP => i j; rewrite !ord1 !mxE eqxx mulr1n.
    by move: ht; rewrite /mxtrace big_ord1 mxE.
  by rewrite -[x]vec_mxK hS.
- move=> ->; rewrite /psd_trace_vectors /= mxvecK; split.
  + split; first by apply/symmetricmxP; rewrite tr_scalar_mx.
    move=> v; rewrite mul_scalar_mx mxdotZr.
    exact: mulr_ge0 tau0 (mxdot_ge0 v).
  + by rewrite mxtrace_scalar mulr1n.
Qed.
Lemma psd_residual_projection_scalar (tau : R) : 0 <= tau ->
  @psd_residual_projection R 1 1 tau 1%:M = mxvec (tau%:M : 'M[R]_1).
Proof.
move=> tau0; rewrite /psd_residual_projection (psd_trace_vectors_scalar tau0).
by rewrite image_projection_singleton mulmx1.
Qed.
Lemma psd_residual_direction_scalar (tau : R) : 0 < tau ->
  @psd_residual_direction R 1 1 tau 1%:M = mxvec (1%:M : 'M[R]_1).
Proof.
move=> tau0.
rewrite /psd_residual_direction /image_direction.
have hz := psd_residual_projection_scalar (ltW tau0).
rewrite /psd_residual_projection in hz; rewrite hz.
have ht : frobenius (mxvec (tau%:M : 'M[R]_1)) = tau.
  by rewrite frobenius_mxvec /frobenius /mxdot !big_ord1 !mxE eqxx !mulr1n -expr2 sqrtr_sqr ger0_norm ?ltW.
by rewrite ht -(@mxvec_is_scalable R 1 1 tau^-1 (tau%:M))
  scale_scalar_mx mulVf ?gt_eqF.
Qed.
End psd_residual_scalar_example.
