(* The public head features and the explicit form of the head correction,
   with its Loewner slack (manuscript lem:head-correction-bounds: the
   residuals r_i above the lemma, eq:EJ-formula and eq:EJ-op, lines
   1024-1035).

   For a sample x of n points of R^d (paper_main_point), the feature of the
   point i is W_i = (x_i x_i^T - I) / sqrt d (paper_main_head_feature). Then
   <W_i, S> = (x_i^T S x_i - Tr S) / sqrt d, so <W_i, S> = 0 gives
   x_i^T S x_i = Tr S, with equivalence for d > 0. For a head s and
   coefficients a, the correction of PaperMainGeometryHeadCorrection is
   E = -(X_J diag(a) X_J^T - (sum_k a_k) I) / sqrt d (eq:EJ-formula), where
   X_J diag(a) X_J^T = sum_k a_k x_(s k) x_(s k)^T. If |a_k| <= A_inf,
   sum_k |a_k| <= A_1 and X_J X_J^T <= lam I, then -delta I <= E <= delta I
   for every delta >= (A_inf lam + A_1) / sqrt d (the Loewner form of
   eq:EJ-op). paper_main_head_feature_close combines this with
   paper_main_head_correction_close.

   The coefficient bounds and the data bound X_J X_J^T <= lam I are
   hypotheses: in the paper they come from the data event (eq:sparse-norms,
   eq:aJ-l1, eq:aJ-linf), which is not proved here. For d = 0 every feature
   is 0 (paper_main_head_feature_dim0), and the other results hold without
   a dimension hypothesis. Nothing from the paper is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* W_i = (x_i x_i^T - I) / sqrt d. *)
Definition paper_main_head_feature {n d : nat} (x : paper_main_sample n d) (i : nat) :
    'M[R]_d :=
  (Num.sqrt d%:R)^-1 *: (paper_main_point x i *m (paper_main_point x i)^T - 1%:M).

(* X_J X_J^T = sum_k x_(s k) x_(s k)^T for a head s. *)
Definition paper_main_head_data_gram {n d m : nat} (x : paper_main_sample n d)
    (s : 'I_m -> 'I_n) : 'M[R]_d :=
  \sum_(k < m) paper_main_point x (s k) *m (paper_main_point x (s k))^T.

Lemma paper_main_head_feature_dim0 n (x : paper_main_sample n 0) (i : nat) :
  paper_main_head_feature x i = 0.
Proof. by apply/matrixP => -[]. Qed.

Section Features.
Variables (n d : nat) (x : paper_main_sample n d).
Implicit Types (A B S P Z : 'M[R]_d) (v : 'cV[R]_d).

Lemma pmh_pairing_id S : paper_main_pairing 1%:M S = paper_main_trace S.
Proof.
rewrite /paper_main_pairing /paper_main_trace; apply: eq_bigr => i _.
rewrite (bigD1 i) //=.
have -> : \sum_(j < d | j != i) (1%:M : 'M[R]_d) i j * S i j = 0.
  by apply: big1 => j Hj; rewrite mxE eq_sym (negbTE Hj) mul0r.
by rewrite addr0 mxE eqxx mul1r.
Qed.

Lemma pmh_form0 v : paper_main_quadratic_form (0 : 'M[R]_d) v = 0.
Proof.
rewrite /paper_main_quadratic_form big1 // => i _; rewrite big1 // => j _.
by rewrite mxE mulr0 mul0r.
Qed.

Lemma pmh_form_sumr m (F : 'I_m -> 'M[R]_d) v :
  paper_main_quadratic_form (\sum_(k < m) F k) v =
  \sum_(k < m) paper_main_quadratic_form (F k) v.
Proof.
exact: (big_morph (fun S => paper_main_quadratic_form S v)
  (fun S M => pms_formD _ S M v) (pmh_form0 v)).
Qed.

Lemma pmh_formN S v : paper_main_quadratic_form (- S) v = - paper_main_quadratic_form S v.
Proof. by rewrite -scaleN1r paper_main_form_scale mulN1r. Qed.

Lemma pmh_symmetricB A B :
  paper_main_symmetric A -> paper_main_symmetric B -> paper_main_symmetric (A - B).
Proof. by move=> HA HB i j; rewrite !mxE HA HB. Qed.

Lemma pmh_symmetric_id : paper_main_symmetric (1%:M : 'M[R]_d).
Proof. by have [] := pmh_psd_id d. Qed.

Lemma paper_main_head_feature_symmetric (i : nat) :
  paper_main_symmetric (paper_main_head_feature x i).
Proof.
apply: paper_main_symmetric_scale; apply: pmh_symmetricB; last exact: pmh_symmetric_id.
by have [] := paper_main_psd_rank1 _ (paper_main_point x i).
Qed.

(* r_i = <W_i, S> = (x_i^T S x_i - Tr S) / sqrt d. *)
Theorem paper_main_head_feature_pairing (i : nat) S :
  paper_main_pairing (paper_main_head_feature x i) S =
  (Num.sqrt d%:R)^-1 *
    (paper_main_quadratic_form S (paper_main_point x i) - paper_main_trace S).
Proof.
rewrite /paper_main_head_feature pmh_pairingZl pmh_pairingBl pmh_pairing_id.
by rewrite paper_main_pairingC paper_main_pairing_outer.
Qed.

Theorem paper_main_head_feature_kernel (i : nat) S :
  paper_main_pairing (paper_main_head_feature x i) S = 0 ->
  paper_main_quadratic_form S (paper_main_point x i) = paper_main_trace S.
Proof.
rewrite paper_main_head_feature_pairing => H.
have [Hd|Hd] := posnP d.
  have E0 : forall F : 'I_d -> R, \sum_(j < d) F j = 0.
    move=> F; apply: big1 => -[j Hj] _ /=.
    by exfalso; move: Hj; rewrite Hd ltn0.
  by rewrite /paper_main_quadratic_form /paper_main_trace !E0.
have Hc : (Num.sqrt d%:R)^-1 != 0 :> R by rewrite invr_eq0 sqrtr_eq0 -ltNge ltr0n.
by move/eqP: H; rewrite mulf_eq0 (negbTE Hc) /= subr_eq0 => /eqP.
Qed.

Theorem paper_main_head_feature_kernelP (i : nat) S :
  (0 < d)%N ->
  (paper_main_pairing (paper_main_head_feature x i) S = 0 <->
   paper_main_quadratic_form S (paper_main_point x i) = paper_main_trace S).
Proof.
move=> Hd; split; first exact: paper_main_head_feature_kernel.
by move=> H; rewrite paper_main_head_feature_pairing H subrr mulr0.
Qed.

(* eq:EJ-formula. *)
Theorem paper_main_head_feature_correction m (s : 'I_m -> 'I_n) (a : 'cV[R]_m) :
  paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a =
  - ((Num.sqrt d%:R)^-1 *:
      (\sum_(k < m) a k 0 *: (paper_main_point x (s k) *m (paper_main_point x (s k))^T)
       - (\sum_(k < m) a k 0) *: 1%:M)).
Proof.
rewrite /paper_main_head_correction /paper_main_head_feature; congr (- _).
rewrite scaler_suml -sumrB scaler_sumr; apply: eq_bigr => k _.
by rewrite -scalerBr !scalerA mulrC.
Qed.

Lemma pmh_feature_correction_form m (s : 'I_m -> 'I_n) (a : 'cV[R]_m) v :
  paper_main_quadratic_form
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a) v =
  - ((Num.sqrt d%:R)^-1 *
      (\sum_(k < m) a k 0 * paper_main_quadratic_form
         (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v
       - (\sum_(k < m) a k 0) * (v^T *m v) 0 0)).
Proof.
rewrite paper_main_head_feature_correction pmh_formN paper_main_form_scale pms_formB.
by rewrite pms_form_sum paper_main_form_scale pmh_form_id.
Qed.

(* The Loewner form of eq:EJ-op. *)
Theorem paper_main_head_feature_slack m (s : 'I_m -> 'I_n) (a : 'cV[R]_m)
    (A_inf A_1 lam delta : R) :
  0 <= A_inf -> (forall k, `|a k 0| <= A_inf) -> \sum_(k < m) `|a k 0| <= A_1 ->
  paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  (Num.sqrt d%:R)^-1 * (A_inf * lam + A_1) <= delta ->
  paper_main_loewner_le ((- delta) *: 1%:M)
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a) /\
  paper_main_loewner_le
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a)
    (delta *: 1%:M).
Proof.
move=> HA0 HA HA1 Hlam Hdel.
have HEs : paper_main_symmetric
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a).
  apply: paper_main_head_correction_symmetric => k.
  exact: paper_main_head_feature_symmetric.
have Hc : 0 <= (Num.sqrt d%:R)^-1 :> R by rewrite invr_ge0 sqrtr_ge0.
have Hbound : forall v, `|paper_main_quadratic_form
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a) v| <=
    delta * (v^T *m v) 0 0.
  move=> v.
  have Hv : 0 <= (v^T *m v) 0 0.
    by rewrite -pmh_form_id; case: (pmh_psd_id d) => _; apply.
  have Hq : forall k, 0 <= paper_main_quadratic_form
      (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v.
    by move=> k; case: (paper_main_psd_rank1 _ (paper_main_point x (s k))) => _; apply.
  have HX : \sum_(k < m) paper_main_quadratic_form
      (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v <=
      lam * (v^T *m v) 0 0.
    case: Hlam => _ /(_ v).
    rewrite pms_formB paper_main_form_scale pmh_form_id /paper_main_head_data_gram.
    by rewrite pmh_form_sumr subr_ge0.
  have H1 : `|\sum_(k < m) a k 0 * paper_main_quadratic_form
      (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v| <=
      A_inf * \sum_(k < m) paper_main_quadratic_form
      (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v.
    apply: le_trans (ler_norm_sum _ _ _) _.
    rewrite mulr_sumr; apply: ler_sum => k _.
    rewrite normrM (ger0_norm (Hq k)).
    exact: (ler_wpM2r (Hq k) (HA k)).
  have H2 : `|\sum_(k < m) a k 0| <= A_1 by apply: le_trans (ler_norm_sum _ _ _) HA1.
  have H4 := ler_wpM2l HA0 HX.
  have H5 := ler_wpM2r Hv H2.
  have H3 : `|\sum_(k < m) a k 0 * paper_main_quadratic_form
      (paper_main_point x (s k) *m (paper_main_point x (s k))^T) v -
      (\sum_(k < m) a k 0) * (v^T *m v) 0 0| <= (A_inf * lam + A_1) * (v^T *m v) 0 0.
    apply: le_trans (ler_normD _ _) _.
    rewrite normrN normrM (ger0_norm Hv).
    lra.
  rewrite pmh_feature_correction_form normrN normrM (ger0_norm Hc).
  have H6 := ler_wpM2l Hc H3.
  have H7 := ler_wpM2r Hv Hdel.
  lra.
split.
- split; first by apply: pmh_symmetricB => // i j; rewrite !mxE eq_sym.
  move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id.
  have := Hbound v; rewrite ler_norml => /andP [H _]; lra.
- split; first by apply: pmh_symmetricB => // i j; rewrite !mxE eq_sym.
  move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id.
  have := Hbound v; rewrite ler_norml => /andP [_ H]; lra.
Qed.

(* The deterministic eq:PJ-close on the public features: exact correction,
   unit norm, the public kernel equations x_(s k)^T Pt x_(s k) = Tr Pt,
   closeness, support transfer and the bounded-condition form. *)
Theorem paper_main_head_feature_close m (s : 'I_m -> 'I_n) (P Z : 'M[R]_d)
    (a : 'cV[R]_m) (eta lm lp kappa A_inf A_1 lam delta : R) :
  paper_main_head_gram (fun k => paper_main_head_feature x (s k)) *m a =
    paper_main_head_residual (fun k => paper_main_head_feature x (s k)) P ->
  paper_main_frobenius P = 1 ->
  paper_main_frobenius
    (paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a) <= eta ->
  eta < 1 ->
  0 <= A_inf -> (forall k, `|a k 0| <= A_inf) -> \sum_(k < m) `|a k 0| <= A_1 ->
  paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  (Num.sqrt d%:R)^-1 * (A_inf * lam + A_1) <= delta ->
  delta < lm -> lp + delta <= kappa * (lm - delta) ->
  paper_main_loewner_le (lm *: 1%:M) P -> paper_main_loewner_le P (lp *: 1%:M) ->
  let Pt := paper_main_head_normalize
    (P + paper_main_head_correction (fun k => paper_main_head_feature x (s k)) a) in
  [/\ paper_main_head_condition kappa Pt, paper_main_frobenius Pt = 1,
      (forall k : 'I_m, paper_main_quadratic_form Pt (paper_main_point x (s k)) =
         paper_main_trace Pt),
      paper_main_frobenius (Pt - P) <= 2 * eta &
      paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <= paper_main_pairing Z Pt].
Proof.
move=> Ha HP HE Heta HA0 HA HA1 Hlam Hdel Hd Hk H1 H2 Pt.
have [S1 S2] := paper_main_head_feature_slack _ _ _ _ _ _ _ HA0 HA HA1 Hlam Hdel.
have [C U K Cl T] := paper_main_head_correction_close _ _ _ _ Z _ _ _ _ _ _
  Ha HP HE Heta Hd Hk H1 H2 S1 S2.
split => // k.
exact: paper_main_head_feature_kernel (K k).
Qed.

End Features.
