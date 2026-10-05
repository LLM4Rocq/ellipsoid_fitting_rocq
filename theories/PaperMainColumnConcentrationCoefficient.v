(* The coefficient error in the non-backtracking column remainder (A36).

   The middle term of paper_main_column_remainder_split is
     sum_c ((Q_c^p - N^p) *: R_c),  R_c = pmcr_rankone N C X c, Q_c = pmcr_column_norm N C X c.
   1. Generic weighted rank-one sums. If the Gram form satisfies
      u^T (sum_c R_c) u <= U |u|^2 with U >= 0, e >= 0, and for every c either
      R_c = 0 or |a_c| <= e, then |u^T (sum_c a_c R_c) u| <= e U |u|^2, since
      u^T R_c u >= 0. The sum is symmetric, so -e U I <= sum_c a_c R_c <= e U I,
      and paper_main_cone_opnorm_of_loewner with paper_main_opnorm_to_action
      give pmlo_opb N (sum_c a_c *: R_c) (e U). The zero alternative covers
      inactive columns, whose coefficient may be large.
   2. Normalized powers. For x >= 0, 0 <= delta <= 1 and |x - 1| <= delta,
      |x^p - 1| <= (2^p - 1) delta, by x^(p+1) - 1 = x (x^p - 1) + (x - 1)
      and x <= 2. Hence |Q^p - N^p| <= N^p (2^p - 1) delta when N > 0 and
      |Q / N - 1| <= delta.
   3. For X = pmnb_X d (tval x) under paper_main_column_frame_good with
      0 < delta <= 1 and N > 0, active columns have |Q_q / N - 1| <= delta and
      inactive columns have R_q = 0, so for every p
        pmlo_opb N (sum_q ((Q_q^p - N^p) *: R_q)) (N^p (2^p - 1) delta (C0 N)).
   Deterministic; no probability premise. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadCorrection PaperMainGeometrySeparation
  PaperMainConeConditionOperator PaperMainMatrixOperatorTransport PaperMainSquarefreeEdgeLower
  PaperMainColumnRemainder PaperMainMatrixFamilyCauchy PaperMainColumnRemainderBounds
  PaperMainSquarefreeWalkNB PaperMainColumnConcentrationFrameEvents PaperMainColumnConcentrationFrame.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. Generic weighted rank-one sums. *)
Lemma pmccc_weighted_form N (C : finType) (X : 'I_N -> C -> R) (a : C -> R) (u : 'cV[R]_N) :
  (u^T *m (\sum_c a c *: pmcr_rankone N C X c) *m u) 0 0 =
  \sum_c a c * (u^T *m pmcr_rankone N C X c *m u) 0 0.
Proof.
rewrite mulmx_sumr mulmx_suml summxE; apply: eq_bigr => c _.
by rewrite -scalemxAr -scalemxAl mxE.
Qed.

Lemma pmccc_weighted_symmetric N (C : finType) (X : 'I_N -> C -> R) (a : C -> R) :
  paper_main_symmetric (\sum_c a c *: pmcr_rankone N C X c).
Proof.
move=> i j; rewrite !summxE; apply: eq_bigr => c _.
by rewrite /pmcr_rankone !mxE [X i c * _]mulrC.
Qed.

Lemma pmccc_weighted_form_bound N (C : finType) (X : 'I_N -> C -> R) (a : C -> R) (U e : R) :
  0 <= e ->
  (forall u : 'cV[R]_N, (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= U * (u^T *m u) 0 0) ->
  (forall c, pmcr_rankone N C X c = 0 \/ `|a c| <= e) ->
  forall u : 'cV[R]_N,
    `|(u^T *m (\sum_c a c *: pmcr_rankone N C X c) *m u) 0 0| <= e * U * (u^T *m u) 0 0.
Proof.
move=> He HG Ha u; rewrite pmccc_weighted_form.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_c e * (u^T *m pmcr_rankone N C X c *m u) 0 0 <= _).
  apply: ler_sum => c _; rewrite normrM (ger0_norm (pmcr_rankone_positive N C X c u)).
  case: (Ha c) => [H0 | Hac].
    by rewrite H0 mulmx0 mul0mx mxE !mulr0.
  by apply: ler_wpM2r => //; exact: pmcr_rankone_positive.
have E : \sum_c (u^T *m pmcr_rankone N C X c *m u) 0 0 =
    (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0.
  by rewrite mulmx_sumr mulmx_suml summxE.
by rewrite -mulr_sumr E -mulrA; apply: ler_wpM2l => //; exact: HG.
Qed.

(* A symmetric matrix with a two-sided form bound lies in the Loewner box. *)
Lemma pmccc_box N (S : 'M[R]_N) (b : R) :
  paper_main_symmetric S -> (forall v : 'cV[R]_N, `|(v^T *m S *m v) 0 0| <= b * (v^T *m v) 0 0) ->
  paper_main_loewner_le ((- b) *: 1%:M) S /\ paper_main_loewner_le S (b *: 1%:M).
Proof.
move=> HS Hf; split; split.
- by move=> i j; rewrite !mxE (HS i j) eq_sym.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
  by have := Hf v; rewrite ler_norml => /andP [H1 _]; lra.
- by move=> i j; rewrite !mxE (HS i j) eq_sym.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id paper_main_quadratic_formE.
  by have := Hf v; rewrite ler_norml => /andP [_ H2]; lra.
Qed.

Theorem paper_main_weighted_rankone_opbound N (C : finType) (X : 'I_N -> C -> R) (a : C -> R) (U e : R) :
  0 <= U -> 0 <= e ->
  (forall u : 'cV[R]_N, (u^T *m (\sum_c pmcr_rankone N C X c) *m u) 0 0 <= U * (u^T *m u) 0 0) ->
  (forall c, pmcr_rankone N C X c = 0 \/ `|a c| <= e) ->
  pmlo_opb N (\sum_c a c *: pmcr_rankone N C X c) (e * U).
Proof.
move=> HU He HG Ha.
have HeU : 0 <= e * U by exact: mulr_ge0.
have HS := pmccc_weighted_symmetric N C X a.
have [Hlo Hup] := pmccc_box N _ (e * U) HS (pmccc_weighted_form_bound N C X a U e He HG Ha).
apply: paper_main_opnorm_to_action => //.
exact: paper_main_cone_opnorm_of_loewner.
Qed.

(* 2. Normalized powers. *)
Lemma paper_main_power_error (x delta : R) (p : nat) :
  0 <= x -> 0 <= delta -> delta <= 1 -> `|x - 1| <= delta ->
  `|x ^+ p - 1| <= (2 ^+ p - 1) * delta.
Proof.
move=> Hx Hd0 Hd1 Hxd.
have Hx2 : x <= 2.
  by move: Hxd; rewrite ler_norml => /andP [_ H]; lra.
elim: p => [|p IH]; first by rewrite !expr0 subrr normr0 mul0r.
have E : x ^+ p.+1 - 1 = x * (x ^+ p - 1) + (x - 1) by rewrite exprS; ring.
rewrite E; apply: le_trans (ler_normD _ _) _.
rewrite normrM (ger0_norm Hx).
have Hn := normr_ge0 (x ^+ p - 1).
have H1 : x * `|x ^+ p - 1| <= 2 * ((2 ^+ p - 1) * delta) by apply: ler_pM.
rewrite exprS; lra.
Qed.

Lemma paper_main_power_ratio_error (Q n delta : R) (p : nat) :
  0 < n -> 0 <= delta -> delta <= 1 -> `|Q / n - 1| <= delta ->
  `|Q ^+ p - n ^+ p| <= n ^+ p * (2 ^+ p - 1) * delta.
Proof.
move=> Hn Hd0 Hd1 HQ.
have Hx : 0 <= Q / n by move: HQ; rewrite ler_norml => /andP [H _]; lra.
have Hnp : n ^+ p != 0 by rewrite expf_neq0 // gt_eqF.
have E : Q ^+ p - n ^+ p = n ^+ p * ((Q / n) ^+ p - 1).
  by rewrite exprMn exprVn mulrBr mulr1 mulrCA divff // mulr1.
rewrite E normrM (ger0_norm (exprn_ge0 _ (ltW Hn))) -mulrA.
by apply: ler_wpM2l; [exact: exprn_ge0 (ltW Hn) | exact: paper_main_power_error].
Qed.

(* 3. The actual coefficient error under the frame premises. *)
Lemma pmccc_inactive_rankone N d (x : paper_main_sample N d) (q : 'I_d * 'I_d) :
  ~~ (q.1 < q.2)%N -> pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q = 0.
Proof.
move=> Hq; apply/matrixP => i j.
by rewrite /pmcr_rankone !mxE !pmccf_X (negbTE Hq) /= ?mulr0n !mul0r.
Qed.

Theorem paper_main_column_coefficient_opbound N d (C0 delta : R) (x : paper_main_sample N d) (p : nat) :
  (0 < N)%N -> 0 < delta -> delta <= 1 ->
  paper_main_column_frame_good N d C0 delta x ->
  pmlo_opb N (\sum_(q : 'I_d * 'I_d)
      ((pmcr_column_norm N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q) ^+ p - N%:R ^+ p) *:
        pmcr_rankone N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N) q)
    (N%:R ^+ p * (2 ^+ p - 1) * delta * (C0 * N%:R)).
Proof.
move=> HN Hd0 Hd1 [[HQ HQr] [_ [Hm0 HmU]] Hform _ _].
have HN0 : 0 < N%:R :> R by rewrite ltr0n.
have H2p : 1 <= 2 ^+ p :> R by apply: exprn_ege1; rewrite ler1n.
have He : 0 <= N%:R ^+ p * (2 ^+ p - 1) * delta.
  by rewrite !mulr_ge0 ?exprn_ge0 ?subr_ge0 // ltW.
apply: (paper_main_weighted_rankone_opbound _ _ _ _ _ _ (le_trans Hm0 HmU) He Hform).
move=> q; case: (boolP (q.1 < q.2)%N) => Hq.
  by right; apply: paper_main_power_ratio_error => //; [exact: ltW | exact: HQr].
by left; exact: pmccc_inactive_rankone.
Qed.
