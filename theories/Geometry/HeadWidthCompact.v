(* Nonemptiness, compactness and pointwise maximizers for the unit section of
   the bounded-condition cone, for the supremum form of eq:width-transfer
   (manuscript eq:P-max and lem:head-correction-bounds).

   K_kappa \cap S_F is paper_main_head_cone_sphere kappa: the S with
   lam I <= S <= kappa lam I for some lam > 0 and |S|_F = 1. For d > 0 and
   kappa >= 1:
   - it contains I / sqrt d (paper_main_head_cone_sphere_nonempty);
   - every witness lam of a unit S lies in [(kappa sqrt d)^-1, (sqrt d)^-1]
     (pmhw_witness_bounds), so K_kappa \cap S_F is the image of the
     augmented set pmhw_aug of rows (S, lam) with lam in that interval,
     lam I <= S <= kappa lam I and <S, S> = 1;
   - pmhw_aug is closed and inside the box [-1, 1]^(d d + 1), hence compact
     (pmhw_aug_compact), by the toolkit of Geometry.Compact;
   - for every Z, <Z, .> attains its maximum on K_kappa \cap S_F
     (paper_main_head_cone_sphere_max), by the extreme value theorem on
     pmhw_aug.
   The maximizer is chosen for each Z separately: no measurability of the
   choice is claimed. paper_main_head_width_transfer_maximizer combines this
   with the supremum transfer of Geometry.HeadWidth. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.Compact Geometry.Separation
  Geometry.HeadFrobenius Geometry.HeadCorrection Geometry.HeadCoefficients
  Geometry.HeadFeature Geometry.HeadSpectral Geometry.HeadWidth.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WidthCompact.
Variable d : nat.
Local Notation N := (d * d + 1)%N.
Local Notation W := 'rV[R]_N.
Implicit Types (S Z : 'M[R]_d) (w : W).

(* The matrix and the scalar coordinates of an augmented row. *)
Definition pmhw_S w : 'M[R]_d := \matrix_(i, j) w 0 (lshift 1 (mxvec_index i j)).
Definition pmhw_lam w : R := w 0 (rshift (d * d) ord0).
Definition pmhw_lift S (lam : R) : W := row_mx (mxvec S) (lam%:M : 'rV[R]_1).

Lemma pmhw_S_lift S (lam : R) : pmhw_S (pmhw_lift S lam) = S.
Proof. by apply/matrixP => i j; rewrite /pmhw_S /pmhw_lift mxE row_mxEl mxvecE. Qed.

Lemma pmhw_lam_lift S (lam : R) : pmhw_lam (pmhw_lift S lam) = lam.
Proof. by rewrite /pmhw_lam /pmhw_lift row_mxEr mxE eqxx mulr1n. Qed.

(* Witness bounds from the spectral argument. *)
Lemma pmhw_witness_bounds S (lam kappa : R) :
  (0 < d)%N -> 0 < lam ->
  paper_main_loewner_le (lam *: 1%:M) S ->
  paper_main_loewner_le S ((kappa * lam) *: 1%:M) ->
  paper_main_frobenius S = 1 ->
  (kappa * Num.sqrt d%:R)^-1 <= lam /\ lam <= (Num.sqrt d%:R)^-1.
Proof.
move=> Hd Hl H1 H2 HF.
have HS := pmh_loewner_psd _ _ _ (ltW Hl) H1.
have Tl := pmh_loewner_trace_lower _ _ _ H1.
have Tu := pmh_loewner_trace_upper _ _ _ H2.
have Fl := pmh_loewner_frobenius_lower _ _ _ (ltW Hl) H1.
have Fu := pmh_loewner_frobenius_upper _ _ _ HS H2.
rewrite HF expr1n in Fl Fu.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
set sd := Num.sqrt d%:R.
have Hs : 0 < sd by rewrite /sd sqrtr_gt0.
have Hs2 : sd ^+ 2 = d%:R by rewrite /sd sqr_sqrtr // ltW.
have Hlo : lam ^+ 2 * d%:R <= 1 by have := ler_wpM2l (ltW Hl) Tl; nra.
have Htr : 0 <= paper_main_trace S by exact: pmh_trace_psd_ge0.
have Hku : 0 < kappa * lam by nra.
have Hk : 0 < kappa by move: Hku; rewrite pmulr_lgt0.
have Hhi : 1 <= (kappa * lam) ^+ 2 * d%:R.
  by have := ler_wpM2l (ltW Hku) Tu; nra.
have Hl1 : lam * sd <= 1 by nra.
have Ht : (kappa * lam * sd) ^+ 2 = (kappa * lam) ^+ 2 * d%:R by rewrite exprMn Hs2.
have Ht0 : 0 <= kappa * lam * sd by apply: mulr_ge0; exact: ltW.
have Hl2 : 1 <= kappa * lam * sd by nra.
split.
- have Hks : 0 < kappa * sd by exact: mulr_gt0.
  by rewrite -(mul1r ((kappa * sd)^-1)) ler_pdivrMr //; nra.
- by rewrite -(mul1r sd^-1) ler_pdivlMr //.
Qed.

(* K_kappa \cap S_F contains I / sqrt d. *)
Theorem paper_main_head_cone_sphere_nonempty (kappa : R) :
  (0 < d)%N -> 1 <= kappa ->
  paper_main_head_cone_sphere kappa ((Num.sqrt d%:R)^-1 *: (1%:M : 'M[R]_d)).
Proof.
move=> Hd Hk.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
set sd := Num.sqrt d%:R.
have Hs : 0 < sd by rewrite /sd sqrtr_gt0.
have Hs2 : sd ^+ 2 = d%:R by rewrite /sd sqr_sqrtr // ltW.
split.
  exists sd^-1; split; first by rewrite invr_gt0.
  split; first by apply: pmh_loewner_scalar; exact: lexx.
  apply: pmh_loewner_scalar; rewrite ler_pMl ?invr_gt0 //.
have Hi : 0 <= sd^-1 by rewrite invr_ge0 ltW.
rewrite pmh_frobeniusZ (ger0_norm Hi) /paper_main_frobenius pmh_pairing_id pmh_trace_id -/sd.
by rewrite mulVf // lt0r_neq0.
Qed.

(* The augmented compact set. *)
Definition pmhw_aug (kappa : R) : set W :=
  [set w | (kappa * Num.sqrt d%:R)^-1 <= pmhw_lam w /\ pmhw_lam w <= (Num.sqrt d%:R)^-1 /\
     paper_main_loewner_le (pmhw_lam w *: 1%:M) (pmhw_S w) /\
     paper_main_loewner_le (pmhw_S w) ((kappa * pmhw_lam w) *: 1%:M) /\
     paper_main_pairing (pmhw_S w) (pmhw_S w) = 1].

Lemma pmhw_S_continuous (i j : 'I_d) : continuous (fun w : W => pmhw_S w i j).
Proof.
have -> : (fun w : W => pmhw_S w i j) = (fun w : W => w 0 (lshift 1 (mxvec_index i j))).
  by apply/funext => w; rewrite mxE.
exact: pmg_continuous_coord.
Qed.

Lemma pmhw_lam_continuous : continuous pmhw_lam.
Proof. exact: pmg_continuous_coord. Qed.

(* A matrix-valued map with continuous entries has a closed PSD set. *)
Lemma pmhw_psd_closed (E : W -> 'M[R]_d) :
  (forall i j, continuous (fun w => E w i j)) -> closed [set w | paper_main_psd (E w)].
Proof.
move=> HE.
have -> : [set w | paper_main_psd (E w)] =
    (\bigcap_(i : 'I_d) \bigcap_(j : 'I_d) [set w : W | E w i j - E w j i = 0]) `&`
    (\bigcap_(u : 'cV[R]_d) [set w : W | 0 <= paper_main_quadratic_form (E w) u]).
  rewrite predeqE => w; split.
    move=> [Hsym Hpos]; split.
      by move=> i _ j _ /=; rewrite Hsym subrr.
    by move=> u _ /=; exact: Hpos.
  move=> [Hsym Hpos]; split.
    by move=> i j; apply/eqP; rewrite -subr_eq0; apply/eqP; exact: (Hsym i Logic.I j Logic.I).
  by move=> u; exact: (Hpos u Logic.I).
apply: closedI.
  apply: closed_bigI => i _; apply: closed_bigI => j _.
  by apply: pmg_closed_eq; apply: pmg_continuousB; exact: HE.
apply: closed_bigI => u _; apply: pmg_closed_ge.
rewrite /paper_main_quadratic_form.
apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
apply: pmg_continuousM; last exact: pmg_continuous_cst.
apply: pmg_continuousM; first exact: pmg_continuous_cst.
exact: HE.
Qed.

Lemma pmhw_aug_closed (kappa : R) : closed (pmhw_aug kappa).
Proof.
have -> : pmhw_aug kappa =
    [set w | (kappa * Num.sqrt d%:R)^-1 <= pmhw_lam w] `&`
    [set w | 0 <= (Num.sqrt d%:R)^-1 - pmhw_lam w] `&`
    [set w | paper_main_psd (pmhw_S w - pmhw_lam w *: 1%:M)] `&`
    [set w | paper_main_psd ((kappa * pmhw_lam w) *: 1%:M - pmhw_S w)] `&`
    [set w | paper_main_pairing (pmhw_S w) (pmhw_S w) = 1].
  rewrite predeqE => w; split.
    move=> [H1 [H2 [H3 [H4 H5]]]].
    split; [split; [split; [split => // | exact: H3] | exact: H4] | exact: H5].
    by rewrite /= subr_ge0.
  move=> [[[[H1 H2] H3] H4] H5].
  split => //; split; first by move: H2; rewrite /= subr_ge0.
  by split; [exact: H3 | split; [exact: H4 | exact: H5]].
have Hlamc := pmhw_lam_continuous.
have HSc := pmhw_S_continuous.
apply: closedI; last first.
  apply: pmg_closed_eq; rewrite /paper_main_pairing.
  apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
  by apply: pmg_continuousM; exact: HSc.
apply: closedI; last first.
  apply: pmhw_psd_closed => i j.
  have -> : (fun w : W => ((kappa * pmhw_lam w) *: 1%:M - pmhw_S w) i j) =
      (fun w : W => kappa * pmhw_lam w * (i == j)%:R - pmhw_S w i j).
    by apply/funext => w; rewrite !mxE mulr_natr.
  apply: pmg_continuousB; last exact: HSc.
  apply: pmg_continuousM; last exact: pmg_continuous_cst.
  by apply: pmg_continuousM; [exact: pmg_continuous_cst | exact: Hlamc].
apply: closedI; last first.
  apply: pmhw_psd_closed => i j.
  have -> : (fun w : W => (pmhw_S w - pmhw_lam w *: 1%:M) i j) =
      (fun w : W => pmhw_S w i j - pmhw_lam w * (i == j)%:R).
    by apply/funext => w; rewrite !mxE mulr_natr.
  apply: pmg_continuousB; first exact: HSc.
  by apply: pmg_continuousM; [exact: Hlamc | exact: pmg_continuous_cst].
apply: closedI.
  by apply: pmg_closed_ge; exact: Hlamc.
apply: pmg_closed_ge; apply: pmg_continuousB; first exact: pmg_continuous_cst.
exact: Hlamc.
Qed.

Lemma pmhw_entry_sqr_le S (i j : 'I_d) : S i j ^+ 2 <= paper_main_pairing S S.
Proof.
rewrite /paper_main_pairing (bigD1 i) //= (bigD1 j) //= -expr2.
rewrite -addrA lerDl.
apply: addr_ge0.
  by apply: sumr_ge0 => k _; rewrite -expr2 sqr_ge0.
by apply: sumr_ge0 => k _; apply: sumr_ge0 => l _; rewrite -expr2 sqr_ge0.
Qed.

Lemma pmhw_aug_sub_box (kappa : R) :
  (0 < d)%N -> 1 <= kappa -> pmhw_aug kappa `<=` pmg_box N.
Proof.
move=> Hd Hk w [H1 [H2 [_ [_ H5]]]] k.
have Hdp : 1 <= d%:R :> R by rewrite ler1n.
have Hs1 : 1 <= Num.sqrt d%:R :> R by have := @ler_wsqrtr R 1 d%:R Hdp; rewrite sqrtr1.
have Hsp : 0 < Num.sqrt d%:R :> R by exact: lt_le_trans ltr01 Hs1.
have Hsi : Num.sqrt d%:R * (Num.sqrt d%:R)^-1 = 1 :> R by rewrite mulfV // gt_eqF.
have Hip : 0 < (Num.sqrt d%:R)^-1 :> R by rewrite invr_gt0.
have Hb : (Num.sqrt d%:R)^-1 <= 1 :> R by nra.
have Hkp : 0 < kappa * Num.sqrt d%:R by apply: mulr_gt0 => //; exact: lt_le_trans ltr01 Hk.
have Ha : 0 <= (kappa * Num.sqrt d%:R)^-1 by rewrite invr_ge0 ltW.
rewrite /= in_itv /=.
case: (splitP k) => [j Hj | j Hj].
- have -> : k = lshift 1 j by apply: val_inj; rewrite /= Hj.
  case: (mxvec_indexP j) => i l.
  have := pmhw_entry_sqr_le (pmhw_S w) i l; rewrite H5 mxE => Hsq.
  by apply/andP; split; nra.
- have -> : k = rshift (d * d) ord0.
    by apply: val_inj; rewrite /= Hj; case: j {Hj} => -[] // ? /=.
  rewrite -/(pmhw_lam w).
  by apply/andP; split; lra.
Qed.

Lemma pmhw_lift_aug S (lam kappa : R) :
  (0 < d)%N -> 0 < lam ->
  paper_main_loewner_le (lam *: 1%:M) S ->
  paper_main_loewner_le S ((kappa * lam) *: 1%:M) ->
  paper_main_frobenius S = 1 -> pmhw_aug kappa (pmhw_lift S lam).
Proof.
move=> Hd Hl H1 H2 HF.
have [Ha Hb] := pmhw_witness_bounds _ _ _ Hd Hl H1 H2 HF.
rewrite /pmhw_aug /= pmhw_S_lift pmhw_lam_lift; do !split => //.
by rewrite -pmh_frobenius_sqr HF expr1n.
Qed.

End WidthCompact.
