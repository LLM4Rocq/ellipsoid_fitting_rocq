(* The trace-one slice of the bounded-condition cone. For d > 0 and
   kappa >= 1, a nonzero element of the condition cone satisfies
   lam I <= S <= kappa lam I for some lam > 0 (paper_main_head_condition).
   Its trace-one slice is compact and convex. It is represented by the
   augmented set paper_main_cone_kernel_slice d kappa of rows w = (S, lam)
   of 'rV[R]_(d*d+1), read with pmhw_S and pmhw_lam of
   PaperMainGeometryHeadWidthCompact, such that
     (kappa d)^-1 <= lam <= d^-1, lam I <= S <= kappa lam I, Tr S = 1.
   Every witness lam of a trace-one S lies in that interval
   (paper_main_cone_kernel_witness_bounds), so the bounds lose nothing.
   The set is closed and inside the box [-1, 1]^(d d + 1), hence compact;
   it contains I / d; it is closed under segments in both coordinates; a
   point of the cone sphere divided by its trace lies in it; and a point of
   it divided by its Frobenius norm lies in the cone sphere. Nothing from
   the paper is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryCompact PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth
  PaperMainGeometryHeadWidthCompact.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition paper_main_cone_kernel_slice d (kappa : R) : set 'rV[R]_(d * d + 1) :=
  [set w | (kappa * d%:R)^-1 <= pmhw_lam d w /\ pmhw_lam d w <= (d%:R)^-1 /\
     paper_main_loewner_le (pmhw_lam d w *: 1%:M) (pmhw_S d w) /\
     paper_main_loewner_le (pmhw_S d w) ((kappa * pmhw_lam d w) *: 1%:M) /\
     paper_main_trace (pmhw_S d w) = 1].

(* Witness bounds on the trace-one slice. *)
Lemma paper_main_cone_kernel_witness_bounds d (S : 'M[R]_d) (lam kappa : R) :
  (0 < d)%N -> 1 <= kappa ->
  paper_main_loewner_le (lam *: 1%:M) S ->
  paper_main_loewner_le S ((kappa * lam) *: 1%:M) ->
  paper_main_trace S = 1 ->
  (kappa * d%:R)^-1 <= lam /\ lam <= (d%:R)^-1.
Proof.
move=> Hd Hk H1 H2 Htr.
have Tl := pmh_loewner_trace_lower _ _ _ H1.
have Tu := pmh_loewner_trace_upper _ _ _ H2.
rewrite Htr in Tl Tu.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
have Hkp : 0 < kappa by exact: lt_le_trans ltr01 Hk.
have Hkd : 0 < kappa * d%:R by exact: mulr_gt0.
split.
- rewrite -(mul1r (kappa * d%:R)^-1) ler_pdivrMr //.
  by rewrite mulrCA mulrA.
- by rewrite -(mul1r (d%:R)^-1) ler_pdivlMr.
Qed.

Lemma paper_main_cone_kernel_slice_closed d (kappa : R) :
  closed (paper_main_cone_kernel_slice d kappa).
Proof.
have -> : paper_main_cone_kernel_slice d kappa =
    [set w | (kappa * d%:R)^-1 <= pmhw_lam d w] `&`
    [set w | 0 <= (d%:R)^-1 - pmhw_lam d w] `&`
    [set w | paper_main_psd (pmhw_S d w - pmhw_lam d w *: 1%:M)] `&`
    [set w | paper_main_psd ((kappa * pmhw_lam d w) *: 1%:M - pmhw_S d w)] `&`
    [set w | paper_main_trace (pmhw_S d w) = 1].
  rewrite predeqE => w; split.
    move=> [H1 [H2 [H3 [H4 H5]]]].
    split; [split; [split; [split => // | exact: H3] | exact: H4] | exact: H5].
    by rewrite /= subr_ge0.
  move=> [[[[H1 H2] H3] H4] H5].
  split => //; split; first by move: H2; rewrite /= subr_ge0.
  by split; [exact: H3 | split; [exact: H4 | exact: H5]].
have Hlamc := pmhw_lam_continuous d.
have HSc := pmhw_S_continuous d.
apply: closedI; last first.
  apply: pmg_closed_eq; rewrite /paper_main_trace.
  by apply: pmg_continuous_sum => i; exact: HSc.
apply: closedI; last first.
  apply: pmhw_psd_closed => i j.
  have -> : (fun w => ((kappa * pmhw_lam d w) *: 1%:M - pmhw_S d w) i j) =
      (fun w => kappa * pmhw_lam d w * (i == j)%:R - pmhw_S d w i j).
    by apply/funext => w; rewrite !mxE mulr_natr.
  apply: pmg_continuousB; last exact: HSc.
  apply: pmg_continuousM; last exact: pmg_continuous_cst.
  by apply: pmg_continuousM; [exact: pmg_continuous_cst | exact: Hlamc].
apply: closedI; last first.
  apply: pmhw_psd_closed => i j.
  have -> : (fun w => (pmhw_S d w - pmhw_lam d w *: 1%:M) i j) =
      (fun w => pmhw_S d w i j - pmhw_lam d w * (i == j)%:R).
    by apply/funext => w; rewrite !mxE mulr_natr.
  apply: pmg_continuousB; first exact: HSc.
  by apply: pmg_continuousM; [exact: Hlamc | exact: pmg_continuous_cst].
apply: closedI.
  by apply: pmg_closed_ge; exact: Hlamc.
apply: pmg_closed_ge; apply: pmg_continuousB; first exact: pmg_continuous_cst.
exact: Hlamc.
Qed.

Lemma paper_main_cone_kernel_slice_sub_box d (kappa : R) :
  (0 < d)%N -> 1 <= kappa -> paper_main_cone_kernel_slice d kappa `<=` pmg_box (d * d + 1).
Proof.
move=> Hd Hk w [H1 [H2 [H3 [_ H5]]]] k.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
have Hd1 : 1 <= d%:R :> R by rewrite ler1n.
have Hkp : 0 < kappa * d%:R by apply: mulr_gt0 => //; exact: lt_le_trans ltr01 Hk.
have Ha : 0 <= (kappa * d%:R)^-1 by rewrite invr_ge0 ltW.
have Hb : (d%:R)^-1 <= 1 :> R.
  by rewrite -(mul1r (d%:R)^-1) ler_pdivrMr // mul1r.
have Hl0 : 0 <= pmhw_lam d w by exact: le_trans Ha H1.
have HS : paper_main_psd (pmhw_S d w) by exact: pmh_loewner_psd _ _ _ Hl0 H3.
rewrite /= in_itv /=.
case: (splitP k) => [j Hj | j Hj].
- have -> : k = lshift 1 j by apply: val_inj; rewrite /= Hj.
  case: (mxvec_indexP j) => i l.
  by have := pmg_trace_one_entry _ (pmhw_S d w) i l HS H5; rewrite /= in_itv /= mxE.
- have -> : k = rshift (d * d) ord0.
    by apply: val_inj; rewrite /= Hj; case: j {Hj} => -[] // ? /=.
  rewrite -/(pmhw_lam d w).
  by apply/andP; split; lra.
Qed.

Theorem paper_main_cone_kernel_slice_compact d (kappa : R) :
  (0 < d)%N -> 1 <= kappa -> compact (paper_main_cone_kernel_slice d kappa).
Proof.
move=> Hd Hk.
have -> : paper_main_cone_kernel_slice d kappa =
    pmg_box (d * d + 1) `&` paper_main_cone_kernel_slice d kappa.
  rewrite predeqE => w; split=> [Hw | [_ Hw]] //; split=> //.
  exact: (paper_main_cone_kernel_slice_sub_box _ _ Hd Hk _ Hw).
by apply: compact_closedI; [exact: pmg_box_compact | exact: paper_main_cone_kernel_slice_closed].
Qed.

Lemma paper_main_cone_kernel_slice_identity d (kappa : R) :
  (0 < d)%N -> 1 <= kappa ->
  paper_main_cone_kernel_slice d kappa (pmhw_lift d ((d%:R)^-1 *: 1%:M) (d%:R)^-1).
Proof.
move=> Hd Hk.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
have Hkp : 0 < kappa by exact: lt_le_trans ltr01 Hk.
have Hi : 0 <= (d%:R)^-1 :> R by rewrite invr_ge0 ltW.
rewrite /paper_main_cone_kernel_slice /= pmhw_S_lift pmhw_lam_lift.
split.
  rewrite -(mul1r (kappa * d%:R)^-1) ler_pdivrMr ?mulr_gt0 //.
  by rewrite mulrCA mulVf ?gt_eqF // mulr1.
split; first exact: lexx.
split; first by apply: pmh_loewner_scalar; exact: lexx.
split; first by apply: pmh_loewner_scalar; rewrite ler_peMl.
by rewrite pmh_trace_scalar mulVf // gt_eqF.
Qed.

Lemma paper_main_cone_kernel_slice_nonempty d (kappa : R) :
  (0 < d)%N -> 1 <= kappa -> paper_main_cone_kernel_slice d kappa !=set0.
Proof.
move=> Hd Hk; eexists; exact: paper_main_cone_kernel_slice_identity.
Qed.

(* Convexity: the slice is closed under segments in (S, lam). *)
Lemma paper_main_cone_kernel_slice_segment d (kappa : R) w0 w (t : R) :
  0 <= t -> t <= 1 ->
  paper_main_cone_kernel_slice d kappa w0 -> paper_main_cone_kernel_slice d kappa w ->
  paper_main_cone_kernel_slice d kappa
    (pmhw_lift d (pmhw_S d w0 + t *: (pmhw_S d w - pmhw_S d w0))
       (pmhw_lam d w0 + t * (pmhw_lam d w - pmhw_lam d w0))%R).
Proof.
move=> t0 t1 [A1 [A2 [A3 [A4 A5]]]] [B1 [B2 [B3 [B4 B5]]]].
rewrite /paper_main_cone_kernel_slice /= pmhw_S_lift pmhw_lam_lift.
have Hc : 0 <= 1 - t by rewrite subr_ge0.
have ES : pmhw_S d w0 + t *: (pmhw_S d w - pmhw_S d w0) =
    (1 - t) *: pmhw_S d w0 + t *: pmhw_S d w.
  by rewrite scalerBr addrA addrAC scalerBl scale1r.
have El : pmhw_lam d w0 + t * (pmhw_lam d w - pmhw_lam d w0) =
    (1 - t) * pmhw_lam d w0 + t * pmhw_lam d w by ring.
split; first by rewrite El; nra.
split; first by rewrite El; nra.
split.
  have EL : (((1 - t) * pmhw_lam d w0 + t * pmhw_lam d w) *: 1%:M : 'M[R]_d) =
      (1 - t) *: (pmhw_lam d w0 *: 1%:M) + t *: (pmhw_lam d w *: 1%:M).
    by rewrite scalerDl !scalerA.
  rewrite ES El EL.
  by apply: pmh_loewner_add; apply: pmh_loewner_scale.
split.
  have Ek : ((kappa * ((1 - t) * pmhw_lam d w0 + t * pmhw_lam d w)) *: 1%:M : 'M[R]_d) =
      (1 - t) *: ((kappa * pmhw_lam d w0) *: 1%:M) + t *: ((kappa * pmhw_lam d w) *: 1%:M).
    by rewrite !scalerA -scalerDl; congr (_ *: _); ring.
  rewrite ES El Ek.
  by apply: pmh_loewner_add; apply: pmh_loewner_scale.
exact: pms_seg_trace.
Qed.

(* From the cone sphere to the slice: divide by the trace. *)
Lemma paper_main_cone_kernel_slice_of_sphere d (kappa : R) (P : 'M[R]_d) :
  (0 < d)%N -> 1 <= kappa -> paper_main_head_cone_sphere kappa P ->
  0 < paper_main_trace P /\
  exists lam, paper_main_cone_kernel_slice d kappa
    (pmhw_lift d ((paper_main_trace P)^-1 *: P) lam).
Proof.
move=> Hd Hk [[lam [Hl [H1 H2]]] HF].
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
have Tl := pmh_loewner_trace_lower _ _ _ H1.
have Ht : 0 < paper_main_trace P by apply: lt_le_trans Tl; exact: mulr_gt0.
split => //.
have [L1 L2] := paper_main_head_loewner_scale _ P (paper_main_trace P) lam (kappa * lam) Ht H1 H2.
have Htr1 : paper_main_trace ((paper_main_trace P)^-1 *: P) = 1.
  by rewrite pms_trace_scale mulVf // gt_eqF.
have L2' : paper_main_loewner_le ((paper_main_trace P)^-1 *: P)
    ((kappa * (lam / paper_main_trace P)) *: 1%:M) by rewrite mulrA.
have [B1 B2] := paper_main_cone_kernel_witness_bounds _ _ _ _ Hd Hk L1 L2' Htr1.
exists (lam / paper_main_trace P).
rewrite /paper_main_cone_kernel_slice /= pmhw_S_lift pmhw_lam_lift.
split; first exact: B1.
split; first exact: B2.
split; first exact: L1.
split; first exact: L2'.
exact: Htr1.
Qed.

(* From the slice to the cone sphere: divide by the Frobenius norm. *)
Lemma paper_main_cone_kernel_sphere_of_slice d (kappa : R) w :
  (0 < d)%N -> 1 <= kappa -> paper_main_cone_kernel_slice d kappa w ->
  pmhw_S d w != 0 /\
  paper_main_head_cone_sphere kappa ((paper_main_frobenius (pmhw_S d w))^-1 *: pmhw_S d w).
Proof.
move=> Hd Hk [H1 [H2 [H3 [H4 H5]]]].
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
have Hkp : 0 < kappa * d%:R by apply: mulr_gt0 => //; exact: lt_le_trans ltr01 Hk.
have Hl : 0 < pmhw_lam d w by apply: lt_le_trans H1; rewrite invr_gt0.
have HS0 : pmhw_S d w != 0.
  by apply/eqP => HS; move: H5; rewrite HS pms_trace0 => /eqP; rewrite eq_sym oner_eq0.
have Hf : 0 < paper_main_frobenius (pmhw_S d w) by exact: pmh_frobenius_gt0.
split => //.
have [L1 L2] := paper_main_head_loewner_scale _ _ _ _ _ Hf H3 H4.
split; last exact: pmh_frobenius_normalize.
exists (pmhw_lam d w / paper_main_frobenius (pmhw_S d w)); split; first exact: divr_gt0.
split => //.
by rewrite mulrA.
Qed.
