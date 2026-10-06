(* The shifted positive part as a bounded-condition candidate: the
   deterministic step of manuscript lem:widthcone (width of the
   bounded-condition cone), without semicircle asymptotics.

   For symmetric Z with P = paper_main_psd_projection Z, d > 0 and t > 0,
   put Q = P + t I and S = Q / |Q|_F (paper_main_cone_shift Z t). Then S is
   PSD, positive definite and of unit Frobenius norm, and
     <Z, S> >= |P|_F - t sqrt d - |Tr Z| / sqrt d
   (paper_main_cone_shift_support). The route: <Z, P> = |P|_F^2 (Moreau);
   t sqrt d <= |Q|_F <= |P|_F + t sqrt d (Tr P >= 0, |I|_F = sqrt d);
   |P|^2 >= (|P| - t sqrt d) |Q|, which needs no division by |P| and covers
   P = 0; and t |Tr Z| / |Q| <= |Tr Z| / sqrt d. Under the explicit Loewner
   bound P <= b I (b >= 0), S lies in the condition cone with
   kappa = (b + t) / t, and the support of K_kappa \cap S_F is at least the
   same bound (paper_main_cone_shift_cone_support). For b = C sqrt d and
   t = s sqrt d: kappa = (C + s) / s and loss s d + |Tr Z| / sqrt d
   (paper_main_cone_shift_scaled). The bound P <= b I is discharged from an
   operator bound on Z in PaperMainConeConditionOperator. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral
  PaperMainGeometryHeadWidth PaperMainConeProjection.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

#[local] Arguments paper_main_psd_projection {d} Z.
#[local] Arguments paper_main_psd_negative_part {d} Z.

(* S = (P + t I) / |P + t I|_F. *)
Definition paper_main_cone_shift {d : nat} (Z : 'M[R]_d) (t : R) : 'M[R]_d :=
  paper_main_head_normalize (paper_main_psd_projection Z + t *: 1%:M).

Section ConeCondition.
Variable d : nat.
Implicit Types (P S Z : 'M[R]_d).

Lemma pmcc_frobenius_id : paper_main_frobenius (1%:M : 'M[R]_d) = Num.sqrt d%:R.
Proof. by rewrite /paper_main_frobenius pmh_pairing_id pmh_trace_id. Qed.

Lemma pmcc_pairing_id_right Z : paper_main_pairing Z 1%:M = paper_main_trace Z.
Proof. by rewrite paper_main_pairingC pmh_pairing_id. Qed.

Lemma pmcc_pairing_projection Z :
  paper_main_symmetric Z ->
  paper_main_pairing Z (paper_main_psd_projection Z) =
  paper_main_pairing (paper_main_psd_projection Z) (paper_main_psd_projection Z).
Proof.
move=> HZ; have [_ _ HZd Horth] := paper_main_psd_moreau _ _ HZ.
rewrite {1}HZd pmh_pairingBl (paper_main_pairingC _ (paper_main_psd_negative_part Z)).
by rewrite Horth subr0.
Qed.

Lemma pmcc_shift_psd Z (t : R) :
  0 <= t -> paper_main_psd (paper_main_psd_projection Z + t *: 1%:M).
Proof.
move=> Ht; apply: pms_psd_add; first exact: paper_main_psd_projection_psd.
exact: pmh_psd_scalar.
Qed.

Lemma pmcc_shift_upper Z (t : R) :
  0 <= t ->
  paper_main_frobenius (paper_main_psd_projection Z + t *: 1%:M) <=
  paper_main_frobenius (paper_main_psd_projection Z) + t * Num.sqrt d%:R.
Proof.
move=> Ht; apply: le_trans (pmh_frobenius_triangle _ _ _) _.
by rewrite pmh_frobeniusZ pmcc_frobenius_id ger0_norm.
Qed.

Lemma pmcc_shift_sqr Z (t : R) :
  paper_main_pairing (paper_main_psd_projection Z + t *: 1%:M)
                     (paper_main_psd_projection Z + t *: 1%:M) =
  paper_main_pairing (paper_main_psd_projection Z) (paper_main_psd_projection Z) +
  2 * t * paper_main_trace (paper_main_psd_projection Z) + t ^+ 2 * d%:R.
Proof.
rewrite pmh_pairingDl !pmh_pairingDr !pmh_pairingZl !paper_main_pairing_scale.
rewrite pmcc_pairing_id_right pmh_pairing_id pmh_pairing_id pmh_trace_id; ring.
Qed.

Lemma pmcc_shift_lower Z (t : R) :
  0 <= t ->
  t * Num.sqrt d%:R <= paper_main_frobenius (paper_main_psd_projection Z + t *: 1%:M).
Proof.
move=> Ht.
have Htr := pmh_trace_psd_ge0 _ _ (paper_main_psd_projection_psd _ Z).
have HP2 := paper_main_pairing_self_ge0 _ (paper_main_psd_projection Z).
have Hq0 := pmh_frobenius_ge0 _ (paper_main_psd_projection Z + t *: 1%:M).
have Hq2 := pmh_frobenius_sqr _ (paper_main_psd_projection Z + t *: 1%:M).
rewrite pmcc_shift_sqr in Hq2.
have Hd0 : 0 <= d%:R :> R by exact: ler0n.
have Hs0 : 0 <= Num.sqrt d%:R :> R by exact: sqrtr_ge0.
have Hs2 : Num.sqrt d%:R ^+ 2 = d%:R :> R by rewrite sqr_sqrtr.
have Hts : 0 <= t * Num.sqrt d%:R by exact: mulr_ge0.
have Hsq : (t * Num.sqrt d%:R) ^+ 2 <=
    paper_main_frobenius (paper_main_psd_projection Z + t *: 1%:M) ^+ 2.
  by rewrite Hq2 exprMn Hs2; nra.
nra.
Qed.

(* The candidate is PSD, positive definite and of unit norm. *)
Theorem paper_main_cone_shift_basic Z (t : R) :
  (0 < d)%N -> 0 < t ->
  [/\ paper_main_psd (paper_main_cone_shift Z t), paper_main_pd (paper_main_cone_shift Z t) &
      paper_main_frobenius (paper_main_cone_shift Z t) = 1].
Proof.
move=> Hd Ht.
have Hs : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
have Hlo := pmcc_shift_lower Z t (ltW Ht).
have HQ := pmcc_shift_psd Z t (ltW Ht).
rewrite /paper_main_cone_shift /paper_main_head_normalize.
set Q := paper_main_psd_projection Z + t *: 1%:M in Hlo HQ *.
have Hq : 0 < paper_main_frobenius Q by apply: lt_le_trans Hlo; exact: mulr_gt0.
have HQ0 : Q != 0 by apply/eqP => H0; move: Hq; rewrite H0 pmh_frobenius0 ltxx.
have Hi : 0 <= (paper_main_frobenius Q)^-1 by rewrite invr_ge0 ltW.
have HS : paper_main_psd ((paper_main_frobenius Q)^-1 *: Q) by exact: paper_main_psd_scale.
split => //; last exact: pmh_frobenius_normalize.
have L1 : paper_main_loewner_le (t *: 1%:M) Q.
  by rewrite /paper_main_loewner_le /Q addrK; exact: paper_main_psd_projection_psd.
have L2 := pmh_loewner_scale _ _ _ _ Hi L1.
rewrite scalerA in L2.
apply: (pmh_loewner_pd _ ((paper_main_frobenius Q)^-1 * t)) => //.
by rewrite mulr_gt0 // invr_gt0.
Qed.

(* The quantitative support lower bound. *)
Theorem paper_main_cone_shift_support Z (t : R) :
  (0 < d)%N -> paper_main_symmetric Z -> 0 < t ->
  paper_main_frobenius (paper_main_psd_projection Z) - t * Num.sqrt d%:R -
    `|paper_main_trace Z| / Num.sqrt d%:R <=
  paper_main_pairing Z (paper_main_cone_shift Z t).
Proof.
move=> Hd HZ Ht.
have HZQ : paper_main_pairing Z (paper_main_psd_projection Z + t *: 1%:M) =
    paper_main_frobenius (paper_main_psd_projection Z) ^+ 2 + t * paper_main_trace Z.
  rewrite pmh_pairingDr pmcc_pairing_projection // paper_main_pairing_scale.
  by rewrite pmcc_pairing_id_right -pmh_frobenius_sqr.
have Hup := pmcc_shift_upper Z t (ltW Ht).
have Hlo := pmcc_shift_lower Z t (ltW Ht).
rewrite /paper_main_cone_shift /paper_main_head_normalize paper_main_pairing_scale HZQ.
set P := paper_main_psd_projection Z in Hup Hlo *.
set Q := P + t *: 1%:M in Hup Hlo *.
set sd := Num.sqrt d%:R in Hup Hlo *.
set T := paper_main_trace Z.
have Hs : 0 < sd by rewrite /sd sqrtr_gt0 ltr0n.
have Hts : 0 < t * sd by exact: mulr_gt0.
have Hq : 0 < paper_main_frobenius Q by exact: lt_le_trans Hts Hlo.
rewrite [X in _ <= X]mulrC ler_pdivlMr //.
have Hp0 := pmh_frobenius_ge0 _ P.
have H1 : (paper_main_frobenius P - t * sd) * paper_main_frobenius Q <=
    paper_main_frobenius P ^+ 2.
  have [Hpa|Hpa] := leP 0 (paper_main_frobenius P - t * sd).
    by have := ler_wpM2l Hpa Hup; nra.
  nra.
have HT0 := normr_ge0 T.
have HTm := ler_norm (- T); rewrite normrN in HTm.
have Hneg := ler_wpM2l (ltW Ht) HTm.
have Htq : t <= paper_main_frobenius Q / sd by rewrite ler_pdivlMr.
have HTq : t * `|T| <= `|T| / sd * paper_main_frobenius Q.
  have -> : `|T| / sd * paper_main_frobenius Q = `|T| * (paper_main_frobenius Q / sd).
    by rewrite mulrAC -mulrA.
  by rewrite [X in X <= _]mulrC; exact: (ler_wpM2l HT0 Htq).
lra.
Qed.


(* Under the explicit bound P <= b I, the candidate lies in
   K_kappa \cap S_F for kappa = (b + t) / t. *)
Theorem paper_main_cone_shift_condition Z (t b kappa : R) :
  (0 < d)%N -> 0 < t -> 0 <= b -> kappa = (b + t) / t ->
  paper_main_loewner_le (paper_main_psd_projection Z) (b *: 1%:M) ->
  paper_main_head_cone_sphere kappa (paper_main_cone_shift Z t).
Proof.
move=> Hd Ht Hb Hk HPb.
have [_ _ HS1] := paper_main_cone_shift_basic Z t Hd Ht.
split => //.
have Hs : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
have Hlo := pmcc_shift_lower Z t (ltW Ht).
rewrite /paper_main_cone_shift /paper_main_head_normalize.
set Q := paper_main_psd_projection Z + t *: 1%:M in Hlo *.
have Hq : 0 < paper_main_frobenius Q by apply: lt_le_trans Hlo; exact: mulr_gt0.
have L1 : paper_main_loewner_le (t *: 1%:M) Q.
  by rewrite /paper_main_loewner_le /Q addrK; exact: paper_main_psd_projection_psd.
have L2 : paper_main_loewner_le Q ((b + t) *: 1%:M).
  rewrite /paper_main_loewner_le.
  have -> : (b + t) *: 1%:M - Q = b *: 1%:M - paper_main_psd_projection Z.
    by rewrite /Q; apply/matrixP => i j; rewrite !mxE; ring.
  exact: HPb.
have [N1 N2] := paper_main_head_loewner_scale _ _ _ _ _ Hq L1 L2.
exists (t / paper_main_frobenius Q); split; first by rewrite divr_gt0.
split; first exact: N1.
have -> : kappa * (t / paper_main_frobenius Q) = (b + t) / paper_main_frobenius Q.
  by rewrite Hk mulrA (divfK (lt0r_neq0 Ht)).
exact: N2.
Qed.

(* The support of K_kappa \cap S_F is at least the candidate bound. *)
Theorem paper_main_cone_shift_cone_support Z (t b kappa : R) :
  (0 < d)%N -> paper_main_symmetric Z -> 0 < t -> 0 <= b -> kappa = (b + t) / t ->
  paper_main_loewner_le (paper_main_psd_projection Z) (b *: 1%:M) ->
  paper_main_frobenius (paper_main_psd_projection Z) - t * Num.sqrt d%:R -
    `|paper_main_trace Z| / Num.sqrt d%:R <=
  paper_main_head_support Z (paper_main_head_cone_sphere kappa).
Proof.
move=> Hd HZ Ht Hb Hk HPb.
have HC := paper_main_cone_shift_condition Z t b kappa Hd Ht Hb Hk HPb.
apply: le_trans (paper_main_cone_shift_support Z t Hd HZ Ht) _.
by apply: (pmh_support_ge _ _ _ _ _ HC) => S [_ HS].
Qed.

(* The scaled form: b = C sqrt d, t = s sqrt d, kappa = (C + s) / s and
   loss s d + |Tr Z| / sqrt d. *)
Corollary paper_main_cone_shift_scaled Z (C s t kappa : R) :
  (0 < d)%N -> paper_main_symmetric Z -> 0 < s -> 0 <= C ->
  t = s * Num.sqrt d%:R -> kappa = (C + s) / s ->
  paper_main_loewner_le (paper_main_psd_projection Z) ((C * Num.sqrt d%:R) *: 1%:M) ->
  paper_main_head_cone_sphere kappa (paper_main_cone_shift Z t) /\
  paper_main_frobenius (paper_main_psd_projection Z) - s * d%:R -
    `|paper_main_trace Z| / Num.sqrt d%:R <=
  paper_main_head_support Z (paper_main_head_cone_sphere kappa).
Proof.
move=> Hd HZ Hs HC Ht Hk HPb.
have Hsd : 0 < Num.sqrt d%:R :> R by rewrite sqrtr_gt0 ltr0n.
have Htp : 0 < t by rewrite Ht mulr_gt0.
have Hb : 0 <= C * Num.sqrt d%:R by rewrite mulr_ge0 // ltW.
have Hk' : kappa = (C * Num.sqrt d%:R + t) / t.
  rewrite Hk Ht -mulrDl invfM mulrACA mulfV ?mulr1 //.
  exact: lt0r_neq0.
have Hl : t * Num.sqrt d%:R = s * d%:R.
  by rewrite Ht -mulrA -expr2 sqr_sqrtr // ler0n.
split; first exact: (paper_main_cone_shift_condition Z t (C * Num.sqrt d%:R) kappa Hd Htp Hb Hk' HPb).
have := paper_main_cone_shift_cone_support Z t (C * Num.sqrt d%:R) kappa Hd HZ Htp Hb Hk' HPb.
by rewrite Hl.
Qed.

End ConeCondition.
