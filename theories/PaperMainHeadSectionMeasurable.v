(* Joint measurability of the support of the data-dependent head section.
   For d = S n, kappa >= 1, matrices W k (k < m) and Z, the section is
   paper_main_head_section kappa W = K_kappa \cap S_F \cap ker W, and its
   support is paper_main_head_support Z (section) = sup of <Z, S> over it.
   The section can be empty, and then the support is sup set0 = 0.
   - Countable characterization (paper_main_head_section_level_iff). Take
     fixed finite nets B j t, t < s j, of K_kappa \cap S_F with Frobenius
     accuracy 1/(2(j+1)) (PaperMainConeApproxSelector). Then "the section is
     nonempty and c <= support" holds iff for every j some net point B j t
     has |<W k, B j t>| <= (1 + <W k, W k>)/(j+1) for every k and
     c - (1 + <Z, Z>)/(j+1) <= <Z, B j t>. One direction uses the supremum
     and the net; the other lifts the net points to the compact augmented
     set pmhw_aug, takes a cluster point and passes to the limit.
   - Measurability. On any measurable space, for entrywise measurable W k
     and Z, every level set of the support is measurable, so the support is
     a measurable function (paper_main_head_section_support_measurable), and
     the event that the section is nonempty is measurable.
   - |support| <= |Z|_F, also for empty sections.
   No measurable selection and no nonemptiness assumption is used. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype derive Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryCompact PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral PaperMainGeometryHeadWidth
  PaperMainGeometryHeadWidthCompact PaperMainMeasurabilityBox PaperMainMeasurabilityCompact
  PaperMainFiniteSupportSelector PaperMainConeApproxSelector.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* Generic measurability helpers. *)

Lemma paper_main_head_section_le_measurable {dX : measure_display} {X : measurableType dX}
    (f g : X -> R) :
  measurable_fun [set: X] (f : X -> T) -> measurable_fun [set: X] (g : X -> T) ->
  measurable [set x | f x <= g x].
Proof.
move=> mf mg.
have mgf := measurable_funB mg mf.
have moA : measurable [set t : T | 0 <= t] by apply: closed_measurable; exact: (@closed_ge R 0).
have := mgf measurableT _ moA.
rewrite setTI => H.
rewrite (_ : [set x | f x <= g x] = (fun x => (g x - f x : T)) @^-1` [set t : T | 0 <= t])//.
by apply/seteqP; split=> x /=; rewrite subr_ge0.
Qed.

Lemma paper_main_head_section_measurable_fun_ge {dX : measure_display}
    {X : measurableType dX} (f : X -> R) :
  (forall c, measurable [set x | c <= f x]) -> measurable_fun [set: X] (f : X -> T).
Proof.
move=> Hf.
have Hlt : forall c, measurable [set x | c < f x].
  move=> c.
  have -> : [set x | c < f x] = \bigcup_(k : nat) [set x | c + k.+1%:R^-1 <= f x].
    apply/seteqP; split=> x /=.
    - move=> Hx; have Hpos : 0 < f x - c by rewrite subr_gt0.
      have [k Hk] := pm_inv_small (f x - c) Hpos.
      by exists k => //=; rewrite -lerBrDl; exact: ltW.
    - move=> [k _ Hk]; apply: lt_le_trans Hk.
      by rewrite ltrDl invr_gt0 ltr0n.
  by apply: bigcupT_measurable => k; exact: Hf.
apply: (measurability (@ocitv R)); first by [].
move=> _ [B [[a b] _ <-] <-]; rewrite setTI.
have -> : f @^-1` `]a, b]%classic = [set x | a < f x] `&` ~` [set x | b < f x].
  apply/seteqP; split=> x /=; rewrite in_itv /=.
  - by move=> /andP [H1 H2]; split=> //; apply/negP; rewrite -leNgt.
  - by move=> [H1 H2]; apply/andP; split=> //; rewrite leNgt; apply/negP.
by apply: measurableI; [exact: Hlt | apply: measurableC; exact: Hlt].
Qed.

(* The support on an empty section, and the norm bound. *)

Lemma paper_main_head_section_support_empty {d m : nat} (kappa : R)
    (W : 'I_m -> 'M[R]_d) (Z : 'M[R]_d) :
  ~ (exists S, paper_main_head_section kappa W S) ->
  paper_main_head_support Z (paper_main_head_section kappa W) = 0.
Proof.
move=> HE; rewrite /paper_main_head_support.
have -> : [set paper_main_pairing Z S | S in paper_main_head_section kappa W] = set0.
  apply/seteqP; split=> [y [S HS _] | y] //.
  by exfalso; apply: HE; exists S.
exact: sup0.
Qed.

Lemma paper_main_head_section_unit {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d) S :
  paper_main_head_section kappa W S -> paper_main_frobenius S = 1.
Proof. by move=> [_ [H _]]. Qed.

Theorem paper_main_head_section_support_bound {d m : nat} (kappa : R)
    (W : 'I_m -> 'M[R]_d) (Z : 'M[R]_d) :
  `|paper_main_head_support Z (paper_main_head_section kappa W)| <= paper_main_frobenius Z.
Proof.
have [[S HS] | HE] := pselect (exists S, paper_main_head_section kappa W S); last first.
  by rewrite paper_main_head_section_support_empty // normr0; exact: pmh_frobenius_ge0.
have Hunit := @paper_main_head_section_unit d m kappa W.
have Hup : paper_main_head_support Z (paper_main_head_section kappa W) <=
    paper_main_frobenius Z.
  apply: ge_sup; first by exists (paper_main_pairing Z S), S.
  exact: pmh_support_ubound.
have Hlo : - paper_main_frobenius Z <=
    paper_main_head_support Z (paper_main_head_section kappa W).
  apply: le_trans (pmh_support_ge _ Z _ S Hunit HS).
  have Hb := pmh_pairing_frobenius_bound _ Z S.
  rewrite (Hunit S HS) mulr1 in Hb.
  by move: Hb; rewrite ler_norml => /andP [].
by rewrite ler_norml Hlo Hup.
Qed.

(* Scalar and set-level facts for the characterization. *)

Lemma paper_main_head_section_tol_w (a q : R) :
  0 <= a -> 0 < q -> a * (q / 2) <= (1 + a ^+ 2) * q.
Proof.
move=> Ha Hq.
have H1 : 0 <= 1 + a ^+ 2 - a / 2 by nra.
have H2 := mulr_ge0 (ltW Hq) H1.
nra.
Qed.

Lemma paper_main_head_section_tol_chain (c su u v a q : R) :
  0 <= a -> 0 < q -> c <= su -> su - q / 2 < u -> v <= a * (q / 2) ->
  c - (1 + a ^+ 2) * q <= u - v.
Proof.
move=> Ha Hq Hc Hu Hv.
have H1 : 0 <= 1 + a ^+ 2 - (1 + a) / 2 by nra.
have H2 := mulr_ge0 (ltW Hq) H1.
nra.
Qed.

Lemma paper_main_head_section_lift n (kappa : R) (P : 'M[R]_(S n)) :
  paper_main_head_cone_sphere kappa P ->
  exists w, pmhw_aug (S n) kappa w /\ pmhw_S (S n) w = P.
Proof.
move=> [[lam [Hl [H1 H2]]] HF].
exists (pmhw_lift (S n) P lam); split; last exact: pmhw_S_lift.
exact: (pmhw_lift_aug (S n) P lam kappa (ltn0Sn n) Hl H1 H2 HF).
Qed.

Lemma paper_main_head_section_aug_sphere n (kappa : R) w :
  1 <= kappa -> pmhw_aug (S n) kappa w ->
  paper_main_head_cone_sphere kappa (pmhw_S (S n) w).
Proof.
move=> Hk [Ha [Hb [H1 [H2 H3]]]]; split.
  exists (pmhw_lam (S n) w); split => //.
  apply: lt_le_trans Ha; rewrite invr_gt0 mulr_gt0 // ?sqrtr_gt0 ?ltr0n //.
  exact: lt_le_trans ltr01 Hk.
by rewrite /paper_main_frobenius H3 sqrtr1.
Qed.

Lemma paper_main_head_section_pairing_continuous n (A : 'M[R]_(S n)) :
  continuous (fun w : 'rV[R]_(S n * S n + 1) => paper_main_pairing A (pmhw_S (S n) w)).
Proof.
rewrite /paper_main_pairing.
apply: pmg_continuous_sum => i; apply: pmg_continuous_sum => j.
by apply: pmg_continuousM; [exact: pmg_continuous_cst | exact: pmhw_S_continuous].
Qed.

(* The countable characterization, with fixed nets. *)

Lemma paper_main_head_section_level_iff n m (kappa : R) (W : 'I_m -> 'M[R]_(S n))
    (Z : 'M[R]_(S n)) (c : R) (B : nat -> nat -> 'M[R]_(S n)) (s : nat -> nat) :
  1 <= kappa ->
  (forall j t, (t < s j)%N -> paper_main_head_cone_sphere kappa (B j t)) ->
  (forall j P, paper_main_head_cone_sphere kappa P ->
    exists t, (t < s j)%N /\ paper_main_frobenius (P - B j t) <= j.+1%:R^-1 / 2%:R) ->
  ((exists S, paper_main_head_section kappa W S) /\
    c <= paper_main_head_support Z (paper_main_head_section kappa W)) <->
  (forall j, exists t, (t < s j)%N /\
    (forall k, `|paper_main_pairing (W k) (B j t)| <=
      (1 + paper_main_pairing (W k) (W k)) * j.+1%:R^-1) /\
    c - (1 + paper_main_pairing Z Z) * j.+1%:R^-1 <= paper_main_pairing Z (B j t)).
Proof.
move=> Hk HB Hnet.
have Hunit := @paper_main_head_section_unit (S n) m kappa W.
split.
- move=> [[S0 HS0] Hc] j.
  pose e : R := j.+1%:R^-1 / 2%:R.
  have Hj : 0 < j.+1%:R^-1 :> R by rewrite invr_gt0 ltr0n.
  have He : 0 < e by rewrite divr_gt0 // ltr0n.
  set E := [set paper_main_pairing Z S | S in paper_main_head_section kappa W].
  have Hsup : has_sup E.
    split; first by exists (paper_main_pairing Z S0), S0.
    by exists (paper_main_frobenius Z); exact: pmh_support_ubound.
  have [_ [S HS <-] HSe] := sup_adherent He Hsup.
  have [HScond [HSF HSker]] := HS.
  have [t [Ht Hdist]] := Hnet j S (conj HScond HSF).
  exists t; split => //.
  split.
  + move=> k.
    have HW0 := pmh_frobenius_ge0 _ (W k).
    have Hk0 : paper_main_pairing (W k) (B j t) = - paper_main_pairing (W k) (S - B j t).
      by rewrite pmh_pairingBr HSker sub0r opprK.
    rewrite Hk0 normrN.
    apply: le_trans (pmh_pairing_frobenius_bound _ (W k) (S - B j t)) _.
    apply: le_trans (ler_wpM2l HW0 Hdist) _.
    rewrite -pmh_frobenius_sqr.
    exact: (paper_main_head_section_tol_w _ _ HW0 Hj).
  + have HZ0 := pmh_frobenius_ge0 _ Z.
    have HZd : `|paper_main_pairing Z (S - B j t)| <=
        paper_main_frobenius Z * (j.+1%:R^-1 / 2).
      apply: (le_trans (pmh_pairing_frobenius_bound _ Z (S - B j t))).
      by have := ler_wpM2l HZ0 Hdist.
    move: HZd; rewrite ler_norml => /andP [_ HZd2].
    have HZP : paper_main_pairing Z (B j t) =
        paper_main_pairing Z S - paper_main_pairing Z (S - B j t).
      by rewrite pmh_pairingBr opprB addrC subrK.
    rewrite -pmh_frobenius_sqr HZP.
    exact: (paper_main_head_section_tol_chain _ (sup E) _ _ _ _ HZ0 Hj Hc HSe HZd2).
- move=> H.
  have [f Hf] := choice H.
  have Hl : forall j, exists w, pmhw_aug (S n) kappa w /\ pmhw_S (S n) w = B j (f j).
    by move=> j; apply: paper_main_head_section_lift; apply: HB; case: (Hf j).
  have [g Hg] := choice Hl.
  have Hbox : forall j, pm_box (S n * S n + 1) 1 (g j).
    move=> j k; have := pmhw_aug_sub_box (S n) kappa (ltn0Sn n) Hk _ (proj1 (Hg j)) k.
    by rewrite /= in_itv.
  have [p [_ Hclp]] := pm_box_cluster _ g 1 Hbox.
  have Hp : pmhw_aug (S n) kappa p.
    rewrite ((closure_id _).1 (pmhw_aug_closed (S n) kappa)).
    move=> A HA; have [j [_ HAj]] := Hclp A HA 0%N.
    by exists (g j); split => //; exact: (proj1 (Hg j)).
  pose Sp := pmhw_S n.+1 p.
  have [HScond HSF] := paper_main_head_section_aug_sphere n kappa p Hk Hp.
  have Hker : forall k, paper_main_pairing (W k) Sp = 0.
    move=> k.
    have Hc0 : {for p, continuous (fun w => paper_main_pairing (W k) (pmhw_S n.+1 w))}.
      exact: paper_main_head_section_pairing_continuous.
    have Ha0 : 0 <= 1 + paper_main_pairing (W k) (W k).
      by apply: addr_ge0; [exact: ler01 | exact: paper_main_pairing_self_ge0].
    have Hbd : forall j, `|(fun w => paper_main_pairing (W k) (pmhw_S n.+1 w)) (g j)| <=
        (1 + paper_main_pairing (W k) (W k)) / j.+1%:R.
      move=> j /=; rewrite (proj2 (Hg j)).
      by have [_ [Hw _]] := Hf j; exact: Hw.
    exact: (pm_cluster_value_zero _ g p _ _ Hc0 Ha0 Hclp Hbd).
  have HcS : c <= paper_main_pairing Z Sp.
    have Hc0 : {for p, continuous (fun w => paper_main_pairing Z (pmhw_S n.+1 w))}.
      exact: paper_main_head_section_pairing_continuous.
    have Ha0 : 0 <= 1 + paper_main_pairing Z Z.
      by apply: addr_ge0; [exact: ler01 | exact: paper_main_pairing_self_ge0].
    have Hbd : forall j, c - (1 + paper_main_pairing Z Z) / j.+1%:R <=
        (fun w => paper_main_pairing Z (pmhw_S n.+1 w)) (g j).
      move=> j /=; rewrite (proj2 (Hg j)).
      by have [_ [_ Hz]] := Hf j; exact: Hz.
    exact: (pm_cluster_value_ge _ g p _ _ _ Hc0 Ha0 Hclp Hbd).
  have HS : paper_main_head_section kappa W Sp by split; [exact: HScond | split].
  split; first by exists Sp.
  exact: le_trans HcS (pmh_support_ge _ Z _ Sp Hunit HS).
Qed.

Lemma paper_main_head_section_guard {dX : measure_display} {X : measurableType dX}
    (b : bool) (A : set X) :
  measurable A -> measurable [set x | b /\ A x].
Proof.
case: b => mA.
  have -> : [set x | true /\ A x] = A by apply/seteqP; split=> x // [_ H].
  exact: mA.
have -> : [set x | false /\ A x] = set0 by apply/seteqP; split=> x // [H _].
exact: measurable0.
Qed.

(* A sequence of fixed nets. *)

Lemma paper_main_head_section_nets n (kappa : R) :
  1 <= kappa ->
  exists (B : nat -> nat -> 'M[R]_(S n)) (s : nat -> nat),
    (forall j t, (t < s j)%N -> paper_main_head_cone_sphere kappa (B j t)) /\
    (forall j P, paper_main_head_cone_sphere kappa P ->
      exists t, (t < s j)%N /\ paper_main_frobenius (P - B j t) <= j.+1%:R^-1 / 2%:R).
Proof.
move=> Hk.
have Hnets : forall j : nat, exists Bs : (nat -> 'M[R]_(S n)) * nat,
    (forall t, (t < Bs.2)%N -> paper_main_head_cone_sphere kappa (Bs.1 t)) /\
    (forall P, paper_main_head_cone_sphere kappa P ->
      exists t, (t < Bs.2)%N /\ paper_main_frobenius (P - Bs.1 t) <= j.+1%:R^-1 / 2%:R).
  move=> j.
  have He : 0 < j.+1%:R^-1 / 2%:R :> R by rewrite divr_gt0 // ?invr_gt0 ltr0n.
  have [B [s [_ [HB Hc]]]] := paper_main_cone_net_family n kappa _ Hk He.
  by exists (B, s).
have [Bs HBs] := choice Hnets.
exists (fun j => (Bs j).1), (fun j => (Bs j).2); split.
- by move=> j t Ht; exact: (proj1 (HBs j) t Ht).
- by move=> j P HP; exact: (proj2 (HBs j) P HP).
Qed.

(* Measurability on any measurable space. *)

Theorem paper_main_head_section_level_measurable {dX : measure_display}
    {X : measurableType dX} n m (kappa : R) (W : 'I_m -> X -> 'M[R]_(S n))
    (Z : X -> 'M[R]_(S n)) (c : R) :
  1 <= kappa ->
  (forall k a b, measurable_fun [set: X] ((fun x => W k x a b) : X -> T)) ->
  (forall a b, measurable_fun [set: X] ((fun x => Z x a b) : X -> T)) ->
  measurable [set x | (exists S, paper_main_head_section kappa (fun k => W k x) S) /\
    c <= paper_main_head_support (Z x) (paper_main_head_section kappa (fun k => W k x))].
Proof.
move=> Hk mW mZ.
have [B [s [HB Hnet]]] := paper_main_head_section_nets n kappa Hk.
pose A j t := [set x : X | (forall k, `|paper_main_pairing (W k x) (B j t)| <=
      (1 + paper_main_pairing (W k x) (W k x)) / j.+1%:R) /\
    c - (1 + paper_main_pairing (Z x) (Z x)) / j.+1%:R <= paper_main_pairing (Z x) (B j t)].
have -> : [set x | (exists S, paper_main_head_section kappa (fun k => W k x) S) /\
    c <= paper_main_head_support (Z x) (paper_main_head_section kappa (fun k => W k x))] =
    \bigcap_j \bigcup_t [set x | (t < s j)%N /\ A j t x].
  apply/seteqP; split=> x Hx.
  - have H := (paper_main_head_section_level_iff n m kappa (fun k => W k x) (Z x) c B s
      Hk HB Hnet).1 Hx.
    by move=> j _; have [t [Ht HA]] := H j; exists t.
  - apply/(paper_main_head_section_level_iff n m kappa (fun k => W k x) (Z x) c B s Hk HB Hnet).
    by move=> j; have [t _ [Ht HA]] := Hx j I; exists t.
apply: bigcapT_measurable => j; apply: bigcupT_measurable => t.
apply: paper_main_head_section_guard.
have Hpair : forall k, measurable_fun [set: X]
    ((fun x => paper_main_pairing (W k x) (B j t)) : X -> T).
  move=> k; apply: paper_main_finite_pairing_measurable => a b; [exact: mW | exact: measurable_cst].
have HZpair : measurable_fun [set: X] ((fun x => paper_main_pairing (Z x) (B j t)) : X -> T).
  by apply: paper_main_finite_pairing_measurable => a b; [exact: mZ | exact: measurable_cst].
have HWW : forall k, measurable_fun [set: X]
    ((fun x => paper_main_pairing (W k x) (W k x)) : X -> T).
  by move=> k; apply: paper_main_finite_pairing_measurable => a b; exact: mW.
have HZZ : measurable_fun [set: X] ((fun x => paper_main_pairing (Z x) (Z x)) : X -> T).
  by apply: paper_main_finite_pairing_measurable => a b; exact: mZ.
have -> : A j t = (\bigcap_(k in [set: 'I_m]) [set x | `|paper_main_pairing (W k x) (B j t)| <=
      (1 + paper_main_pairing (W k x) (W k x)) / j.+1%:R]) `&`
    [set x | c - (1 + paper_main_pairing (Z x) (Z x)) / j.+1%:R <=
      paper_main_pairing (Z x) (B j t)].
  apply/seteqP; split=> x.
  - by move=> [H1 H2]; split=> // k _; exact: H1.
  - by move=> [H1 H2]; split=> // k; exact: (H1 k I).
apply: measurableI.
- apply: fin_bigcap_measurable; first exact: finite_finset.
  move=> k _; apply: paper_main_head_section_le_measurable.
  + exact: (measurableT_comp (@normr_measurable _ _) (Hpair k)).
  + apply: measurable_funM; last exact: measurable_cst.
    by apply: measurable_funD; [exact: measurable_cst | exact: HWW].
- apply: paper_main_head_section_le_measurable; last exact: HZpair.
  apply: measurable_funB; first exact: measurable_cst.
  apply: measurable_funM; last exact: measurable_cst.
  by apply: measurable_funD; [exact: measurable_cst | exact: HZZ].
Qed.

Theorem paper_main_head_section_nonempty_measurable {dX : measure_display}
    {X : measurableType dX} n m (kappa : R) (W : 'I_m -> X -> 'M[R]_(S n)) :
  1 <= kappa ->
  (forall k a b, measurable_fun [set: X] ((fun x => W k x a b) : X -> T)) ->
  measurable [set x | exists S, paper_main_head_section kappa (fun k => W k x) S].
Proof.
move=> Hk mW.
have H := paper_main_head_section_level_measurable n m kappa W (fun _ => 0) 0 Hk mW
  (fun a b => measurable_cst _).
rewrite (_ : [set x | exists S, paper_main_head_section kappa (fun k => W k x) S] =
    [set x | (exists S, paper_main_head_section kappa (fun k => W k x) S) /\
      0 <= paper_main_head_support 0 (paper_main_head_section kappa (fun k => W k x))]) //.
apply/seteqP; split=> x; last by case.
move=> [S HS]; split; first by exists S.
rewrite -(pmh_pairing0l _ S).
exact: (pmh_support_ge _ 0 _ S (@paper_main_head_section_unit _ _ kappa _) HS).
Qed.

Theorem paper_main_head_section_support_measurable {dX : measure_display}
    {X : measurableType dX} n m (kappa : R) (W : 'I_m -> X -> 'M[R]_(S n))
    (Z : X -> 'M[R]_(S n)) :
  1 <= kappa ->
  (forall k a b, measurable_fun [set: X] ((fun x => W k x a b) : X -> T)) ->
  (forall a b, measurable_fun [set: X] ((fun x => Z x a b) : X -> T)) ->
  measurable_fun [set: X] ((fun x => paper_main_head_support (Z x)
    (paper_main_head_section kappa (fun k => W k x))) : X -> T).
Proof.
move=> Hk mW mZ.
apply: paper_main_head_section_measurable_fun_ge => c.
have HNE := paper_main_head_section_nonempty_measurable n m kappa W Hk mW.
have HL := paper_main_head_section_level_measurable n m kappa W Z c Hk mW mZ.
have Hc0 : measurable [set x : X | (c <= 0) /\ [set: X] x].
  exact: (@paper_main_head_section_guard _ X (c <= 0) [set: X] measurableT).
have -> : [set x | c <= paper_main_head_support (Z x)
      (paper_main_head_section kappa (fun k => W k x))] =
    [set x | (exists S, paper_main_head_section kappa (fun k => W k x) S) /\
      c <= paper_main_head_support (Z x) (paper_main_head_section kappa (fun k => W k x))] `|`
    (~` [set x | exists S, paper_main_head_section kappa (fun k => W k x) S] `&`
      [set x : X | (c <= 0) /\ [set: X] x]).
  apply/seteqP; split=> x.
  - move=> /= Hc; case: (pselect (exists S, paper_main_head_section kappa (fun k => W k x) S)).
      by move=> HNEx; left.
    move=> HNEx; right.
    rewrite (paper_main_head_section_support_empty kappa (fun k => W k x) (Z x) HNEx) in Hc.
    by split.
  - case=> [[_ Hc] | [HnNE [Hc0x _]]] //=.
    by rewrite (paper_main_head_section_support_empty kappa (fun k => W k x) (Z x) HnNE).
by apply: measurableU => //; apply: measurableI => //; exact: measurableC.
Qed.
