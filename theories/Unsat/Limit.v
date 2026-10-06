(* The UNSAT limit at fixed density and its extension to supercritical
   sample-size sequences.

   For gamma in (1/4, 1/2) and N(d) = paper_main_fixed_count gamma d:
   1. paper_main_unsat_orientation_constants fixes kappa, e, c, L, eps, tau
      and d0 from gamma alone, with events for each orientation, and
      paper_main_orientation_rank_bound fixes rmax with
      1/(eps/2)^2 <= rmax, all before d. Put
      C = paper_main_orientation_entropy rmax tau and
      a = gamma (e/4)^2 / 4 > 0.
   2. For every large d, the union F_d of these events given by
      paper_main_orientation_union_fit (cutoff eps/2) is measurable, has
      probability at most
        (rmax + 1) exp (C (d + 1)) exp (- N (e/4)^2 / 2)
          <= (rmax + 1) exp (C (d + 1)) exp (- a d^2),
      and contains every fit outside the feature upper event: there the raw
      Gram matrix is at most (3 N + 106 d^2) I and
      3 N + 106 d^2 <= 109 d^2 <= N L^2. For small d, F_d is empty. The
      events are chosen for each d separately; no measurability in d is
      used.
   3. For large d, P(fit) <= P(feature upper event) + P(F_d), and both tend
      to 0 (paper_main_feature_upper_edge and
      paper_main_unsat_orientation_union_limit). Hence the fit probability
      at fixed density tends to 0 (paper_main_unsat_fixed_density_limit).
   4. With the measurability of the fit event (pm_fit_event_measurable),
      the reduction paper_main_unsat_from_fixed gives P(fit) -> 0 for every
      sample-size sequence whose density has liminf greater than 1/4
      (paper_main_unsat_supercritical_limit). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Feature.GramBlocks Feature.LossControl Asymptotics
  Fixed.Density Measurability.Fit SquareFree.EdgeUpperLimit
  Feature.UpperProbability Fixed.CountBounds Unsat.Rates Orientation.Net
  Orientation.Witness Orientation.Family Orientation.Union Unsat.Orientation.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* An eventual scalar threshold. *)

Lemma paper_main_unsat_limit_small_exp (c : R) : (0 < c)%Rcoq ->
  exists D : nat, forall d, (D <= d)%N -> (exp (- c * (INR d) ^ 2) <= 1 / 4)%Rcoq.
Proof.
move=> Hc.
have [J HJ] := INR_unbounded (3 / c)%Rcoq.
exists (S J) => d Hd.
have HdJ : (S J <= d)%coq_nat by apply/ssrnat.leP.
have Hd1 : (1 <= INR d)%Rcoq by apply: (le_INR 1); lia.
have HdJ' : (3 / c < INR d)%Rcoq by have := le_INR J d ltac:(lia); lra.
have Hcd : (3 <= c * INR d ^ 2)%Rcoq.
  have H1 : (c * (3 / c) < c * INR d)%Rcoq by apply: Rmult_lt_compat_l.
  have E : (c * (3 / c) = 3)%Rcoq by field; lra.
  have Hsq : (INR d <= INR d ^ 2)%Rcoq by nra.
  have := Rmult_le_compat_l c _ _ (Rlt_le _ _ Hc) Hsq; lra.
have H1 := exp_ineq1_le (c * INR d ^ 2)%Rcoq.
have Hpos := exp_pos (c * INR d ^ 2)%Rcoq.
have E : (exp (- c * INR d ^ 2) = / exp (c * INR d ^ 2))%Rcoq.
  by rewrite -exp_Ropp; f_equal; ring.
rewrite E.
apply: (Rmult_le_reg_l (exp (c * INR d ^ 2))) => //.
rewrite Rinv_r; last lra.
lra.
Qed.

(* The fixed-density limit from events for each orientation, of the form
   given by paper_main_unsat_orientation_constants. *)

Theorem paper_main_unsat_fixed_density_limit_from_events (gamma kappa e c L eps tau : R) (d0 : nat) :
  1 / 4%:R < gamma -> gamma < 1 / 2%:R ->
  (0 < kappa)%Rcoq -> (kappa <= gamma / 2)%Rcoq -> (0 < e)%Rcoq -> (0 < c)%Rcoq -> (0 < L)%Rcoq ->
  (gamma / 2 * L ^ 2 = 109)%Rcoq -> (0 < eps)%Rcoq -> (0 < tau)%Rcoq -> (tau <= 1 / 8)%Rcoq ->
  (eps / 2 + tau ^ 2 <= eps)%Rcoq ->
  (forall N d r (O : 'M[R]_d), O^T *m O = 1%:M -> (d0 <= d)%N -> (r < d)%N ->
     (INR r <= sqrt (INR d) + 1)%Rcoq ->
     (Rabs (INR N - gamma * (INR d) ^ 2) <= kappa * (INR d) ^ 2)%Rcoq ->
     (exp (- c * (INR d) ^ 2) <= 1 / 4)%Rcoq ->
     exists E : set (paper_main_sample N d), measurable E /\
       (paper_main_probability N d E <= ((exp (- (INR N * (e / 4) ^ 2) / 2))%Rcoq)%:E)%E /\
       forall (x : paper_main_sample N d) K,
         0 <= K -> paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
         (K <= INR N * L ^ 2)%Rcoq ->
         (exists A b, paper_main_orientation_admissible r O eps L A b /\
           (paper_main_quadratic_risk N d x A b <= 16 * L * tau)%Rcoq) -> E x) ->
  paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count gamma d) d
    (paper_main_fit_event (paper_main_fixed_count gamma d) d)) 0.
Proof.
move=> Hg14 Hg12 Hk Hk2 He Hc HL HLeq Heps Ht Ht8 Hept Hev.
have Hg14R : (1 / 4 < gamma)%Rcoq.
  by move/RltP: Hg14; rewrite -RdivE -INRE INR_IZR_INZ.
have Hg12R : (gamma < 1 / 2)%Rcoq.
  by move/RltP: Hg12; rewrite -RdivE -INRE INR_IZR_INZ.
have Hg0 : (0 < gamma)%Rcoq by lra.
have Hg1 : (gamma <= 1)%Rcoq by lra.
set Nf := paper_main_fixed_count gamma.
set eps0 := (eps / 2)%Rcoq.
have He0R : (0 < eps0)%Rcoq by rewrite /eps0; lra.
have He0 : 0 < eps0 by apply/RltP.
have [rmax [HR _]] := paper_main_orientation_rank_bound eps0 He0.
set C := paper_main_orientation_entropy rmax tau.
have HC : (0 <= C)%Rcoq by exact: paper_main_orientation_entropy_nonneg.
set a := (gamma * (e / 4) ^ 2 / 4)%Rcoq.
have Ha : (0 < a)%Rcoq.
  rewrite /a; apply: Rmult_lt_0_compat; last lra.
  by apply: Rmult_lt_0_compat => //; apply: pow_lt; lra.
have [D1 HD1] := paper_main_fixed_count_near gamma kappa (Rlt_le _ _ Hg0) Hk.
have [D2 HD2] := paper_main_fixed_count_density_bounds gamma Hg0 Hg1.
have [D3 HD3] := paper_main_unsat_limit_small_exp c Hc.
set D := maxn (maxn d0 (rmax * rmax + 1)) (maxn D1 (maxn D2 D3)).
have HDmax : forall d, (D <= d)%N ->
    [/\ (d0 <= d)%N, (rmax * rmax + 1 <= d)%N, (D1 <= d)%N, (D2 <= d)%N & (D3 <= d)%N].
  by move=> d; rewrite !geq_max => /andP [/andP [-> ->] /andP [-> /andP [-> ->]]].
have Heps' : (0 <= eps)%Rcoq by lra.
have HepsR : 0 <= eps by apply/RleP.
have HtR : 0 < tau by apply/RltP.
have HL' : (0 <= L)%Rcoq by lra.
have HLR : 0 <= L by apply/RleP.
have Ht8R : tau <= 1 / 8.
  apply/RleP.
  rewrite -RdivE.
  have E8 : (8%R : R) = INR 8 by rewrite INRE.
  rewrite E8 INR_IZR_INZ /=; exact: Ht8.
have HeptR : eps0 + tau ^+ 2 <= eps.
  by apply/RleP; rewrite -RpowE -RplusE /eps0.
(* For each d, the union event of paper_main_orientation_union_fit (empty
   for small d). *)
have Hpick : forall d, exists F : set (paper_main_sample (Nf d) d),
    (D <= d)%N -> measurable F /\
      (paper_main_probability (Nf d) d F <=
        ((INR (rmax + 1) * exp (C * (INR d + 1)) *
          exp (- (INR (Nf d) * (e / 4) ^ 2) / 2))%Rcoq)%:E)%E /\
      forall (x : paper_main_sample (Nf d) d) (K : R), 0 <= K ->
        paper_main_loewner_le (paper_main_feature_gram (Nf d) d x) (K *: 1%:M) ->
        (K <= INR (Nf d) * L ^ 2)%Rcoq -> paper_main_fit_event (Nf d) d x -> F x.
  move=> d.
  case: (boolP (D <= d)%N) => Hd; last by exists set0 => Hd'; exfalso; move/negP: Hd; apply.
  have [Hd0 HdR HdD1 HdD2 HdD3] := HDmax d Hd.
  have [_ Hnear] := HD1 d (elimT ssrnat.leP HdD1).
  have [Hdpos [HNpos [HNd Hlow]]] := HD2 d (elimT ssrnat.leP HdD2).
  have Hsmall := HD3 d HdD3.
  have HdR' : Nat.le (Nat.add (Nat.mul rmax rmax) 1) d.
    by apply/ssrnat.leP; rewrite plusE multE.
  have Hrank : forall r, (r <= rmax)%N -> (r < d)%N /\ (INR r <= sqrt (INR d) + 1)%Rcoq.
    move=> r Hr.
    have [H1 H2] := paper_main_unsat_fixed_rank rmax d r (elimT ssrnat.leP Hr) HdR'.
    by split => //; apply/ssrnat.ltP.
  have HRd : (rmax < d)%N by have [] := Hrank rmax (leqnn rmax).
  have Hp : (0 <= exp (- (INR (Nf d) * (e / 4) ^ 2) / 2))%Rcoq by apply: Rlt_le; apply: exp_pos.
  have Hin : forall r, (r <= rmax)%N -> forall O : 'M[R]_d, O^T *m O = 1%:M ->
      exists E : set (paper_main_sample (Nf d) d), measurable E /\
        (paper_main_probability (Nf d) d E <= (exp (- (INR (Nf d) * (e / 4) ^ 2) / 2))%:E)%E /\
        forall (x : paper_main_sample (Nf d) d) (K : R), 0 <= K ->
          paper_main_loewner_le (paper_main_feature_gram (Nf d) d x) (K *: 1%:M) ->
          (K <= INR (Nf d) * L ^ 2)%Rcoq ->
          (exists (A : 'M[R]_d) (b : R), paper_main_orientation_admissible r O eps L A b /\
             (paper_main_quadratic_risk (Nf d) d x A b <= 16 * L * tau)%Rcoq) -> E x.
    move=> r Hr O HO; have [Hrd Hrs] := Hrank r Hr.
    exact: (Hev (Nf d) d r O HO Hd0 Hrd Hrs Hnear Hsmall).
  have [F [mF [PF HF]]] := paper_main_orientation_union_fit d eps0 eps tau L
    (exp (- (INR (Nf d) * (e / 4) ^ 2) / 2)) rmax (Nf d) He0 HepsR HtR Ht8R HeptR HLR HR HRd
    HNpos Hp Hin.
  by exists F => _; split => //; split => //.
pose F := fun d => proj1_sig (cid (Hpick d)).
have HF : forall d, (D <= d)%N -> measurable (F d) /\
    (paper_main_probability (Nf d) d (F d) <=
      ((INR (rmax + 1) * exp (C * (INR d + 1)) *
        exp (- (INR (Nf d) * (e / 4) ^ 2) / 2))%Rcoq)%:E)%E /\
    forall (x : paper_main_sample (Nf d) d) (K : R), 0 <= K ->
      paper_main_loewner_le (paper_main_feature_gram (Nf d) d x) (K *: 1%:M) ->
      (K <= INR (Nf d) * L ^ 2)%Rcoq -> paper_main_fit_event (Nf d) d x -> F d x.
  by move=> d; exact: (proj2_sig (cid (Hpick d))).
(* The feature upper event (paper_main_feature_upper_edge). *)
have Hg2R : (0 < gamma / 2)%Rcoq by lra.
have Hg2 : 0 < (gamma / 2)%Rcoq by apply/RltP.
have Hlowev := paper_main_fixed_count_eventually_lower gamma Hg0 Hg1.
have Hup : exists D0, forall d, (D0 <= d)%N -> (0 < Nf d)%N /\ (Nf d <= d ^ 2)%N.
  exists D2 => d Hd.
  by have [_ [HN [HNd _]]] := HD2 d (elimT ssrnat.leP Hd).
have [E [mE [limE HE]]] := paper_main_feature_upper_edge Nf (gamma / 2)%Rcoq Hg2 Hlowev Hup.
have E109 : (109%:R : R) = 109%Rcoq by rewrite -INRE INR_IZR_INZ.
apply: (paper_main_tends_to_zero_squeeze_eventually _
  (fun d => (paper_main_probability (Nf d) d (E d) + paper_main_probability (Nf d) d (F d))%E) D).
- by move=> d; exact: measure_ge0.
- move=> d Hd.
  have [mF [_ HFd]] := HF d Hd.
  have [_ _ _ HdD2 _] := HDmax d Hd.
  have [Hdpos [_ [HNd Hlow]]] := HD2 d (elimT ssrnat.leP HdD2).
  have EK : (109%:R * d%:R ^+ 2 : R) = (109 * INR d ^ 2)%Rcoq.
    by rewrite RmultE RpowE INRE E109.
  have HK : 0 <= (109%:R * d%:R ^+ 2 : R) by apply: mulr_ge0; [exact: ler0n | exact: sqr_ge0].
  have HKN : ((109%:R * d%:R ^+ 2 : R) <= INR (Nf d) * L ^ 2)%Rcoq.
    rewrite EK.
    have HL2 : (0 <= L ^ 2)%Rcoq by apply: pow2_ge_0.
    have H1 := Rmult_le_compat_r _ _ _ HL2 Hlow.
    have E2 : (gamma / 2 * INR d ^ 2 * L ^ 2 = (gamma / 2 * L ^ 2) * INR d ^ 2)%Rcoq by ring.
    by rewrite E2 HLeq in H1.
  have H1 : (paper_main_probability (Nf d) d (paper_main_fit_event (Nf d) d) <=
      paper_main_probability (Nf d) d (E d `|` F d))%E.
    apply: paper_main_probability_mono.
    + exact: pm_fit_event_measurable.
    + by apply: measurableU; [exact: mE | exact: mF].
    + move=> x Hx.
      case: (pselect (E d x)) => HEx; first by left.
      by right; exact: (HFd x _ HK (HE d x Hdpos HNd HEx) HKN Hx).
  apply: le_trans H1 _.
  by rewrite /paper_main_probability; exact: (measureU2 _ (mE d) mF).
- apply: pmel_tends_to_add.
  + by move=> d; exact: measure_ge0.
  + by move=> d; exact: measure_ge0.
  + exact: limE.
  + apply: (paper_main_unsat_orientation_union_limit _ (INR (rmax + 1)) C a).
    * exact: pos_INR.
    * exact: HC.
    * exact: Ha.
    * by move=> d; exact: measure_ge0.
    * exists D => d Hd.
      have Hd' : (D <= d)%N by apply/ssrnat.leP.
      have [_ [PF _]] := HF d Hd'.
      have [_ _ _ HdD2 _] := HDmax d Hd'.
      have [_ [_ [_ Hlow]]] := HD2 d (elimT ssrnat.leP HdD2).
      apply: le_trans PF _.
      rewrite lee_fin; apply/RleP.
      apply: Rmult_le_compat_l.
        by apply: Rmult_le_pos; [exact: pos_INR | apply: Rlt_le; exact: exp_pos].
      have He4 : (0 <= (e / 4) ^ 2)%Rcoq by apply: pow2_ge_0.
      have H1 := Rmult_le_compat_r _ _ _ He4 Hlow.
      have Hx : (- (INR (Nf d) * (e / 4) ^ 2) / 2 <= - a * INR d ^ 2)%Rcoq.
        by rewrite /a /Nf; lra.
      case: (Rle_lt_or_eq_dec _ _ Hx) => Hlt.
        by left; exact: exp_increasing.
      by right; rewrite Hlt.
Qed.

(* The UNSAT limit at fixed density, with the constants of
   paper_main_unsat_orientation_constants. *)

Theorem paper_main_unsat_fixed_density_limit (gamma : R) :
  1 / 4%:R < gamma -> gamma < 1 / 2%:R ->
  paper_main_tends_to (fun d => paper_main_probability (paper_main_fixed_count gamma d) d
    (paper_main_fit_event (paper_main_fixed_count gamma d) d)) 0.
Proof.
move=> Hg14 Hg12.
have Hg14R : (1 / 4 < gamma)%Rcoq.
  by move/RltP: Hg14; rewrite -RdivE -INRE INR_IZR_INZ.
have [kappa [e [c [L [eps [tau [d0 [Hk [Hk2 [He [Hc [HL [HLeq [Heps [Ht [Ht8 [Hept Hev]]]]]]]]]]]]]]]]] :=
  paper_main_unsat_orientation_constants gamma Hg14R.
exact: (paper_main_unsat_fixed_density_limit_from_events gamma kappa e c L eps tau d0
  Hg14 Hg12 Hk Hk2 He Hc HL HLeq Heps Ht Ht8 Hept Hev).
Qed.

(* Every sample-size sequence whose density has liminf greater than 1/4 is
   asymptotically UNSAT. *)

Theorem paper_main_unsat_supercritical_limit (n : nat -> nat) :
  paper_main_liminf_gt (paper_main_density n) (1 / 4%:R) ->
  paper_main_tends_to (fun d => paper_main_probability (n d) d (paper_main_fit_event (n d) d)) 0.
Proof.
apply: paper_main_unsat_from_fixed.
- exact: pm_fit_event_measurable.
- exact: paper_main_unsat_fixed_density_limit.
Qed.
