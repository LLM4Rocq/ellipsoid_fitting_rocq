(* The actual non-backtracking column remainder endpoint (A38).

   Interface (R) of the lower edge: for N(d) with eventual density >= c > 0
   and eventually 0 < N(d) <= d^2, every K and eta > 0 have actual measurable
   bad events E_d with probability tending to 0 such that, for all large d
   and x outside E_d, every k < K satisfies
     pmlo_opb N (pmlo_E N C X kap s k) eta,
   with C = 'I_d * 'I_d, X = pmnb_X d (tval x), M = 'C(d, 2),
   kap = (sqrt (N M))^-1 and s = kap N.
   The constants are chosen before the data: C0 = 2 + 109 / c (A35),
   delta = paper_main_remainder_tolerance K (2 C0) eta (A38). E_d is the A35
   frame event at delta. For large d outside it, the A35 frame premises,
   the A37 entry radius d <= C0 N delta^2 and binomial bound N <= 4 M, and
   the kap normalization (M142) feed the deterministic M143 bound
     pmlo_opb N (pmlo_E ..k) (C_k(2 C0) delta),
   and C_k(2 C0) delta <= eta for k < K. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions
  PaperMainSquarefreeEdgeLower PaperMainSquarefreeWalkNB PaperMainColumnRemainder
  PaperMainColumnConcentrationFrameEvents PaperMainColumnConcentrationFrame
  PaperMainColumnConcentrationScaling PaperMainColumnRemainderTolerance
  PaperMainColumnRemainderScaling PaperMainColumnRemainderFrame.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma pmcrp_constant_eq k h :
  paper_main_remainder_constant k h = (k.+2)%:R * (2 * h) ^+ k.+2 + 4 ^+ k.+1 * h + 2 ^+ k.
Proof. by rewrite /paper_main_remainder_constant addn2 addn1. Qed.

Theorem paper_main_column_remainder_probability (N : nat -> nat) (c : R) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N -> (0 < N d)%N /\ (N d <= d ^ 2)%N) ->
  forall (K : nat) (eta : R), 0 < eta ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D : nat, forall d, (D <= d)%N -> forall x : paper_main_sample (N d) d, ~ E d x ->
      forall k, (k < K)%N ->
        pmlo_opb (N d)
          (pmlo_E (N d) [the finType of ('I_d * 'I_d)%type] (@pmnb_X R d (tval x) (N d))
             ((Num.sqrt ((N d)%:R * ('C(d, 2))%:R))^-1)
             ((Num.sqrt ((N d)%:R * ('C(d, 2))%:R))^-1 * (N d)%:R) k)
          eta.
Proof.
move=> Hc Hlow Hup K eta Heta.
have [HC2 _] := paper_main_frame_constant_ge c Hc.
set C0 := paper_main_frame_constant c in HC2 *.
have HC0' : 0 < C0 by apply: lt_le_trans HC2; rewrite ltr0n.
have HC0 : 0 <= C0 := ltW HC0'.
have Hh : 0 <= 2 * C0 by rewrite mulr_ge0 // ler0n.
set delta := paper_main_remainder_tolerance K (2 * C0) eta.
have [Hd0 [Hd1 Htol]] := paper_main_remainder_tolerance_spec K (2 * C0) eta Hh Heta.
have [_ Hframe] := paper_main_column_frame N c Hc Hlow Hup.
have [E [mE [limE [D1 HD1]]]] := Hframe delta Hd0.
have [D2 HD2] := paper_main_frame_entry_radius N c C0 delta Hc HC0' Hd0 Hlow.
have [D3 HD3] := Hup.
exists E; split => //; split => //.
exists (maxn (maxn D1 D2) (maxn D3 2)) => d Hd x Hx k Hk.
rewrite !geq_max in Hd; case/andP: Hd => /andP [HdD1 HdD2] /andP [HdD3 Hd2].
have Hgood := HD1 d HdD1 x Hx.
have Hent := HD2 d HdD2.
have [HN HNd] := HD3 d HdD3.
have [HM0 HN4M] := paper_main_frame_binomial_bounds (N d) d Hd2 HN HNd.
have HN0 : 0 < (N d)%:R :> R by rewrite ltr0n.
have [Hk0 [Hk1 Hk2]] := pmcr_normalization (N d)%:R ('C(d, 2))%:R HN0 HM0.
have Hs := pmcr_normalized_count_bound (N d)%:R ('C(d, 2))%:R _ (ltW Hk0) HN0 HM0 Hk1 HN4M.
have HB := paper_main_column_remainder_frame_scaled (N d) d C0 delta _ x
  HN HC0 Hd0 Hd1 (ltW Hk0) Hs Hk2 Hent Hgood k.
apply: (pmlo_opb_le (N d) _ _ _ HB).
have H := Htol k Hk; rewrite pmcrp_constant_eq in H.
exact H.
Qed.
