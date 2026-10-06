(* Exceptional sets for the uniform width of the regular selected heads.
   paper_main_regular_heads_width_good N n K c c0 Q L kappa eps x says that
   every head of x selected by a regular selection
   (paper_main_head_regular of PaperMainHeadWidthRegular) has section width
   at least (1/2 - eps) d, where d = n + 1.
   paper_main_head_width_regular_probability_fixed: assume N(d) <= C d^2
   for all large d, k0 >= 1, and that the Gaussian condition width
   paper_main_gaussian_condition_width n k0 is at least (1/2 - eps/2) d for
   all large n. Then there are measurable events A_d with probability
   tending to 0 such that, for all large d, every sample outside A_d
   satisfies paper_main_regular_heads_width_good with kappa = 2 k0^2. For
   each large d, the event of paper_main_head_width_regular_event_fixed is
   chosen with Hilbert's epsilon; its probability is at most
   2 N d^4 exp(-sqrt d / 2) <= 2 C d^6 exp(-sqrt d / 2). *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import AnalysisBridge GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions
  PaperMainGeometryHeadFeature PaperMainHeadSectionWidthLaw
  PaperMainHeadWidthRegular PaperMainClippingLimits
  PaperMainGaussianConditionWidth PaperMainGaussianConditionWidthBound.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition paper_main_regular_heads_width_good N n K c c0 Q L kappa eps
    (x : paper_main_sample N (S n)) : Prop :=
  forall m (h : paper_main_sample m (S n)) (s : 'I_m -> 'I_N),
    paper_main_head_regular N n m x s K c c0 Q L ->
    (forall k : 'I_m, paper_main_head_feature h k = paper_main_head_feature x (s k)) ->
    ((1/2-eps)*INR (S n) <= fine (paper_main_head_section_width n m kappa h))%Rcoq.

Theorem paper_main_head_width_regular_probability_fixed
    (N : nat -> nat) K c c0 Q L C k0 eps :
  (0 <= K)%Rcoq -> (0 < c)%Rcoq -> (0 < c0)%Rcoq ->
  (0 <= Q)%Rcoq -> (0 <= L)%Rcoq -> (0 <= C)%Rcoq -> (0 < eps)%Rcoq ->
  (exists D, forall d, Nat.le D d -> (INR (N d) <= C*(INR d)^2)%Rcoq) ->
  (1 <= k0)%Rcoq ->
  (exists D0, forall n, Nat.le D0 n ->
    ((1/2-eps/2)*INR (S n) <= paper_main_gaussian_condition_width n k0)%Rcoq) ->
  exists A : forall d, set (paper_main_sample (N d) d),
      (forall d, measurable (A d)) /\
      paper_main_tends_to (fun d => paper_main_probability (N d) d (A d)) 0 /\
      exists D, forall n, Nat.le D n -> forall x, ~ A (S n) x ->
        paper_main_regular_heads_width_good (N (S n)) n K c c0 Q L (2*k0^2)%Rcoq eps x.
Proof.
move=> HK Hc Hc0 HQ HL HC Heps [DN HN] Hk0 Hbase.
pose kappa := (2*k0^2)%Rcoq.
have [D HD] := paper_main_head_width_regular_event_fixed K c c0 Q L k0 eps
  HK Hc Hc0 HQ HL Heps Hk0 Hbase.
pose good n (A : set (paper_main_sample (N (S n)) (S n))) :=
  measurable A /\
  (paper_main_probability (N (S n)) (S n) A <=
    (2*INR (N (S n))*(INR (S n))^4*exp(-sqrt(INR (S n))/2))%Rcoq%:E)%E /\
  forall x, ~ A x -> paper_main_regular_heads_width_good (N (S n)) n K c c0 Q L kappa eps x.
pose pick n := epsilon (inhabits (@set0 (paper_main_sample (N (S n)) (S n)))) (good n).
have Hpick n : Nat.le D n -> good n (pick n).
{ move=> Hn; apply: epsilon_spec.
  have [A [mA [HA HW]]] := HD n Hn (N (S n)).
  exists A; split; first exact mA; split; first exact HA; exact HW. }
pose A d : set (paper_main_sample (N d) d) :=
  match d as j return set (paper_main_sample (N j) j) with
  | O => set0
  | S n => if (D <= n)%N then pick n else set0
  end.
exists A; split.
- case=> [|n]; first exact: measurable0.
  rewrite /A; case Hdn: (D <= n)%N; last exact: measurable0.
  have HdnN : Nat.le D n by exact: (elimT ssrnat.leP Hdn).
  exact: (proj1 (Hpick n HdnN)).
split.
- apply: (paper_main_sqrt_polynomial_tends_to_zero _ (2*C)%Rcoq 6).
  + lra.
  + move=> d; exact: measure_ge0.
  + exists (Nat.max (S D) DN) => d Hdd.
    case: d Hdd => [|n] Hdd; first lia.
    have HdnN : Nat.le D n by lia.
    have Hdn : (D <= n)%N by exact/ssrnat.leP.
    have [_ [HA _]] := Hpick n HdnN.
    rewrite /A Hdn.
    apply: le_trans HA _; rewrite lee_fin; apply/RleP.
    have HNd := HN (S n) ltac:(lia).
    have Hd : (0 < INR (S n))%Rcoq by apply lt_0_INR; lia.
    have Hpos := exp_pos (-sqrt(INR (S n))/2)%Rcoq.
    have Hpow := pow_le (INR (S n)) 4 ltac:(lra).
    have HM := Rmult_le_compat_r (2*(INR (S n))^4*exp(-sqrt(INR (S n))/2))%Rcoq
      _ _ ltac:(nra) HNd.
    change (2*INR (N (S n))*(INR (S n))^4*exp(-sqrt(INR (S n))/2) <=
      (2*C)*(INR (S n))^6*exp(-sqrt(INR (S n))/2))%Rcoq.
    nra.
- exists D => n Hn x Hx.
  have Hdn : (D <= n)%N by exact/ssrnat.leP.
  rewrite /A Hdn in Hx.
  exact: (proj2 (proj2 (Hpick n Hn)) x Hx).
Qed.
