(* Bounds on the sample count n(d) = floor(alpha d^2) of
   paper_main_fixed_count for 0 < alpha < 1/4: the count and density
   hypotheses of the lower spectral bound
   paper_main_squarefree_lower_probability.
   paper_main_fixed_subcritical_counts: for some c1 and every large d,
   0 < n(d), 4 n(d) <= d^2 and d^2 <= c1 n(d).
   paper_main_fixed_subcritical_density: n(d) / d^2 >= alpha / 2 for every
   large d. Deterministic. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import GaussianProbabilityProductContinuity PaperMainDefinitions
 PaperMainFixedDensity PaperMainFixedCountBounds.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Theorem paper_main_fixed_subcritical_counts alpha :
  (0 < alpha)%Rcoq -> (alpha < 1/4)%Rcoq ->
  exists c1 : nat, exists D : nat, forall d, (D <= d)%N ->
    (0 < paper_main_fixed_count alpha d)%N /\
    (4 * paper_main_fixed_count alpha d <= d^2)%N /\
    (d^2 <= c1 * paper_main_fixed_count alpha d)%N.
Proof.
move=>Ha Haq.
have Ha1 : (alpha <= 1)%Rcoq by Stdlib.micromega.Lra.lra.
have [D HD] := paper_main_fixed_count_density_bounds alpha Ha Ha1.
have [c1 Hc1] := INR_unbounded (2/alpha)%Rcoq.
have Ha0 : (0 <= alpha)%Rcoq by Stdlib.micromega.Lra.lra.
have Hrec : (alpha * (2/alpha) = 2)%Rcoq by field; Stdlib.micromega.Lra.lra.
have Hc : (2 <= alpha * INR c1)%Rcoq.
{ have := Rmult_lt_compat_l alpha _ _ Ha Hc1; Stdlib.micromega.Lra.lra. }
have Hc0 : (0 <= INR c1)%Rcoq := pos_INR c1.
exists c1,D => d Hd.
have [Hd0 [HN [Hup Hlow]]] := HD d (elimT ssrnat.leP Hd).
have [_ Hfloor] := paper_main_fixed_count_error alpha d Ha0.
have Hsq : (0 <= (INR d)^2)%Rcoq := pow2_ge_0 (INR d).
split=> //; split.
- rewrite -(@ler_nat R) natrM natrX -!INRE -RmultE -RpowE.
  apply/RleP.
  have E4 : INR 4 = 4%Rcoq by simpl; ring.
  rewrite E4.
  Stdlib.micromega.Lra.nra.
- rewrite -(@ler_nat R) natrM natrX -!INRE -RmultE -RpowE.
  apply/RleP.
  have HM := Rmult_le_compat_l (INR c1) _ _ Hc0 Hlow.
  have HC := Rmult_le_compat_r ((INR d)^2) _ _ Hsq Hc.
  Stdlib.micromega.Lra.nra.
Qed.

Corollary paper_main_fixed_subcritical_density alpha :
  (0 < alpha)%Rcoq -> (alpha < 1/4)%Rcoq ->
  paper_main_eventually_ge (paper_main_density (paper_main_fixed_count alpha)) (alpha/2)%Rcoq.
Proof.
move=>Ha Haq; apply: paper_main_fixed_count_eventually_lower => //.
Stdlib.micromega.Lra.lra.
Qed.
