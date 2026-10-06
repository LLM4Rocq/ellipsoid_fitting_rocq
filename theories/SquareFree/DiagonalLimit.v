(* The diagonal of the square-free feature Gram matrix concentrates
   (eq:diag-limit of the paper): paper_main_squarefree_diag_tends_to_zero.
   For fixed eps > 0 and N(d) <= C d^2 eventually, the probability of
   paper_main_squarefree_diag_event, that some row has
   |(V V^T)_ii / d^2 - 1| > eps, tends to 0.
   The clipping level is U = d^(1/4), so U^2 = sqrt d, and
   eta = min(1, eps / 6) (pmsdl_eta). Then eventually
   eta (2 + eta) + U^2 (1 + eta) / d <= eps. In the bound
   paper_main_squarefree_diag_bound of SquareFree.Diagonal, the
   row tail term is then at most 2 C d^2 exp (- sqrt d / 2)
   (pmsdl_exp_compare), and the coordinate term is
   2 N d exp (- sqrt d / 2) <= 2 C d^3 exp (- sqrt d / 2).
   paper_main_sqrt_polynomial_tends_to_zero finishes. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Soft.Extrema PaperMainDefinitions GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Data.SampleTail Clipping.Rates
  Clipping.Limits SquareFree.Diagonal.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

(* 1. The choice of eta. *)
Lemma pmsdl_eta eps :
  0 < eps -> 0 < Rmin 1 (eps / 6) /\ Rmin 1 (eps / 6) <= 1 /\
  Rmin 1 (eps / 6) * (2 + Rmin 1 (eps / 6)) <= eps / 2.
Proof.
move=> Heps.
have H1 := Rmin_l 1 (eps / 6); have H2 := Rmin_r 1 (eps / 6).
have H0 : 0 < Rmin 1 (eps / 6) by apply: Rmin_glb_lt; lra.
split => //; split => //; nra.
Qed.

(* 2. A linear exponent beats the square-root exponent eventually. *)
Lemma pmsdl_exp_compare c D :
  0 < c -> 0 < D -> 1 / (4 * c ^ 2) <= D -> exp (- (c * D)) <= exp (- sqrt D / 2).
Proof.
move=> Hc HD HcD.
have Hs := sqrt_lt_R0 _ HD.
have Hsq := pow2_sqrt D (Rlt_le _ _ HD).
have Hcs : 1 / 2 <= c * sqrt D.
  have H4 : 0 < 4 * c ^ 2 by nra.
  have H1 : 4 * c ^ 2 * (1 / (4 * c ^ 2)) <= 4 * c ^ 2 * D.
    by apply: Rmult_le_compat_l => //; lra.
  have E : 4 * c ^ 2 * (1 / (4 * c ^ 2)) = 1 by field; lra.
  rewrite E in H1.
  have Hx0 : 0 < c * sqrt D by apply: Rmult_lt_0_compat.
  have Hx2 : (c * sqrt D) ^ 2 = c ^ 2 * D by rewrite Rpow_mult_distr Hsq.
  nra.
apply: exp_monotone; nra.
Qed.

(* 3. The limit. *)
Theorem paper_main_squarefree_diag_tends_to_zero (N : nat -> nat) (C eps : R) :
  0 <= C -> 0 < eps ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C * INR d ^ 2) ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d (paper_main_squarefree_diag_event (N d) d eps)) 0.
Proof.
move=> HC Heps [D HD].
have [Heta [Heta1 Heta2]] := pmsdl_eta eps Heps.
set eta := Rmin 1 (eps / 6) in Heta Heta1 Heta2 *.
set c := eta ^ 2 / (4 * (1 + eta)).
have Hc : 0 < c by apply: Rdiv_lt_0_compat; nra.
have [K1 HK1] := INR_unbounded (16 / eps ^ 2).
have [K2 HK2] := INR_unbounded (1 / (4 * c ^ 2)).
apply: (paper_main_sqrt_polynomial_tends_to_zero _ (4 * C) 3); first by lra.
  by move=> d; exact: measure_ge0.
exists (Nat.max D (Nat.max K1 (Nat.max K2 1))) => d Hd.
(* The thresholds at d. *)
have HdD : Nat.le D d by lia.
have HdK1 : Nat.le K1 d by lia.
have HdK2 : Nat.le K2 d by lia.
have Hd1 : Nat.le 1 d by lia.
have HdR1 : 1 <= INR d by have := le_INR _ _ Hd1; rewrite /=; lra.
have Hd0 : 0 < INR d by lra.
have HdK1R : 16 / eps ^ 2 < INR d by have := le_INR _ _ HdK1; lra.
have HdK2R : 1 / (4 * c ^ 2) <= INR d by have := le_INR _ _ HdK2; lra.
(* U = d^(1/4). *)
have [HU2 HU] := paper_main_coordinate_clipping_scale (INR d) Hd0.
set U := sqrt (sqrt (INR d)) in HU2 HU.
have Hs := sqrt_lt_R0 _ Hd0.
have Hsq := pow2_sqrt (INR d) (Rlt_le _ _ Hd0).
have Hs4 : 4 / eps <= sqrt (INR d).
  have He4 : 0 < 4 / eps by apply: Rdiv_lt_0_compat; lra.
  have E : 16 / eps ^ 2 = (4 / eps) ^ 2 by field; lra.
  rewrite E in HdK1R; nra.
(* The condition of the finite bound. *)
have Hcond : eta * (2 + eta) + U ^ 2 * (1 + eta) / INR d <= eps.
  rewrite HU2.
  have H2 : (1 + eta) * sqrt (INR d) <= eps / 2 * INR d.
    have He : 2 <= eps / 2 * sqrt (INR d).
      have := Rmult_le_compat_l (eps / 2) _ _ (ltac:(lra) : 0 <= eps / 2) Hs4.
      have -> : eps / 2 * (4 / eps) = 2 by field; lra.
      by [].
    have Hm := Rmult_le_compat_l (sqrt (INR d)) _ _ (Rlt_le _ _ Hs) He.
    nra.
  have H3 : sqrt (INR d) * (1 + eta) / INR d <= eps / 2.
    apply: (Rmult_le_reg_r (INR d)) => //.
    have -> : sqrt (INR d) * (1 + eta) / INR d * INR d = sqrt (INR d) * (1 + eta).
      by field; lra.
    lra.
  lra.
(* The finite bound and the comparison with 4 C d^3 exp (- sqrt d / 2). *)
have Hd0N : (0 < d)%N by apply/ssrnat.ltP; lia.
have [_ Hb] := paper_main_squarefree_diag_bound (N d) d eps eta U Hd0N Heta HU Hcond.
apply: (le_trans Hb); rewrite lee_fin; apply/RleP.
rewrite -!RmultE -!RplusE HU2.
have E2 : (2%R : R) = 2 by [].
rewrite E2.
have Eexp : - (eta * INR d) ^ 2 / (4 * INR d + 4 * (eta * INR d)) = - (c * INR d).
  rewrite /c; field.
  split; [lra | nra].
rewrite Eexp.
have HF := pmsdl_exp_compare c (INR d) Hc Hd0 HdK2R.
set E := exp (- sqrt (INR d) / 2) in HF *.
set F := exp (- (c * INR d)) in HF *.
have HE0 : 0 < E by exact: exp_pos.
have HF0 : 0 < F by exact: exp_pos.
have HN := HD d HdD.
have HN0 := pos_INR (N d).
have Hd23 : INR d ^ 2 <= INR d ^ 3 by rewrite /=; nra.
have H1 : INR (N d) * (2 * F) <= C * INR d ^ 2 * (2 * E).
  by apply: Rmult_le_compat => //; lra.
have H2 : 2 * INR (N d) * INR d * E <= 2 * (C * INR d ^ 2) * INR d * E.
  apply: Rmult_le_compat_r; first lra.
  apply: Rmult_le_compat_r; first lra.
  lra.
have HCE : 0 <= 2 * C * E by nra.
have H3 : C * INR d ^ 2 * (2 * E) <= 2 * C * INR d ^ 3 * E.
  have := Rmult_le_compat_l (2 * C * E) _ _ HCE Hd23; nra.
have H4 : 2 * (C * INR d ^ 2) * INR d * E = 2 * C * INR d ^ 3 * E by rewrite /=; ring.
lra.
Qed.
