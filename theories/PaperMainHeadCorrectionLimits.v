(* Public convergence consequences of the explicit dimension scale. *)
From Stdlib Require Import Reals Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 PaperMainDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainHeadCorrectionScale PaperMainResidualRates.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Lemma paper_main_head_scale_residual kappa d :
  1 <= d -> paper_main_residual_threshold kappa d =
    sqrt(4+4*kappa)/(paper_main_head_scale d)^8.
Proof.
move=> Hd; have [_ [HE _]] := paper_main_head_scale_powers d Hd.
by rewrite HE /paper_main_residual_threshold.
Qed.

Theorem paper_main_head_inverse_power_tends_to_zero C k :
  0 <= C -> (0 < k)%coq_nat ->
  paper_main_tends_to (fun d => ((C/(paper_main_head_scale (INR d))^k)%Rcoq)%:E) 0.
Proof.
move=> HC Hk eps Heps.
have HepsR : 0 < eps by exact/RltP.
have [D HD] := paper_main_head_inverse_power_small C k eps HC Hk HepsR.
exists D => d Hdd.
have HddN : Nat.le D d by exact: (elimT ssrnat.leP Hdd).
have [H0 Hlt] := HD d HddN.
have Hp : (0 <= ((C/(paper_main_head_scale (INR d))^k)%Rcoq)%:E)%E.
{ rewrite lee_fin; exact/RleP. }
rewrite sube0 (gee0_abs Hp) lte_fin; exact/RltP.
Qed.

Lemma paper_main_head_width_error_large E eps :
  0 <= E -> 0 < eps -> exists D : nat, forall d, (D <= d)%coq_nat ->
    0 < INR d /\
    2*(E/(paper_main_head_scale (INR d))^7)*INR d+1+1/(INR d)^2 <= eps*INR d.
Proof.
move=> HE Heps.
have [D1 HD1] := paper_main_head_inverse_power_small E 7 (eps/4) HE ltac:(lia) ltac:(lra).
have [D2 HD2] := INR_unbounded (4/eps).
exists (Nat.max 1 (Nat.max D1 D2)) => d Hdd.
have Hd1 : 1 <= INR d by change (INR 1 <= INR d); apply le_INR; lia.
have Hd : 0 < INR d by lra.
have [Heta0 Heta] := HD1 d ltac:(lia).
have Hlarge : 4/eps < INR d by have := le_INR D2 d ltac:(lia); lra.
have HM := Rmult_lt_compat_l eps _ _ Heps Hlarge.
replace (eps*(4/eps)) with 4 in HM by (field; lra).
have Hinv : 1/(INR d)^2 <= 1.
{ apply (Rmult_le_reg_r ((INR d)^2)); first nra.
  replace (1/(INR d)^2*(INR d)^2) with 1 by (field; lra); nra. }
split; first exact Hd.
nra.
Qed.
