(* Quantitative floor-count bounds for the fixed-density phase reductions. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum archimedean matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainFixedDensity.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_fixed_count_error alpha d : (0<=alpha)%Rcoq ->
  (alpha*(INR d)^2-1<INR(paper_main_fixed_count alpha d)<=alpha*(INR d)^2)%Rcoq.
Proof.
move=> Ha.
have Ha' : 0<=alpha by exact/RleP.
have Hpos : 0<=alpha*d%:R^+2 by apply mulr_ge0; [exact Ha'|exact: sqr_ge0].
have /andP[HL HU] := truncn_itv Hpos.
rewrite -/(paper_main_fixed_count alpha d) in HL HU.
move/RleP: HL => HL; move/RltP: HU => HU.
rewrite -!INRE -RpowE -RmultE in HL.
rewrite -!INRE -RpowE -RmultE S_INR in HU.
Stdlib.micromega.Lra.lra.
Qed.

Theorem paper_main_fixed_count_near alpha kappa : (0<=alpha)%Rcoq -> (0<kappa)%Rcoq ->
  exists D, forall d, Nat.le D d -> (0<d)%coq_nat /\
    (Rabs(INR(paper_main_fixed_count alpha d)-alpha*(INR d)^2)<=kappa*(INR d)^2)%Rcoq.
Proof.
move=> Ha Hk; have [K HK] := INR_unbounded (1/kappa)%Rcoq.
exists (S K) => d Hd.
have Hd0 : (0<d)%coq_nat by lia.
have Hd1 : (1<=INR d)%Rcoq by apply (le_INR 1); lia.
have Hlarge : (1/kappa<INR d)%Rcoq by have := le_INR K d ltac:(lia); Stdlib.micromega.Lra.lra.
have HH := Rmult_lt_compat_l kappa _ _ Hk Hlarge.
replace (kappa*(1/kappa))%Rcoq with 1%Rcoq in HH by (field; Stdlib.micromega.Lra.lra).
have Hd2 : (INR d<=(INR d)^2)%Rcoq by Stdlib.micromega.Lra.nra.
have HM := Rmult_le_compat_l kappa _ _ (Rlt_le _ _ Hk) Hd2.
have [HL HU] := paper_main_fixed_count_error alpha d Ha.
split=> //; apply Rabs_le; Stdlib.micromega.Lra.lra.
Qed.

Theorem paper_main_fixed_count_density_bounds alpha : (0<alpha)%Rcoq -> (alpha<=1)%Rcoq ->
  exists D, forall d, Nat.le D d ->
    (0<d)%N /\ (0<paper_main_fixed_count alpha d)%N /\
    (paper_main_fixed_count alpha d<=d^2)%N /\
    (alpha/2*(INR d)^2<=INR(paper_main_fixed_count alpha d))%Rcoq.
Proof.
move=> Ha Ha1.
have [D HD] := paper_main_fixed_count_near alpha (alpha/2)%Rcoq ltac:(Stdlib.micromega.Lra.lra) ltac:(Stdlib.micromega.Lra.lra).
exists D => d Hd.
have [Hd0 Hnear] := HD d Hd.
have Hd1 : (1<=INR d)%Rcoq by apply (le_INR 1); lia.
have Habs := Rle_abs (-(INR(paper_main_fixed_count alpha d)-alpha*(INR d)^2))%Rcoq.
rewrite Rabs_Ropp in Habs.
have Hlower : (alpha/2*(INR d)^2<=INR(paper_main_fixed_count alpha d))%Rcoq by Stdlib.micromega.Lra.lra.
have Hpos : (0<INR(paper_main_fixed_count alpha d))%Rcoq.
{ have Hp : (0<alpha/2*(INR d)^2)%Rcoq.
  { apply Rmult_lt_0_compat; [Stdlib.micromega.Lra.lra|apply pow_lt; Stdlib.micromega.Lra.lra]. }
  Stdlib.micromega.Lra.lra. }
have HNpos : (0<paper_main_fixed_count alpha d)%N.
{ apply/ssrnat.ltP; apply INR_lt; exact Hpos. }
have [_ Hupper] := paper_main_fixed_count_error alpha d ltac:(Stdlib.micromega.Lra.lra).
have HM := Rmult_le_compat_r ((INR d)^2)%Rcoq _ _ (pow2_ge_0 _) Ha1.
have Hupper2 : (INR(paper_main_fixed_count alpha d)<=(INR d)^2)%Rcoq by Stdlib.micromega.Lra.lra.
have HupperMC : (paper_main_fixed_count alpha d)%:R<=d%:R^+2 :> R.
{ rewrite -!INRE -RpowE; exact/RleP. }
have HNupper : (paper_main_fixed_count alpha d<=d^2)%N by move: HupperMC; rewrite -natrX ler_nat.
split; first exact/ssrnat.ltP.
by split=> //; split.
Qed.

Corollary paper_main_fixed_count_eventually_lower alpha : (0<alpha)%Rcoq -> (alpha<=1)%Rcoq ->
  paper_main_eventually_ge (paper_main_density (paper_main_fixed_count alpha)) (alpha/2)%Rcoq.
Proof.
move=> Ha Ha1; have [D HD] := paper_main_fixed_count_density_bounds alpha Ha Ha1.
exists D => d Hd.
have HdN : Nat.le D d by exact/ssrnat.leP.
have [Hd0 [_ [_ Hlow]]] := HD d HdN.
have HdR : (0:R)<d%:R by rewrite ltr0n.
have Hsq : (0:R)<d%:R^+2 by exact: exprn_gt0.
rewrite /paper_main_density ler_pdivlMr //.
apply/RleP; rewrite -RmultE -RpowE -!INRE; exact Hlow.
Qed.
