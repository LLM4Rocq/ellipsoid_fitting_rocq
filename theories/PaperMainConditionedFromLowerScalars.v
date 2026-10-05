(* The scalars of the conditioned reduction. For kappa >= 1, the number
   lambda = (kappa+1/2)/(1-1/2) satisfies 1 <= lambda (pmcfls_lambda_ge1)
   and 0 < lambda^-1 <= lambda (pmcfls_bounds), in the MathComp order on
   R. The hypothesis Rle 1 kappa is the Stdlib form of kappa >= 1, as in
   paper_main_subcritical_raw_spectral_reduction, and lambda is written
   exactly as there (MathComp operations). PaperMainConditionedFromLower
   uses lm = lambda^-1 and lp = lambda as the constants of the
   well-conditioned fit event. *)
From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp reals Rstruct.
Import GRing.Theory Num.Theory Order.TTheory.

Lemma pmcfls_half : (1 - 1/2 = 1/2 :> R)%R.
Proof.
by rewrite {1}(splitr 1) addrK.
Qed.

Lemma pmcfls_lambda_ge1 (kappa : R) : Rle 1 kappa -> (1 <= (kappa+1/2)/(1-1/2))%R.
Proof.
move/RleP => Hk.
rewrite pmcfls_half ler_pdivlMr ?divr_gt0 ?ltr01 ?ltr0n // mul1r.
rewrite mul1r lerDr.
by apply: le_trans Hk; exact: ler01.
Qed.

Lemma pmcfls_bounds (kappa : R) : Rle 1 kappa ->
  (0 < ((kappa+1/2)/(1-1/2))^-1)%R /\
  (((kappa+1/2)/(1-1/2))^-1 <= (kappa+1/2)/(1-1/2))%R.
Proof.
move=> Hk; have H1 := pmcfls_lambda_ge1 kappa Hk.
set l := ((kappa + 1 / 2) / (1 - 1 / 2))%R in H1 *.
have Hl : (0 < l)%R by apply: lt_le_trans H1; exact: ltr01.
split; first by rewrite invr_gt0.
by apply: (le_trans _ H1); rewrite invf_le1.
Qed.
