(* Jensen's inequality for the exponential under the iterated Gaussian
   expectation E = gaussian_iterated_expectation d of
   GaussianProductDefinitions. If F and G are integrable
   (gaussian_iterated_integrable) and exp (F xs) <= G xs, then
   exp (E F) <= E G (gaussian_iterated_exp_dominated_jensen). Hence, for
   t > 0 and exp (t * F xs) <= G xs, E F <= ln (E G) / t
   (gaussian_iterated_log_majorant_bound). The proof integrates the tangent
   bound exp a * (1 + x - a) <= exp x (exponential_tangent_lower_bound) at
   a = E F.

   The module loads MathComp's exp, under which an unqualified ln is
   exp.ln, so the statements write Rpower.ln for Stdlib's logarithm; an
   importer that loads MathComp's exp must do the same. The arithmetic, exp
   and length in every statement are Stdlib's. *)

From Stdlib Require Import Reals List Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive realfun exp.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import GaussianDefinitions GaussianProductDefinitions GaussianProduct.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

Lemma exponential_tangent_lower_bound a x :
  exp a * (1 + x - a) <= exp x.
Proof.
  assert (H : 1 + (x-a) <= exp (x-a)).
  { rewrite RexpE RplusE; apply/RleP; exact: expR_ge1Dx. }
  pose proof (exp_pos a) as Ha.
  assert (HM := Rmult_le_compat_l (exp a) _ _ ltac:(lra) H).
  rewrite -exp_plus in HM.
  replace (a+(x-a)) with x in HM by ring.
  nra.
Qed.

Theorem gaussian_iterated_exp_dominated_jensen d F G :
  gaussian_iterated_integrable d F ->
  gaussian_iterated_integrable d G ->
  (forall xs, length xs=d -> exp (F xs) <= G xs) ->
  exp (gaussian_iterated_expectation d F) <= gaussian_iterated_expectation d G.
Proof.
  intros HF HG Hb.
  set (m := gaussian_iterated_expectation d F).
  destruct (gaussian_iterated_constant d (1-m)) as [HC HCE].
  destruct (gaussian_iterated_add d (fun _ => 1-m) F HC HF) as [HI HIE].
  destruct (gaussian_iterated_scale d (fun xs => (1-m)+F xs) (exp m) HI) as [HS HSE].
  assert (HL : forall xs, length xs=d -> exp m*((1-m)+F xs) <= G xs).
  { intros xs Hxs. eapply Rle_trans; [|apply Hb; exact Hxs].
    replace ((1-m)+F xs) with (1+F xs-m) by ring.
    apply exponential_tangent_lower_bound. }
  pose proof (gaussian_iterated_monotone d (fun xs => exp m*((1-m)+F xs)) G HS HG HL) as HM.
  rewrite HSE HIE HCE in HM; fold m in HM.
  replace (exp m * (1-m+m)) with (exp m) in HM by ring.
  exact HM.
Qed.

Theorem gaussian_iterated_log_majorant_bound d F G t :
  0 < t ->
  gaussian_iterated_integrable d F ->
  gaussian_iterated_integrable d G ->
  (forall xs, length xs=d -> exp (t*F xs) <= G xs) ->
  gaussian_iterated_expectation d F <= Rpower.ln (gaussian_iterated_expectation d G) / t.
Proof.
  intros Ht HF HG Hb.
  destruct (gaussian_iterated_scale d F t HF) as [HI HE].
  pose proof (gaussian_iterated_exp_dominated_jensen d (fun xs => t*F xs) G HI HG Hb) as H.
  rewrite HE in H.
  assert (HL : t*gaussian_iterated_expectation d F <=
    Rpower.ln (gaussian_iterated_expectation d G)).
  { destruct (Req_EM_T (exp (t*gaussian_iterated_expectation d F))
      (gaussian_iterated_expectation d G)) as [Heq|Hneq].
    - rewrite -Heq ln_exp; lra.
    - pose proof (ln_increasing (exp (t*gaussian_iterated_expectation d F))
        (gaussian_iterated_expectation d G) (exp_pos _) ltac:(lra)) as HH.
      rewrite ln_exp in HH; lra. }
  apply (Rmult_le_reg_r t); [exact Ht|].
  replace (Rpower.ln (gaussian_iterated_expectation d G)/t*t) with
    (Rpower.ln (gaussian_iterated_expectation d G)) by (field; lra).
  nra.
Qed.
