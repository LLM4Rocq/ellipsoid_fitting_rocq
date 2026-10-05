(* Port of theories/GaussianJensen.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem of the original keeps its name and its arguments,
   in the same order, and no statement gains or loses a hypothesis. The
   iterated operators come from the ported GaussianProductDefinitions, where
   gaussian_iterated_integrable asks at each level for the Lebesgue
   integrability over the line of the outer function times the kernel
   (difference 4 of analysis/README.md). The proofs use only
   gaussian_iterated_constant, gaussian_iterated_add,
   gaussian_iterated_scale and gaussian_iterated_monotone of the ported
   GaussianProduct, whose statements keep the text of the originals.

   One change of text, and none of meaning. The module loads MathComp's exp,
   under which an unqualified ln is exp.ln. The two statements about the
   logarithm, gaussian_iterated_log_exp_bound and
   gaussian_iterated_log_majorant_bound, therefore write Rpower.ln, which is
   Stdlib's logarithm, the ln of the original. The arithmetic, exp and
   length in every statement are Stdlib's, as in the original. An importer
   that loads MathComp's exp must also write Rpower.ln to use them.

   Assumptions. Stdlib's exp_ineq1_le, which the original proof of
   exponential_tangent_lower_bound used, rests on Classical_Prop.classic.
   The port proves the inequality 1 + y <= exp y with MathComp's expR_ge1Dx
   and RexpE instead, so exponential_tangent_lower_bound,
   gaussian_iterated_exp_jensen and gaussian_iterated_exp_dominated_jensen
   rest on the seven axioms of analysis/README.md only. The two statements
   about Rpower.ln also carry classic, the eighth axiom of the README,
   because Stdlib defines Rpower.ln through ln_exists, whose proof uses it.

   The Coquelicot import is dropped; the original used nothing from it. *)

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
