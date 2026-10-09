(* The condition-number statements for countable mixtures, from the finite
   ones, at Stdlib's R: step D4 of the route of
   notes/three-extensions-plan.md (section 2), the countable part of item
   Q9 of phase 8.

   Proved here, as implications, so that they do not wait for the proofs
   of the finite statements.
   - countable_condition_holds : condition_statement ->
     countable_condition_statement, (20) for countable mixtures. The
     measurability of universality_conditioned_fit_event is that of the
     finite statement. At each dimension d the countable family is
     replaced by its truncation of Countable/Truncation (trunc_N, trunc_w,
     trunc_mu), a finite family with the same K and the fourth moment 3
     (trunc_family, trunc_fourth), to which the finite statement applies;
     countable_transfer of Countable/Theorem carries each of the two
     limits (1 below alpha_C, 0 above it) to the countable family.
   - countable_condition_number_holds : condition_number_statement ->
     countable_condition_number_statement, (21) for countable mixtures.
     The finite statement for the truncated family, with delta / 2 in place
     of delta, gives the exceptional set E. Its countable probability is
     at most delta / 2 + n_d r_d (trunc_coupling), and n_d r_d <= delta / 2
     for every large d (trunc_nr_small), as in
     countable_interpolation_holds. The bound on the optimal condition
     number outside E does not involve the law of the sample. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype sequences esum.
From mathcomp Require Import ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import mixture countable_mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionStatement.
From EllipsoidUniversality.Countable Require Import Truncation.
Require Import EllipsoidUniversality.Countable.Theorem.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* (20) for countable mixtures, from (20) for finite mixtures. *)
Theorem countable_condition_holds :
  condition_statement -> countable_condition_statement.
Proof.
move=> hC K C alpha K0 C1 a0.
have [hm hc] := hC K C alpha K0 C1 a0.
split => // w mu hfam h4 n hn.
have [p1 p2] := hc _ _ _ (trunc_family K w mu hfam)
  (trunc_fourth K w mu hfam _ h4) n hn.
split => ha.
  apply: (countable_transfer K w mu hfam n alpha a0 hn) (p1 ha).
  by move=> d; exact: hm.
apply: (countable_transfer K w mu hfam n alpha a0 hn) (p2 ha).
by move=> d; exact: hm.
Qed.

(* (21) for countable mixtures, from (21) for finite mixtures. *)
Theorem countable_condition_number_holds :
  condition_number_statement -> countable_condition_number_statement.
Proof.
move=> hC K alpha K0 a0 ah w mu hfam h4 n hn eps delta e0 d0.
have d2 : 0 < delta / 2 by rewrite divr_gt0.
have [D1 h1] := hC K alpha K0 a0 ah _ _ _ (trunc_family K w mu hfam)
  (trunc_fourth K w mu hfam _ h4) n hn eps (delta / 2) e0 d2.
have [D2 h2] := trunc_nr_small K w mu hfam n alpha a0 hn (delta / 2) d2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[dD1 dD2].
have [E [mE PE hE]] := h1 d dD1.
exists E; split => //.
(* the countable probability of E is at most delta / 2 + n r_d *)
have hc := trunc_coupling K w mu hfam (n d) d E mE.
have ff := trunc_probability_fin K w mu hfam n d E mE.
have hr : (n d)%:R * trunc_r K w mu hfam d <= delta / 2 := h2 d dD2.
move: hc PE ff.
set X := countable_mixture_probability _ _ _ _ E.
set Y := mixture_probability _ _ _ _ _ E => hc PE ff.
have xf : X \is a fin_num.
  clearbody X Y.
  by move: hc PE ff; case: X => [x||]; case: Y => [y||] //=.
move: hc PE; rewrite -(fineK xf) -(fineK ff) /= !lee_fin.
rewrite ler_norml => /andP[_ h] PE.
lra.
Qed.
