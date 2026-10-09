(* Robustness of the optimal condition number at fourth moment three, at
   Stdlib's R: item R7 of phase 10. Required as
   From EllipsoidUniversality.Condition Require Import RobustCondition.

   Proved here, from condition_theorem (its countable parts (20) and (21))
   and the transfer of Countable/Robust.v, for a countable family (w, mu)
   of fourth moment 3 and laws P d of a point with d^2 tv(P d, nu_d) -> 0:
   - robust_condition_holds : robust_condition_statement. The fit event of
     condition number at most C is measurable (countable_condition_statement),
     so robust_tends carries its limits 1 below alpha_C and 0 above it from
     the samples of the family to those of P d.
   - robust_condition_number_holds : robust_condition_number_statement.
     For delta > 0, countable_condition_number_statement gives, for every
     large d, a measurable set E of samples of probability at most delta / 2
     under the family off which the optimal condition number is within eps
     of C_star(alpha). On E the probabilities under P d and under the family
     differ by at most n (tv(P d, nu_d) + 2 r_d) (robust_transfer), which
     is at most delta / 2 for every large d (robust_err_small); so E has
     probability at most delta under the samples of P d.
   - robust_condition_theorem_holds : robust_condition_theorem_statement. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import esum exp ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import ConditionStatement ConditionTheorem.
From EllipsoidUniversality Require Import RobustDefinitions.
From EllipsoidUniversality Require Import ConditionRobustStatement.
From EllipsoidUniversality.Countable Require Import Robust.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(* (20) for the samples of P d. *)
Theorem robust_condition_holds : robust_condition_statement.
Proof.
move=> K C alpha K0 C1 a0 w mu hfam h4 P hP n hn.
have [_ _ h20 _] := condition_theorem.
have [m hc] := h20 K C alpha K0 C1 a0.
have [p1 p2] := hc w mu hfam h4 n hn.
split => ha.
  exact: (robust_tends K w mu hfam P n alpha
    (fun d => universality_conditioned_fit_event (n d) d C) 1 a0 hn hP
    (fun d => m (n d) d) (p1 ha)).
exact: (robust_tends K w mu hfam P n alpha
  (fun d => universality_conditioned_fit_event (n d) d C) 0 a0 hn hP
  (fun d => m (n d) d) (p2 ha)).
Qed.

(* (21) for the samples of P d: the exceptional set of the family, whose
   probability changes by at most delta / 2 for large d. *)
Theorem robust_condition_number_holds : robust_condition_number_statement.
Proof.
move=> K alpha K0 a0 a4 w mu hfam h4 P hP n hn eps delta e0 dl0.
have [_ _ _ h21] := condition_theorem.
have d2 : 0 < delta / 2 by rewrite divr_gt0.
have [D1 h1] := h21 K alpha K0 a0 a4 w mu hfam h4 n hn eps _ e0 d2.
have [D2 h2] := robust_err_small K w mu hfam P n alpha a0 hn hP _ d2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[dd1 dd2].
have [E [mE PE hE]] := h1 d dd1.
exists E; split => //.
have hc := robust_transfer K w mu hfam (n d) d (P d) E mE.
have hr := h2 d dd2.
have fZ := cmp_fin K w mu hfam (n d) d E mE.
have fX : robust_sample_law (n d) d (P d) E \is a fin_num.
  have mB := measurable_robust_image (n d) d E mE.
  by rewrite /robust_sample_law; exact: fin_num_measure.
move: hc PE hr fX fZ.
set X := robust_sample_law _ _ _ E.
set Z := countable_mixture_probability _ _ _ _ E.
set e := (n d)%:R * _ => hc PE hr fX fZ.
move: hc PE; rewrite -(fineK fX) -(fineK fZ) /= !lee_fin.
rewrite ler_norml => /andP[_ h] PE.
by move: hr; clearbody X Z e; lra.
Qed.

Theorem robust_condition_theorem_holds : robust_condition_theorem_statement.
Proof.
by split; [exact: robust_condition_holds | exact: robust_condition_number_holds].
Qed.
