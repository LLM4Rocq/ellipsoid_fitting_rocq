(* Robustness of the condition-number theorem at fourth moment kappa, at
   Stdlib's R: item A3 of phase 11 (notes/phase11-plan.md, sections 3.4
   and 5; lane B). The model is Condition/RobustCondition.v, which treats
   kappa = 3 through robust_transfer and its truncation term; here the
   transfer is robust_transfer_tv of Countable/Robust.v, with its exact
   bound n tv(P d, nu_d).

   Proved here, as implications from the countable statements of
   ConditionKappaStatement, for laws P d of a point with
   d^2 tv(P d, nu_d) -> 0.
   - robust_tv_small, robust_tends_tv: for a countable family (w, mu) and
     n d / d^2 -> alpha > 0, n d tv(P d, nu_d) -> 0, so the limits of the
     probabilities of measurable sets of samples carry over from the
     samples of the family to those of n d i.i.d. points of law P d.
   - robust_condition_kappa_holds : countable_condition_kappa_statement ->
     robust_condition_kappa_statement. The fit event of condition number
     at most C is measurable (the countable statement), so robust_tends_tv
     carries its limits, 1 below alpha(C, kappa) and 0 above it.
   - robust_condition_kappa_number_holds :
     countable_condition_kappa_number_statement ->
     robust_condition_kappa_number_statement. For delta > 0 the countable
     statement gives, for every large d, a measurable set E of samples of
     probability at most delta / 2 under the family, off which the optimal
     condition number is within eps of C_star(alpha, kappa); on E the two
     laws of samples differ by at most n d tv(P d, nu_d) <= delta / 2
     (robust_transfer_tv, robust_tv_small).
   - finite_point_lawE, finite_robust_close: a finite family (N, w, mu)
     lifts to the admissible countable family (fin_cw N w, fin_cmu N mu) of
     Countable/Theorem, as countable_of_finite does. The weights are
     extended by zero (fin_cw), and the inactive component laws, s >= N d,
     are filled with the admissible laws mu d 0 j (fin_cmu), so that the
     lift is admissible (fin_cfamily); zero weights alone would keep the
     point law but not make the family admissible. The point law of the
     lift is robust_point_law (finite_weights (N d) (w d)) (mu d) d, the
     reference law of the finite statements, so the closeness of P to the
     finite family is that to the lift.
   - finite_robust_condition_kappa_holds : robust_condition_kappa_statement
     -> finite_robust_condition_kappa_statement and
     finite_robust_condition_kappa_number_holds :
     robust_condition_kappa_number_statement ->
     finite_robust_condition_kappa_number_statement, through fin_cfamily
     and fin_cfourth.
   - condition_kappa_robust_holds : condition_kappa_theorem_statement ->
     condition_kappa_robust_theorem_statement. *)

From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import esum exp ereal measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis Require Import lindeberg.
From GaussianAnalysis.probability Require Import mixture countable_mixture.
From GaussianAnalysis.probability Require Import total_variation.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality Require Import ConditionDefinitions.
From EllipsoidUniversality Require Import RobustDefinitions.
From EllipsoidUniversality Require Import ConditionKappaDefinitions.
From EllipsoidUniversality Require Import ConditionKappaStatement.
From EllipsoidUniversality Require Import ConditionKappaRobustStatement.
From EllipsoidUniversality.Sat Require Import ApproximateFit.
From EllipsoidUniversality.Countable Require Import Robust.
Require Import EllipsoidUniversality.Countable.Theorem.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).
Local Notation pt d := (d.-tuple (measurableTypeR R)).

(* 1. The transfer with the exact bound n tv(P d, nu_d). *)

Section tv_transfer.
Variables (K : R) (w : nat -> nat -> R).
Variable (mu : nat -> nat -> nat -> probability (measurableTypeR R) R).
Hypothesis hfam : countable_mixture_family K w mu.

(* n d tv(P d, nu_d) -> 0 when n d / d^2 -> alpha and
   d^2 tv(P d, nu_d) -> 0. *)
Lemma robust_tv_small (P : forall d, probability (pt d) RR)
    (n : nat -> nat) (alpha : R) :
  0 < alpha -> universality_density_tends_to n alpha -> robust_close w mu P ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
    (n d)%:R * tv_dist (P d) (rob_nu K w mu hfam d) <= eps.
Proof.
move=> a0 hn hP eps e0.
have ea : 0 < eps / (2 * alpha) by rewrite divr_gt0 // mulr_gt0.
have [D1 h1] := af_ev_density n alpha a0 hn.
have [D2 h2] := hP (eps / (2 * alpha)) ea.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [d0 [nlo nhi]] := h1 d d1.
have tv0 := tv_dist_ge0 (P d) (rob_nu K w mu hfam d).
have htv : d%:R ^+ 2 * tv_dist (P d) (rob_nu K w mu hfam d) <
    eps / (2 * alpha).
  have := h2 d d2; rewrite (rob_tvE K w mu hfam) -EFinM -EFinB abse_EFin.
  by rewrite lte_fin subr0 ger0_norm // mulr_ge0 // exprn_ge0.
apply: le_trans (_ : 2 * alpha *
    (d%:R ^+ 2 * tv_dist (P d) (rob_nu K w mu hfam d)) <= _).
  by rewrite mulrA; apply: ler_wpM2r.
apply: le_trans (_ : 2 * alpha * (eps / (2 * alpha)) <= _).
  by apply: ler_wpM2l; [rewrite mulr_ge0 // ltW | exact: ltW].
have an : alpha != 0 by rewrite gt_eqF.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

(* The limits carry over from the countable family to the samples of P,
   through robust_transfer_tv. *)
Lemma robust_tends_tv (P : forall d, probability (pt d) RR)
    (n : nat -> nat) (alpha : R)
    (E : forall d, set (paper_main_sample (n d) d)) (l : R) :
  0 < alpha -> universality_density_tends_to n alpha -> robust_close w mu P ->
  (forall d, measurable (E d)) ->
  paper_main_tends_to
    (fun d => countable_mixture_probability (w d) (mu d) (n d) d (E d)) l ->
  paper_main_tends_to (fun d => robust_sample_law (n d) d (P d) (E d)) l.
Proof.
move=> a0 hn hP mE h.
apply: (tends_to_transfer _ _
  (fun d => (n d)%:R * tv_dist (P d) (rob_nu K w mu hfam d)) l _ _ _ h).
- by move=> d; exact: (robust_transfer_tv K w mu hfam (n d) d (P d) (E d)
    (mE d)).
- by move=> d; exact: (cmp_fin K w mu hfam (n d) d (E d) (mE d)).
- exact: (robust_tv_small P n alpha a0 hn hP).
Qed.

End tv_transfer.

(* 2. The countable reference families. *)

(* (20) at fourth moment kappa for the samples of P d. *)
Theorem robust_condition_kappa_holds :
  countable_condition_kappa_statement -> robust_condition_kappa_statement.
Proof.
move=> h20 kappa K C alpha k1 K0 C1 a0 w mu hfam h4 P hP n hn.
have [m hc] := h20 kappa K C alpha k1 K0 C1 a0.
have [p1 p2] := hc w mu hfam h4 n hn.
split => ha.
  exact: (robust_tends_tv K w mu hfam P n alpha
    (fun d => universality_conditioned_fit_event (n d) d C) 1 a0 hn hP
    (fun d => m (n d) d) (p1 ha)).
exact: (robust_tends_tv K w mu hfam P n alpha
  (fun d => universality_conditioned_fit_event (n d) d C) 0 a0 hn hP
  (fun d => m (n d) d) (p2 ha)).
Qed.

Lemma robust_number_arith (x z e delta : RR) : x - z <= e -> z <= delta / 2 ->
  e <= delta / 2 -> x <= delta.
Proof. by move=> h1 h2 h3; lra. Qed.

(* (21) at fourth moment kappa for the samples of P d: the exceptional set
   of the family, whose probability changes by at most delta / 2 for large
   d. *)
Theorem robust_condition_kappa_number_holds :
  countable_condition_kappa_number_statement ->
  robust_condition_kappa_number_statement.
Proof.
move=> h21 kappa K alpha k1 K0 a0 a4 w mu hfam h4 P hP n hn eps delta e0 dl0.
have d2 : 0 < delta / 2 by rewrite divr_gt0.
have [D1 h1] := h21 kappa K alpha k1 K0 a0 a4 w mu hfam h4 n hn eps _ e0 d2.
have [D2 h2] := robust_tv_small K w mu hfam P n alpha a0 hn hP _ d2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[dd1 dd2].
have [E [mE PE hE]] := h1 d dd1.
exists E; split => //.
have hc := robust_transfer_tv K w mu hfam (n d) d (P d) E mE.
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
exact: (robust_number_arith _ _ _ _ h PE hr).
Qed.

(* 3. The finite reference families, lifted to admissible countable
   families. *)

Lemma finite_point_lawE (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) d
    (A : set (pt d)) :
  robust_point_law (fin_cw N w d) (fin_cmu N mu d) d A =
  robust_point_law (finite_weights (N d) (w d)) (mu d) d A.
Proof.
rewrite /robust_point_law; apply: eq_esum => s _.
rewrite /fin_cw /finite_weights; case: ifP => sN; last by rewrite !mul0e.
congr (_ * _)%E; congr (tuple_prod _ d A); apply/funext => j.
by rewrite /fin_cmu sN.
Qed.

Lemma finite_robust_close (N : nat -> nat) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R)
    (P : forall d, probability (pt d) RR) :
  robust_close (fun d => finite_weights (N d) (w d)) mu P ->
  robust_close (fin_cw N w) (fin_cmu N mu) P.
Proof.
move=> hP eps e0; have [D hD] := hP eps e0.
exists D => d dD; have := hD d dD.
have -> : robust_point_law (fin_cw N w d) (fin_cmu N mu d) d =
    robust_point_law (finite_weights (N d) (w d)) (mu d) d.
  by apply/funext => A; exact: finite_point_lawE.
by [].
Qed.

(* (20) at fourth moment kappa around a finite family. *)
Theorem finite_robust_condition_kappa_holds :
  robust_condition_kappa_statement -> finite_robust_condition_kappa_statement.
Proof.
move=> hR kappa K C alpha k1 K0 C1 a0 N w mu hfam h4 P hP n hn.
exact: (hR kappa K C alpha k1 K0 C1 a0 _ _ (fin_cfamily K N w mu hfam)
  (fin_cfourth K N w mu hfam kappa h4) P (finite_robust_close N w mu P hP)
  n hn).
Qed.

(* (21) at fourth moment kappa around a finite family. *)
Theorem finite_robust_condition_kappa_number_holds :
  robust_condition_kappa_number_statement ->
  finite_robust_condition_kappa_number_statement.
Proof.
move=> hR kappa K alpha k1 K0 a0 a4 N w mu hfam h4 P hP n hn.
exact: (hR kappa K alpha k1 K0 a0 a4 _ _ (fin_cfamily K N w mu hfam)
  (fin_cfourth K N w mu hfam kappa h4) P (finite_robust_close N w mu P hP)
  n hn).
Qed.

(* 4. The robust theorem from the theorem at fourth moment kappa. *)
Theorem condition_kappa_robust_holds :
  condition_kappa_theorem_statement -> condition_kappa_robust_theorem_statement.
Proof.
move=> [_ _ h20 h21].
have r20 := robust_condition_kappa_holds h20.
have r21 := robust_condition_kappa_number_holds h21.
split => //.
  exact: finite_robust_condition_kappa_holds.
exact: finite_robust_condition_kappa_number_holds.
Qed.
