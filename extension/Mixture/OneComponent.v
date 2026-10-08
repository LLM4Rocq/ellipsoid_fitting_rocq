(* A finite mixture with one component is the paper's sample law: item X7b
   of phase 6, at Stdlib's R, the first check of the representation of the
   mixture statement.

   Results.
   - one_component_probability: with one component (N = 1, weight 1) whose
     coordinate laws are nu, mixture_probability is
     universality_probability nu on every set of samples.
   - one_component_tends_to: the same for the limits of the statements.
   - one_component_family: coordinate laws of class
     universality_coordinate_law kappa K form a mixture family with one
     component (coordinate_law_component of Mixture/Component), of fourth
     moment kappa.
   - mixture_universality_statement: mixture_statement implies
     universality_statement: Theorem 1.2 for finite mixtures contains the
     theorem of Koehler and Sohn. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.probability Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import UniversalityStatement.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality.Mixture Require Import Component.

Import GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* With one component of coordinate laws nu, the mixture probability is the
   probability of the paper's sample law. *)
Lemma one_component_probability (nu : nat -> probability (measurableTypeR R) R)
    n d (E : set (paper_main_sample n d)) :
  mixture_probability 1 (fun=> 1) (fun=> nu) n d E =
  universality_probability nu n d E.
Proof.
pose t0 : n.-tuple 'I_1 := [tuple of nseq n ord0].
have all_t0 (s : n.-tuple 'I_1) : s == t0.
  by apply/eqP/eq_from_tnth => i; rewrite [LHS]ord1 [RHS]ord1.
rewrite /mixture_probability (big_pred1 t0).
  by move=> s; rewrite /= all_t0.
by rewrite big1 // mul1e.
Qed.

Lemma one_component_tends_to
    (nu : nat -> nat -> probability (measurableTypeR R) R) (n : nat -> nat)
    (E : forall d, set (paper_main_sample (n d) d)) (l : R) :
  paper_main_tends_to
    (fun d => mixture_probability 1 (fun=> 1) (fun=> nu d) (n d) d (E d)) l ->
  paper_main_tends_to
    (fun d => universality_probability (nu d) (n d) d (E d)) l.
Proof.
have -> : (fun d => universality_probability (nu d) (n d) d (E d)) =
    (fun d => mixture_probability 1 (fun=> 1) (fun=> nu d) (n d) d (E d)).
  by apply/funext => d; rewrite one_component_probability.
by [].
Qed.

(* Coordinate laws of class universality_coordinate_law kappa K form a
   mixture family with one component, of fourth moment kappa. *)
Lemma one_component_family (kappa K : R)
    (nu : nat -> nat -> probability (measurableTypeR R) R) :
  (forall d j, (j < d)%N -> universality_coordinate_law kappa K (nu d j)) ->
  mixture_family K (fun=> 1%N) (fun _ _ => 1) (fun d => fun=> nu d) /\
  mixture_fourth_moment kappa (fun=> 1%N) (fun _ _ => 1) (fun d => fun=> nu d).
Proof.
move=> hnu; split.
  move=> d; split => //; split; first by rewrite big_ord1.
  by move=> s j _ jd; exact: coordinate_law_component (hnu d j jd).
move=> d j jd; rewrite big_ord1 mul1e.
by case: (hnu d j jd) => _ [_ [_ [h4 _]]].
Qed.

(* Theorem 1.2 for finite mixtures of product laws contains Theorem 1.2 of
   Koehler and Sohn: a sample of the paper is a mixture with one
   component. *)
Theorem mixture_universality_statement :
  mixture_statement -> universality_statement.
Proof.
move=> hM kappa K alpha k1 K0 a0.
have [h1 h2 h3] := hM kappa K alpha k1 K0 a0.
split.
  move=> aast; have [c [c1 [m1 [m2 h]]]] := h1 aast.
  exists c; split => //; split => //; split => // nu hnu n hn.
  have [hf h4] := one_component_family kappa K nu hnu.
  have [t1 t2] := h _ _ _ hf h4 n hn.
  by split; apply: one_component_tends_to; [exact: t1|exact: t2].
move=> aast; have [e0 [m1 h]] := h2 aast; have [m3 h'] := h3.
split => //; split => //; split => // nu hnu n hn.
have [hf h4] := one_component_family kappa K nu hnu.
split; first by apply: one_component_tends_to; exact: h _ _ _ hf h4 n hn.
move=> eps eps0; apply: one_component_tends_to.
exact: h' _ _ _ hf h4 n hn eps eps0.
Qed.
