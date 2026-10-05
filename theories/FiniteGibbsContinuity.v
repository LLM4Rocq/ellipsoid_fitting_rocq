From Stdlib Require Import Reals List Lra.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import SoftDefinitions GibbsDefinitions GibbsWeights ThirdDefinitions.
Import ListNotations.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

(* Continuity at one point of the finite Gibbs quantities. Let [E] be a
   topological space, [A] a point of [E], [I] a nonempty list of indices,
   and [F j] a score [E -> R], continuous at [A], for each [j] in [I]. Then
   the Gibbs weight of each index of [I] is continuous at [A]
   ([gibbs_weight_continuous]). If the observables [U i], [V i], [W i] are
   continuous at [A] too, so are the Gibbs average, covariance and third
   cumulant ([gibbs_average_continuous], [gibbs_covariance_continuous],
   [gibbs_cumulant3_continuous]). Continuity at [A] is MathComp's
   [{for A, continuous f}], and [R] has the topology of the absolute value
   (Rstruct_topology). The first lemmas treat sums, differences, products
   and finite sums written with Stdlib's operations.

   When [E] is a concrete type ([R], a matrix type, a product) or a
   [uniformType], Rocq's plain [apply] does not find the topology of [E] by
   unification, as for MathComp's own [continuousM]. Use ssreflect's
   [apply:], [refine], or give [E] explicitly, as in
   [apply (@gibbs_average_continuous R)]. When [E] is a variable of type
   [topologicalType], plain [apply] works. *)

Lemma continuous_Rplus_fct {E : topologicalType} (f g : E -> R) (A : E) :
  {for A, continuous f} -> {for A, continuous g} ->
  {for A, continuous (fun M => f M + g M)}.
Proof. exact: (@continuousD R R^o E f g A). Qed.

Lemma continuous_Rminus_fct {E : topologicalType} (f g : E -> R) (A : E) :
  {for A, continuous f} -> {for A, continuous g} ->
  {for A, continuous (fun M => f M - g M)}.
Proof. exact: (@continuousB R R^o E f g A). Qed.

Lemma continuous_Rmult_fct {E : topologicalType} (f g : E -> R) (A : E) :
  {for A, continuous f} -> {for A, continuous g} ->
  {for A, continuous (fun M => f M * g M)}.
Proof. exact: (@continuousM R E f g A). Qed.

Lemma finite_sum_continuous {E : topologicalType} (F : nat -> E -> R) I (A : E) :
  (forall i, In i I -> {for A, continuous (F i)}) ->
  {for A, continuous (fun M => finite_sum (fun i => F i M) I)}.
Proof.
  induction I as [|i I IH]; intros HF; simpl.
  - apply: cst_continuous.
  - apply continuous_Rplus_fct.
    + apply HF; simpl; auto.
    + apply IH; intros j Hj; apply HF; simpl; auto.
Qed.

Lemma gibbs_exp_continuous {E : topologicalType} c (F : E -> R) (A : E) :
  {for A, continuous F} -> {for A, continuous (fun M => exp (c * F M))}.
Proof.
  intros HF.
  apply (@continuous_comp E R R (fun M => c * F M) exp A).
  - apply continuous_Rmult_fct; [apply: cst_continuous | exact HF].
  - apply/continuity_ptE; apply derivable_continuous_pt, derivable_pt_exp.
Qed.

Theorem gibbs_weight_continuous {E : topologicalType} c (F : nat -> E -> R) I (A : E) i :
  I <> [] -> In i I -> (forall j, In j I -> {for A, continuous (F j)}) ->
  {for A, continuous (fun M => gibbs_weight c (fun j => F j M) I i)}.
Proof.
  intros HI Hi HF; unfold gibbs_weight, Rdiv; apply continuous_Rmult_fct.
  - apply gibbs_exp_continuous, HF; exact Hi.
  - have Hpos := partition_positive c (fun j => F j A) I HI.
    have HP : {for A, continuous (fun M => partition c (fun j => F j M) I)}.
    { unfold partition; apply finite_sum_continuous; intros j Hj.
      apply gibbs_exp_continuous, HF; exact Hj. }
    have Hne : (partition c (fun j => F j A) I != 0)%R.
    { apply/eqP; exact: Rgt_not_eq Hpos. }
    have -> : (fun M => / partition c (fun j => F j M) I) =
              (fun M => (partition c (fun j => F j M) I)^-1%R).
    { by apply: funext => M; rewrite RinvE. }
    exact: continuousV Hne HP.
Qed.

Theorem gibbs_average_continuous {E : topologicalType}
    c (F U : nat -> E -> R) I (A : E) :
  I <> [] -> (forall i, In i I -> {for A, continuous (F i)}) ->
  (forall i, In i I -> {for A, continuous (U i)}) ->
  {for A, continuous (fun M => gibbs_average c (fun i => F i M) I (fun i => U i M))}.
Proof.
  intros HI HF HU; unfold gibbs_average; apply finite_sum_continuous; intros i Hi.
  apply continuous_Rmult_fct.
  - apply gibbs_weight_continuous; assumption.
  - apply HU; exact Hi.
Qed.

Theorem gibbs_covariance_continuous {E : topologicalType}
    c (F U V : nat -> E -> R) I (A : E) :
  I <> [] -> (forall i, In i I -> {for A, continuous (F i)}) ->
  (forall i, In i I -> {for A, continuous (U i)}) ->
  (forall i, In i I -> {for A, continuous (V i)}) ->
  {for A, continuous (fun M => gibbs_covariance c (fun i => F i M) I
    (fun i => U i M) (fun i => V i M))}.
Proof.
  intros HI HF HU HV; unfold gibbs_covariance; apply continuous_Rminus_fct.
  - apply gibbs_average_continuous; [exact HI | exact HF |].
    intros i Hi; apply continuous_Rmult_fct; [apply HU | apply HV]; exact Hi.
  - apply continuous_Rmult_fct; apply gibbs_average_continuous; assumption.
Qed.

Theorem gibbs_cumulant3_continuous {E : topologicalType}
    c (F U V W : nat -> E -> R) I (A : E) :
  I <> [] -> (forall i, In i I -> {for A, continuous (F i)}) ->
  (forall i, In i I -> {for A, continuous (U i)}) ->
  (forall i, In i I -> {for A, continuous (V i)}) ->
  (forall i, In i I -> {for A, continuous (W i)}) ->
  {for A, continuous (fun M => gibbs_cumulant3 c (fun i => F i M) I
    (fun i => U i M) (fun i => V i M) (fun i => W i M))}.
Proof.
  intros HI HF HU HV HW; unfold gibbs_cumulant3.
  apply gibbs_average_continuous; [exact HI | exact HF |].
  intros i Hi; apply continuous_Rmult_fct.
  - apply continuous_Rmult_fct; apply continuous_Rminus_fct.
    + apply HU; exact Hi.
    + apply gibbs_average_continuous; assumption.
    + apply HV; exact Hi.
    + apply gibbs_average_continuous; assumption.
  - apply continuous_Rminus_fct.
    + apply HW; exact Hi.
    + apply gibbs_average_continuous; assumption.
Qed.
