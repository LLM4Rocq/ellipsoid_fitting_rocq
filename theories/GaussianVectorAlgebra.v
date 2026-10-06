From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions VectorCoordinateDefinitions
  GaussianProductDefinitions GaussianProduct GaussianVectorDefinitions GaussianVectorDomain.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.

(* Linearity of gaussian_vector_expectation, the expectation of a function
   of a standard Gaussian vector of vector n (GaussianVectorDefinitions).
   The expectation is c on the constant c (gaussian_vector_constant) and
   commutes with scaling and finite sums (gaussian_vector_scale,
   gaussian_vector_add, gaussian_vector_coordinate_sum). A finite sum of
   continuous functions bounded by C * (1 + `|x|) ^ p, for the Euclidean
   norm, satisfies gaussian_vector_domain, and its expectation is the sum
   of the expectations (gaussian_vector_polynomial_sum_domain). *)

Lemma gaussian_vector_expectation_ext n (f g : vector n -> R) :
  (forall x, f x = g x) -> gaussian_vector_expectation n f = gaussian_vector_expectation n g.
Proof.
  intros He; unfold gaussian_vector_expectation; apply gaussian_iterated_expectation_ext.
  intros xs Hxs; apply He.
Qed.

Lemma gaussian_vector_constant n c :
  gaussian_vector_integrable n (fun _ => c) /\ gaussian_vector_expectation n (fun _ => c) = c.
Proof. exact (gaussian_iterated_constant (S n) c). Qed.

Lemma gaussian_vector_scale n (f : vector n -> R) c :
  gaussian_vector_integrable n f ->
  gaussian_vector_integrable n (fun x => c * f x) /\
  gaussian_vector_expectation n (fun x => c * f x) = c * gaussian_vector_expectation n f.
Proof. exact (gaussian_iterated_scale (S n) (fun xs => f (vector_of_list n xs)) c). Qed.

Lemma gaussian_vector_add n (f g : vector n -> R) :
  gaussian_vector_integrable n f -> gaussian_vector_integrable n g ->
  gaussian_vector_integrable n (fun x => f x + g x) /\
  gaussian_vector_expectation n (fun x => f x + g x) =
    gaussian_vector_expectation n f + gaussian_vector_expectation n g.
Proof.
  exact (gaussian_iterated_add (S n) (fun xs => f (vector_of_list n xs))
    (fun xs => g (vector_of_list n xs))).
Qed.

Theorem gaussian_vector_coordinate_sum n m (F : nat -> vector n -> R) :
  (forall i, (i <= m)%coq_nat -> gaussian_vector_integrable n (F i)) ->
  gaussian_vector_integrable n (fun x => coordinate_sum m (fun i => F i x)) /\
  gaussian_vector_expectation n (fun x => coordinate_sum m (fun i => F i x)) =
    coordinate_sum m (fun i => gaussian_vector_expectation n (F i)).
Proof.
  revert F; induction m as [|m IH]; intros F HF.
  - change (gaussian_vector_integrable n (F O) /\ gaussian_vector_expectation n (F O) = gaussian_vector_expectation n (F O)).
    split; [apply HF; lia|reflexivity].
  - destruct (IH (fun i => F (S i)) ltac:(intros; apply HF; lia)) as [HI HE].
    change (gaussian_vector_integrable n (fun x => F O x + coordinate_sum m (fun i => F (S i) x)) /\
      gaussian_vector_expectation n (fun x => F O x + coordinate_sum m (fun i => F (S i) x)) =
      gaussian_vector_expectation n (F O) + coordinate_sum m (fun i => gaussian_vector_expectation n (F (S i)))).
    pose proof (gaussian_vector_add n (F O) (fun x => coordinate_sum m (fun i => F (S i) x))
      (HF O ltac:(lia)) HI) as [HA HV].
    split; [exact HA|rewrite HE in HV; exact HV].
Qed.

Lemma gaussian_vector_coordinate_sum_continuous n m (F : nat -> vector n -> R) :
  (forall i, (i <= m)%coq_nat -> forall x, {for x, continuous (F i)}) ->
  forall x, {for x, continuous (fun y => coordinate_sum m (fun i => F i y))}.
Proof.
  revert F; induction m as [|m IH]; intros F HF x.
  - apply HF; lia.
  - change {for x, continuous (fun y => F O y + coordinate_sum m (fun i => F (S i) y))}.
    have H0 : {for x, continuous (F O)} by apply HF; lia.
    have HT : {for x, continuous (fun y => coordinate_sum m (fun i => F (S i) y))}
      by apply IH; intros; apply HF; lia.
    exact (@continuousD R R^o (vector_NormedModule n) (F O)
      (fun y => coordinate_sum m (fun i => F (S i) y)) x H0 HT).
Qed.

Lemma gaussian_vector_coordinate_sum_polynomial n m p (F : nat -> vector n -> R) :
  (forall i, (i <= m)%coq_nat -> exists C : R, 0 <= C /\
    forall x, Rabs (F i x) <= C * (1 + (`|x|)%R) ^ p) ->
  exists C : R, 0 <= C /\ forall x,
    Rabs (coordinate_sum m (fun i => F i x)) <= C * (1 + (`|x|)%R) ^ p.
Proof.
  revert F; induction m as [|m IH]; intros F HF.
  - exact (HF O (Nat.le_refl O)).
  - destruct (HF O ltac:(lia)) as [C0 [HC0 H0]].
    destruct (IH (fun i => F (S i)) ltac:(intros; apply HF; lia)) as [CT [HCT HT]].
    exists (C0 + CT); split; [lra|]; intros x.
    change (Rabs (F O x + coordinate_sum m (fun i => F (S i) x)) <= (C0 + CT) * (1 + (`|x|)%R) ^ p).
    eapply Rle_trans; [apply Rabs_triang|].
    replace ((C0 + CT) * (1 + (`|x|)%R) ^ p) with
      (C0 * (1 + (`|x|)%R) ^ p + CT * (1 + (`|x|)%R) ^ p) by ring.
    apply Rplus_le_compat; [apply H0|apply HT].
Qed.

Theorem gaussian_vector_polynomial_sum_domain n m p (F : nat -> vector n -> R) :
  (forall i, (i <= m)%coq_nat -> forall x, {for x, continuous (F i)}) ->
  (forall i, (i <= m)%coq_nat -> exists C : R, 0 <= C /\
    forall x, Rabs (F i x) <= C * (1 + (`|x|)%R) ^ p) ->
  gaussian_vector_domain n (fun x => coordinate_sum m (fun i => F i x)) /\
  gaussian_vector_expectation n (fun x => coordinate_sum m (fun i => F i x)) =
    coordinate_sum m (fun i => gaussian_vector_expectation n (F i)).
Proof.
  intros HC HB; split.
  - destruct (gaussian_vector_coordinate_sum_polynomial n m p F HB) as [C [HC0 Hbound]].
    apply (gaussian_vector_polynomial_domain n _ C p).
    + apply gaussian_vector_coordinate_sum_continuous; exact HC.
    + exact HC0.
    + exact Hbound.
  - apply (proj2 (gaussian_vector_coordinate_sum n m F ltac:(
      intros i Hi; destruct (HB i Hi) as [C [HC0 Hbound]];
      exact (proj1 (gaussian_vector_polynomial_domain n (F i) C p (HC i Hi) HC0 Hbound))))).
Qed.
