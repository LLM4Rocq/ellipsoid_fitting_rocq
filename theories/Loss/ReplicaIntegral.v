(* Gaussian integration commutes with finite Gibbs replica averages.
   paper_main_loss_replica c f I k F is the k-fold iterated Gibbs average
   (gibbs_average c f I) of F over lists of k indices in I.
   - paper_main_loss_gibbs_integral and paper_main_loss_replica_integral:
     if every F js is integrable, the replica average of F is integrable,
     and its expectation is the replica average of the expectations.
   - paper_main_loss_replica_add and paper_main_loss_replica_difference:
     the replica average is additive.
   - paper_main_loss_replica_comparison: if the expectations of F js and
     G js differ by at most B for every js, so do the expectations of
     their replica averages. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import Analysis.CalculusBridge Soft.Definitions
  Analysis.FiniteSumAlgebra Gaussian.IteratedExpectationDefinitions
  Gaussian.IteratedExpectation Gaussian.FiniteSums Gibbs.Definitions
  Gibbs.Weights Loss.Replica.
Open Scope R_scope.

Lemma paper_main_loss_gibbs_integral d c f I F :
  (forall i, In i I -> gaussian_iterated_integrable d (F i)) ->
  gaussian_iterated_integrable d (fun xs => gibbs_average c f I (fun i => F i xs)) /\
  gaussian_iterated_expectation d (fun xs => gibbs_average c f I (fun i => F i xs))=
    gibbs_average c f I (fun i => gaussian_iterated_expectation d (F i)).
Proof.
intro HI; unfold gibbs_average.
assert (HW : forall i, In i I -> gaussian_iterated_integrable d (fun xs => gibbs_weight c f I i*F i xs)).
{ intros i Hi; exact(proj1(gaussian_iterated_scale d (F i) (gibbs_weight c f I i) (HI i Hi))). }
destruct(gaussian_iterated_finite_sum d I (fun i xs => gibbs_weight c f I i*F i xs) HW) as [HIS HE].
split; [exact HIS|]; rewrite HE; apply finite_sum_ext; intros i Hi.
exact(proj2(gaussian_iterated_scale d (F i) (gibbs_weight c f I i) (HI i Hi))).
Qed.

Theorem paper_main_loss_replica_integral d c f I k F :
  (forall js, List.length js=k -> List.Forall (fun j => In j I) js ->
    gaussian_iterated_integrable d (F js)) ->
  gaussian_iterated_integrable d (fun xs => paper_main_loss_replica c f I k (fun js => F js xs)) /\
  gaussian_iterated_expectation d (fun xs => paper_main_loss_replica c f I k (fun js => F js xs))=
    paper_main_loss_replica c f I k (fun js => gaussian_iterated_expectation d (F js)).
Proof.
revert F; induction k as [|k IH]; intros F HF.
- simpl; split; [apply HF; [reflexivity|constructor]|reflexivity].
- simpl.
  assert (HT : forall i, In i I ->
    gaussian_iterated_integrable d (fun xs => paper_main_loss_replica c f I k (fun js => F(i::js) xs)) /\
    gaussian_iterated_expectation d (fun xs => paper_main_loss_replica c f I k (fun js => F(i::js) xs))=
      paper_main_loss_replica c f I k (fun js => gaussian_iterated_expectation d (F(i::js)))).
  { intros i Hi; apply IH; intros js Hlen Hjs; apply HF; [simpl; rewrite Hlen; reflexivity|constructor; assumption]. }
  destruct(paper_main_loss_gibbs_integral d c f I
    (fun i xs => paper_main_loss_replica c f I k (fun js => F(i::js) xs))
    (fun i Hi => proj1(HT i Hi))) as [HI HE].
  split; [exact HI|]; rewrite HE; apply gibbs_average_ext; intros i Hi; exact(proj2(HT i Hi)).
Qed.

Lemma paper_main_loss_replica_add c f I k F G :
  paper_main_loss_replica c f I k (fun js => F js+G js)=
    paper_main_loss_replica c f I k F+paper_main_loss_replica c f I k G.
Proof.
revert F G; induction k as [|k IH]; intros F G; simpl; [reflexivity|].
transitivity (gibbs_average c f I (fun i =>
  paper_main_loss_replica c f I k (fun js => F(i::js))+
  paper_main_loss_replica c f I k (fun js => G(i::js)))).
- apply gibbs_average_ext; intros i Hi; apply IH.
- apply gibbs_average_add.
Qed.

Lemma paper_main_loss_replica_difference c f I k F G :
  paper_main_loss_replica c f I k (fun js => F js-G js)=
    paper_main_loss_replica c f I k F-paper_main_loss_replica c f I k G.
Proof.
transitivity (paper_main_loss_replica c f I k (fun js => F js+(-1)*G js)).
- apply paper_main_loss_replica_ext; intros; ring.
- rewrite paper_main_loss_replica_add paper_main_loss_replica_scale; ring.
Qed.

Theorem paper_main_loss_replica_comparison d e c f I k F G B : I<>nil ->
  (forall js, List.length js=k -> List.Forall (fun j => In j I) js ->
    gaussian_iterated_integrable d (F js)) ->
  (forall js, List.length js=k -> List.Forall (fun j => In j I) js ->
    gaussian_iterated_integrable e (G js)) ->
  (forall js, List.length js=k -> List.Forall (fun j => In j I) js ->
    Rabs(gaussian_iterated_expectation d (F js)-gaussian_iterated_expectation e (G js))<=B) ->
  Rabs(gaussian_iterated_expectation d (fun xs => paper_main_loss_replica c f I k (fun js => F js xs))-
    gaussian_iterated_expectation e (fun ys => paper_main_loss_replica c f I k (fun js => G js ys)))<=B.
Proof.
intros HI HF HG HB.
rewrite (proj2(paper_main_loss_replica_integral d c f I k F HF))
  (proj2(paper_main_loss_replica_integral e c f I k G HG)).
rewrite <- paper_main_loss_replica_difference; apply paper_main_loss_replica_bound; assumption.
Qed.
