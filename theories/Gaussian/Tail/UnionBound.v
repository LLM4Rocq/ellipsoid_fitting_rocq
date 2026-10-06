(* Finite measurable unions and their probability bound, with list multiplicity. *)
From Stdlib Require Import Reals List Lra.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
Import Order.TTheory GRing.Theory Num.Theory ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Fixpoint paper_main_finite_event_union {T : Type} (S : list nat) (E : nat -> set T) : set T :=
  match S with
  | [] => set0
  | i :: S' => E i `|` paper_main_finite_event_union S' E
  end.

Lemma paper_main_finite_event_union_member T S (E : nat -> set T) x :
  paper_main_finite_event_union S E x <-> exists i, List.In i S /\ E i x.
Proof.
induction S as [|i S IH]; simpl.
- split; [tauto|intros [j [H _]]; contradiction].
- rewrite IH; split.
  + intros [H|[j [Hj HE]]]; [exists i|exists j]; auto.
  + intros [j [[Hj|Hj] HE]]; [subst j; auto|right; exists j; auto].
Qed.

Lemma paper_main_gaussian_union_measurable d S (E : nat -> set (d.-tuple (measurableTypeR R))) :
  (forall i, List.In i S -> measurable (E i)) ->
  measurable (paper_main_finite_event_union S E).
Proof.
induction S as [|i S IH]; intro H.
- exact: measurable0.
- apply: measurableU.
  + apply H; simpl; auto.
  + apply IH; intros j Hj; apply H; simpl; auto.
Qed.

Theorem paper_main_gaussian_union_bound d S (E : nat -> set (d.-tuple (measurableTypeR R))) b :
  (forall i, List.In i S -> measurable (E i)) ->
  (forall i, List.In i S -> (gaussian_product_law d (E i) <= b%:E)%E) ->
  (gaussian_product_law d (paper_main_finite_event_union S E) <=
    (INR (List.length S)*b)%:E)%E.
Proof.
induction S as [|i S IH]; intros HM HB.
- by rewrite /= measure0 mul0r.
- have HMT : forall j, List.In j S -> measurable (E j) by intros j Hj; apply HM; simpl; auto.
  have HBT : forall j, List.In j S -> (gaussian_product_law d (E j) <= b%:E)%E by intros j Hj; apply HB; simpl; auto.
  have H0 := HB i (List.in_eq i S).
  have HT := IH HMT HBT.
  simpl paper_main_finite_event_union.
  eapply le_trans; first exact: (measureU2 _ (HM i (List.in_eq i S)) (paper_main_gaussian_union_measurable d S E HMT)).
  eapply le_trans; first exact: (leeD H0 HT).
  rewrite -EFinD lee_fin; apply/RleP.
  change (b + INR(List.length S)*b <= INR(List.length (i::S))*b).
  rewrite length_cons S_INR; lra.
Qed.
