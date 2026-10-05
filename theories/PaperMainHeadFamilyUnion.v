(* The explicit family of all small ordered heads admits a vanishing union bound. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGaussianUnion
  PaperMainHeadFamilyCount PaperMainHeadDataRates PaperMainClippingLimits.
Import GRing.Theory Num.Theory Order.TTheory ListNotations.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_head_family_event {T : Type} N K (E : list nat -> set T) :=
  paper_main_finite_event_union (List.seq 0 (List.length (paper_main_head_families N K)))
    (fun i => E (List.nth i (paper_main_head_families N K) [])).

Lemma paper_main_head_family_event_member T N K (E : list nat -> set T) J x :
  In J (paper_main_head_families N K) -> E J x -> paper_main_head_family_event N K E x.
Proof.
move=> HJ HE; apply/paper_main_finite_event_union_member.
apply List.In_nth with (d := []) in HJ.
case: HJ => i [Hi Hnth].
exists i; split.
- apply List.in_seq; lia.
- by rewrite Hnth.
Qed.

Theorem paper_main_head_family_event_complete T N K (E : list nat -> set T) J x :
  (List.length J <= K)%coq_nat -> (forall i, In i J -> (i < N)%coq_nat) ->
  E J x -> paper_main_head_family_event N K E x.
Proof.
move=> Hlen HJ HE.
exact: paper_main_head_family_event_member (paper_main_head_families_complete N K J Hlen HJ) HE.
Qed.

Lemma paper_main_head_family_event_measurable N d K (E : list nat -> set (paper_main_sample N d)) :
  (forall J, In J (paper_main_head_families N K) -> measurable (E J)) ->
  measurable (paper_main_head_family_event N K E).
Proof.
move=> HM; apply: paper_main_gaussian_union_measurable => i Hi.
apply: HM; apply List.nth_In; apply List.in_seq in Hi; lia.
Qed.

Theorem paper_main_head_family_event_bound N d K
    (E : list nat -> set (paper_main_sample N d)) b :
  (forall J, In J (paper_main_head_families N K) -> measurable (E J)) ->
  (forall J, In J (paper_main_head_families N K) -> (paper_main_probability N d (E J) <= b%:E)%E) ->
  (paper_main_probability N d (paper_main_head_family_event N K E) <=
    (INR (List.length (paper_main_head_families N K))*b)%:E)%E.
Proof.
move=> HM HB.
have HG := paper_main_gaussian_union_bound (N*d)%N
  (List.seq 0 (List.length (paper_main_head_families N K)))
  (fun i => E (List.nth i (paper_main_head_families N K) [])) b.
rewrite List.length_seq in HG.
apply: HG.
- move=> i Hi; apply: HM; apply List.nth_In; apply List.in_seq in Hi; lia.
- move=> i Hi; apply: HB; apply List.nth_In; apply List.in_seq in Hi; lia.
Qed.
