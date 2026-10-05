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

Theorem paper_main_head_family_union_tends_to_zero (N K : nat -> nat)
    (E : forall d, list nat -> set (paper_main_sample (N d) d)) C B c :
  0 <= C -> 0 <= B -> 0 < c ->
  (forall d J, In J (paper_main_head_families (N d) (K d)) -> measurable (E d J)) ->
  (exists D, forall d, Nat.le D d ->
    INR (N d) <= C*(INR d)^2 /\ INR (K d) <= B*INR d*Rpower.ln(INR d) /\
    forall J, In J (paper_main_head_families (N d) (K d)) ->
      (paper_main_probability (N d) d (E d J) <= (exp(-c*INR d*sqrt(INR d)))%:E)%E) ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d (paper_main_head_family_event (N d) (K d) (E d))) 0.
Proof.
move=> HC HB Hc HM [D HD].
have [HC0 _] := paper_main_log_successor_bound C HC.
have HC' : 0 <= B*(Rpower.ln(C+1)+2) by nra.
apply: (paper_main_clipped_head_union_tends_to_zero _ (B*(Rpower.ln(C+1)+2)) c HC' Hc).
- move=> d; exact: measure_ge0.
- have [DL HDL] := INR_unbounded (exp 1).
  exists (Nat.max D DL) => d Hdd.
  have Hlarge : exp 1 < INR d by have := le_INR DL d ltac:(lia); lra.
  have Hd : 1 <= INR d by have := exp_ineq1_le 1; lra.
  have Hlog : 1 <= Rpower.ln(INR d).
  { rewrite -(ln_exp 1); apply Rlt_le,ln_increasing; [exact: exp_pos|exact Hlarge]. }
  have [HN [HK HP]] := HD d ltac:(lia).
  have HU := paper_main_head_family_event_bound (N d) d (K d) (E d)
    (exp(-c*INR d*sqrt(INR d))) (HM d) HP.
  have HCARD := paper_main_head_families_exp (N d) (K d) C B (INR d) HC HB Hd Hlog HN HK.
  apply: le_trans HU _; rewrite lee_fin; apply/RleP.
  exact: Rmult_le_compat_r _ _ _ (Rlt_le _ _ (exp_pos _)) HCARD.
Qed.
