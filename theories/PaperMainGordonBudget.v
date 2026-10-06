(* Counting integer coordinate codes with bounded total mass. *)
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition paper_main_gordon_raise_head (xs : list nat) :=
  match xs with [] => [] | x :: rest => S x :: rest end.

Fixpoint paper_main_gordon_budget_grid (d : nat) : nat -> list (list nat) :=
  match d with
  | O => fun _ => [[]]
  | S n => fix levels K :=
      match K with
      | O => [List.repeat 0 (S n)]
      | S k => List.map (cons 0) (paper_main_gordon_budget_grid n (S k)) ++
          List.map paper_main_gordon_raise_head (levels k)
      end
  end.

Lemma paper_main_gordon_budget_zero_list xs :
  List.list_sum xs = 0 -> xs = List.repeat 0 (List.length xs).
Proof.
induction xs as [|x xs IH]; simpl; intros H; [reflexivity|].
assert (Hx : x = 0) by lia; subst x.
f_equal; apply IH; lia.
Qed.

Lemma paper_main_gordon_budget_grid_length d K xs :
  List.In xs (paper_main_gordon_budget_grid d K) -> List.length xs = d.
Proof.
revert K xs; induction d as [|d IH]; intros K.
- intros xs H; simpl in H; destruct H as [<-|[]]; reflexivity.
- induction K as [|K IK]; intros xs H.
  + simpl in H; destruct H as [<-|[]]; simpl; rewrite repeat_length; reflexivity.
  + change (In xs (map (cons 0) (paper_main_gordon_budget_grid d (S K)) ++
      map paper_main_gordon_raise_head (paper_main_gordon_budget_grid (S d) K))) in H.
    apply in_app_iff in H; destruct H as [H|H]; apply in_map_iff in H;
      destruct H as [ys [<- Hy]].
    * simpl; f_equal; apply (IH (S K)); exact Hy.
    * pose proof (IK ys Hy) as HL; destruct ys as [|y ys]; simpl in *; [lia|lia].
Qed.

Lemma paper_main_gordon_budget_grid_cover d K xs :
  List.length xs = d -> List.list_sum xs <= K ->
  List.In xs (paper_main_gordon_budget_grid d K).
Proof.
revert K xs; induction d as [|d IH]; intros K.
- intros xs HL HS; destruct xs; [simpl; auto|simpl in HL; lia].
- induction K as [|K IK]; intros xs HL HS.
  + assert (HZ : list_sum xs = 0) by lia.
    rewrite (paper_main_gordon_budget_zero_list xs HZ), HL; simpl; auto.
  + destruct xs as [|x xs]; [simpl in HL; lia|].
    change (In (x::xs) (map (cons 0) (paper_main_gordon_budget_grid d (S K)) ++
      map paper_main_gordon_raise_head (paper_main_gordon_budget_grid (S d) K))).
    apply in_app_iff; destruct x as [|x].
    * left; apply in_map; apply IH; simpl in *; lia.
    * right; apply in_map_iff; exists (x::xs); split; [reflexivity|].
      apply IK; simpl in *; lia.
Qed.

Lemma paper_main_gordon_budget_grid_cardinality d K :
  List.length (paper_main_gordon_budget_grid d K) <= 2^(d+K).
Proof.
revert K; induction d as [|d IH]; intros K.
- simpl; pose proof (Nat.pow_nonzero 2 K ltac:(lia)); lia.
- induction K as [|K IK].
  + rewrite Nat.add_0_r. change (1 <= 2^(S d)).
    pose proof (Nat.pow_nonzero 2 (S d) ltac:(lia)); lia.
  + change (length (map (cons 0) (paper_main_gordon_budget_grid d (S K)) ++
      map paper_main_gordon_raise_head (paper_main_gordon_budget_grid (S d) K)) <= 2^(S d+S K)).
    rewrite length_app, !length_map.
    pose proof (IH (S K)) as HD.
    replace (d + S K) with (S (d+K)) in HD by lia.
    replace (S d+K) with (S (d+K)) in IK by lia.
    replace (S d+S K) with (S (S (d+K))) by lia.
    simpl Nat.pow in *; lia.
Qed.
