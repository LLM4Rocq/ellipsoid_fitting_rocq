From Stdlib Require Import List Permutation PeanoNat Lia.
From EllipsoidFitting Require Import Definitions.

(** Finite complements represented by duplicate-free lists of indices.
    outside B A keeps the elements of A that are not in B (Definitions).
    For duplicate-free lists with B included in A, outside_length gives the
    length of the complement, and outside_twice_permutation shows that the
    complement of the complement is a permutation of B. *)
Lemma outside_in (i : nat) (B A : list nat) :
  In i (outside B A) <-> In i A /\ ~ In i B.
Proof.
  unfold outside. rewrite filter_In.
  destruct (in_dec Nat.eq_dec i B); simpl; intuition discriminate.
Qed.

Lemma outside_nodup (B A : list nat) :
  NoDup A -> NoDup (outside B A).
Proof. apply NoDup_filter. Qed.

Lemma outside_incl (B A : list nat) : incl (outside B A) A.
Proof.
  intros i Hi. apply outside_in in Hi. exact (proj1 Hi).
Qed.

Lemma outside_length (B A : list nat) :
  incl B A -> NoDup A -> NoDup B ->
  length (outside B A) = length A - length B.
Proof.
  intros Hincl HnodupA HnodupB.
  set (f := fun i => if in_dec Nat.eq_dec i B then false else true).
  assert (Hperm : Permutation (filter (fun i => negb (f i)) A) B).
  { apply NoDup_Permutation.
    - now apply NoDup_filter.
    - exact HnodupB.
    - intro i. rewrite filter_In. unfold f.
      destruct (in_dec Nat.eq_dec i B) as [Hi | Hi]; simpl.
      + split.
        * tauto.
        * intros _. split; [now apply Hincl | reflexivity].
      + split; [intros [_ Hfalse]; discriminate | contradiction]. }
  pose proof (Permutation_length Hperm) as Hlength.
  pose proof (filter_length f A) as Hpartition.
  unfold outside. change (length (filter f A) = length A - length B).
  lia.
Qed.

Lemma outside_twice_permutation (B A : list nat) :
  incl B A -> NoDup A -> NoDup B ->
  Permutation (outside (outside B A) A) B.
Proof.
  intros Hincl HnodupA HnodupB.
  apply NoDup_Permutation.
  - now apply outside_nodup.
  - exact HnodupB.
  - intro i. rewrite !outside_in.
    destruct (in_dec Nat.eq_dec i B); firstorder.
Qed.
