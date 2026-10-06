(* Vectors as lists of coordinates. vector_to_list n x lists the S n
   coordinates of x, and vector_of_list n xs is the vector whose coordinate
   i is List.nth i xs 0. They are inverse on the lists of length S n
   (vector_of_to_list, vector_to_of_list), and vector_to_list_nth and
   vector_entry_of_list read their coordinates. Coordinates are additive
   and homogeneous (vector_entry_plus, vector_entry_scal), chaos_basis n i
   is the i-th coordinate vector (vector_coordinate_basis_entry), and
   replacing coordinate i of xs by t adds (t - x_i) times it
   (vector_of_list_replace_line).

   The statements write List.nth because MathComp's seq.nth takes its
   arguments in another order, and (i <= n)%coq_nat, Stdlib's le, because
   %nat would give ssrnat's boolean leq. In vector_of_list_replace_line the
   scalar t - List.nth i xs 0 is read in %R, so its subtraction is
   MathComp's, equal to Stdlib's Rminus by conversion. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.EntriesAndLinearMaps Matrix.OperatorDefinitions Tensor.Definitions
  Chaos.SecondOrderDefinitions Analysis.CoordinatePermutationDefinitions
  Analysis.CoordinatePermutations Matrix.VectorListDefinitions.
Import GRing.Theory Num.Theory.
Import ListNotations.
Open Scope R_scope.


Lemma vector_to_list_length n (x : vector n) :
  length (vector_to_list n x) = S n.
Proof. unfold vector_to_list; rewrite List.length_map List.length_seq; reflexivity. Qed.

Lemma vector_to_list_nth n (x : vector n) i :
  (i <= n)%coq_nat -> List.nth i (vector_to_list n x) 0 = vector_entry n x i.
Proof.
  intro Hi; unfold vector_to_list.
  assert (Hlen : (i < length (List.map (vector_entry n x) (List.seq 0 (S n))))%coq_nat).
  { rewrite List.length_map List.length_seq; lia. }
  rewrite (@List.nth_indep R (List.map (vector_entry n x) (List.seq 0 (S n))) i 0 (vector_entry n x O) Hlen).
  rewrite List.map_nth (@List.seq_nth (S n) 0 i O ltac:(lia)); reflexivity.
Qed.

Lemma vector_entry_of_list n xs i :
  (i <= n)%coq_nat -> vector_entry n (vector_of_list n xs) i = List.nth i xs 0.
Proof.
  intro Hi; unfold vector_entry, vector_of_list.
  exact (tuple_entry_build R^o n i (fun k => List.nth k xs 0) Hi).
Qed.

Lemma vector_of_to_list n (x : vector n) :
  vector_of_list n (vector_to_list n x) = x.
Proof.
  apply (tuple_ext R^o n); intros i Hi.
  change (vector_entry n (vector_of_list n (vector_to_list n x)) i = vector_entry n x i).
  rewrite (vector_entry_of_list n _ i Hi) (vector_to_list_nth n x i Hi); reflexivity.
Qed.

Lemma vector_to_of_list n xs :
  length xs = S n -> vector_to_list n (vector_of_list n xs) = xs.
Proof.
  intro Hxs; apply (List.nth_ext _ _ 0 0).
  - rewrite vector_to_list_length; symmetry; exact Hxs.
  - intros i Hi; rewrite vector_to_list_length in Hi.
    rewrite (vector_to_list_nth n _ i ltac:(lia)) (vector_entry_of_list n xs i ltac:(lia)); reflexivity.
Qed.

Lemma vector_entry_plus n (x y : vector n) i :
  vector_entry n (x + y)%R i = vector_entry n x i + vector_entry n y i.
Proof. exact (linearD (tuple_entry R^o n i) x y). Qed.

Lemma vector_entry_scal n (c : R) (x : vector n) i :
  vector_entry n (c *: x)%R i = c * vector_entry n x i.
Proof. exact (linearZZ (tuple_entry R^o n i) c x). Qed.

Lemma vector_coordinate_basis_entry n i j :
  (j <= n)%coq_nat -> vector_entry n (chaos_basis n i) j = if Nat.eqb j i then 1 else 0.
Proof.
  intro Hj; unfold vector_entry, chaos_basis.
  exact (tuple_entry_build R^o n j (fun k => if Nat.eqb k i then 1 else 0) Hj).
Qed.

Theorem vector_of_list_replace_line n xs i t :
  length xs = S n -> (i <= n)%coq_nat ->
  vector_of_list n (replace_coordinate i t xs) =
  (vector_of_list n xs + (t - List.nth i xs 0) *: chaos_basis n i)%R.
Proof.
  intros Hxs Hi; apply (tuple_ext R^o n); intros j Hj.
  change (vector_entry n (vector_of_list n (replace_coordinate i t xs)) j =
    vector_entry n (GRing.add (vector_of_list n xs)
      (GRing.scale (Rminus t (List.nth i xs 0)) (chaos_basis n i))) j).
  rewrite vector_entry_plus vector_entry_scal (vector_entry_of_list n _ j Hj)
    (vector_entry_of_list n xs j Hj) (vector_coordinate_basis_entry n i j Hj).
  destruct (Nat.eq_dec j i) as [He|Hne].
  - subst j; rewrite Nat.eqb_refl (replace_coordinate_nth_same i t xs ltac:(lia)); ring.
  - assert (Hneq : Nat.eqb j i = false) by (apply Nat.eqb_neq; exact Hne).
    rewrite Hneq.
    rewrite (replace_coordinate_nth_other i j t xs ltac:(congruence)); ring.
Qed.
