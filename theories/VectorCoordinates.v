(* Port of the inner module VectorCoordinates of
   theories/InterpolationFoundations.v (and of its identical copy in
   theories/GaussianVectorProofs.v), extracted to
   build/agent2/unbundled/VectorCoordinates.v, from Coquelicot to
   MathComp-Analysis.

   Every lemma and theorem keeps its name, its arguments in the same order
   and its hypotheses. The vectors are those of the ported
   OperatorDefinitions: nested euclidean_product of R^o, with coordinates
   read by vector_entry and built by tuple_build. The lists are Stdlib's.

   The original imported the bundle GaussianCoordinateProofs and named its
   inner module GaussianCoordinatePermutations. This port imports the
   standalone module GaussianCoordinatePermutations, which is the same
   module. The original also imported FunctionalExtensionality, which it
   did not use; this port does not import it.

   Statements that change form, all without a change of meaning.

   1. Indices. With ssreflect loaded, (i <= n)%nat would mean ssrnat's
      boolean leq. The statements write (i <= n)%coq_nat, which is Stdlib's
      Peano order le, the order of the original, as in the ported
      MatrixCoordinates. This concerns vector_to_list_nth,
      vector_entry_of_list, vector_coordinate_basis_entry and
      vector_of_list_replace_line.

   2. Lists. With ssreflect loaded, the bare name nth would mean MathComp's
      seq.nth. The statements write List.nth, the function of the original.
      length is Stdlib's in both.

   3. Vector operations. Coquelicot's plus x y and scal c x become
      MathComp's (x + y)%R and (c *: x)%R on the normed module
      vector_NormedModule n. Both are componentwise on the nested pairs, as
      before, so vector_entry_plus and vector_entry_scal say the same thing.
      Their right-hand sides keep Stdlib's + and *.

   4. In vector_of_list_replace_line, the right-hand side is written
        (vector_of_list n xs + (t - List.nth i xs 0) *: chaos_basis n i)%R.
      Inside %R the scalar t - List.nth i xs 0 is parsed with MathComp's
      subtraction and zero on R. These are Stdlib's Rminus and 0 up to
      conversion (Rstruct's RminusE is proved by reflexivity), so the vector
      is the one of the original. reflexivity accepts either form against
      the other, and a rewrite from right to left finds the right-hand side
      in a goal written either way (both checked in scratch).

   The proofs follow the original ones. Coquelicot's linear_plus and
   linear_scal, applied to tuple_entry_linear, become MathComp's linearD
   and linearZZ, through the instance of MatrixCoordinates that declares
   tuple_entry V n i linear. Stdlib's rewrite A, B by tac, which does not
   parse once ssreflect is loaded, is replaced by rewrites with explicit
   side conditions. *)

From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import MatrixDefinitions MatrixCoordinates OperatorDefinitions
  TensorDefinitions SecondChaosDefinitions GaussianCoordinatePermutationDefinitions
  GaussianCoordinatePermutations VectorCoordinateDefinitions.
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
