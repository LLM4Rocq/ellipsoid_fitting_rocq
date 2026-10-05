From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import Rstruct.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions.
Open Scope R_scope.

(* Facts about the port of OperatorDefinitions that need proofs, kept out of
   the definitions module.

   The original defined matrix_operator_norm as real (Lub_Rbar E), and its
   importers used Coquelicot's Lub_Rbar_correct. The port uses MathComp's
   sup E. The two lemmas below say what sup E is, in Stdlib's vocabulary:
   the least upper bound (Stdlib's is_lub) when E is bounded above and
   nonempty, and 0 otherwise. real (Lub_Rbar E) has exactly the same two
   properties, which is why the port does not change the value. *)

Lemma operator_sup_is_lub (E : R -> Prop) :
  bound E -> (exists r, E r) -> is_lub E (sup E).
Proof.
  intros [M HM] [r Hr].
  have hs : has_sup E.
  { split; [exists r; exact Hr|].
    exists M; intros x Hx; apply/RleP; apply HM; exact Hx. }
  split.
  - intros x Hx; apply/RleP; exact (sup_upper_bound hs Hx).
  - intros b Hb; apply/RleP; apply ge_sup; [exists r; exact Hr|].
    intros x Hx; apply/RleP; apply Hb; exact Hx.
Qed.

(* The form in which OperatorBounds uses the definition: once the unit image
   is known to be bounded and nonempty, the operator norm is its least upper
   bound. *)
Lemma matrix_operator_norm_is_lub (n : nat) (A : matrix n) :
  bound (matrix_unit_image n A) -> (exists r, matrix_unit_image n A r) ->
  is_lub (matrix_unit_image n A) (matrix_operator_norm n A).
Proof. exact (operator_sup_is_lub (matrix_unit_image n A)). Qed.
