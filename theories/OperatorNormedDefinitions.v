From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import NormedTransport OperatorSpaceDefinitions OperatorRepresentation.
Open Scope R_scope.

(* Port of theories/OperatorNormedDefinitions.v from Coquelicot to
   MathComp-Analysis.

   The original declares one canonical structure,
     Canonical bounded_matrix_NormedModule n V : NormedModule R_AbsRing :=
       transport_NormedModule (operator_coefficients n V)
         (bounded_matrix_map n V) (operator_encode n V) (operator_decode n V)
         (operator_decode_encode n V) (operator_encode_decode n V).
   Its carrier is bounded_matrix_map n V, and because it is canonical, every
   term of type bounded_matrix_map n V has its operations.

   Hierarchy Builder keys instances on a type, so the port does this in two
   steps.
   1. The instance below copies the normed module structure of
      transport_NormedModule, applied to the same six arguments as in the
      original, onto bounded_matrix_map n V. This plays the part of the word
      Canonical: a term of type bounded_matrix_map n V has these operations
      and this norm, as in the original.
   2. bounded_matrix_NormedModule n V is the normedModType R of that
      instance. Its carrier is bounded_matrix_map n V, as in the original.

   What the structure says is the transport of NormedTransport, as in the
   original. The operations are those of the coefficients: L + M is
   operator_decode n V (operator_encode n V L + operator_encode n V M), c *: L
   and - L are defined in the same way, and 0 is operator_decode n V 0. The
   norm of L is the norm of operator_encode n V L. operator_coefficients n V
   carries the Euclidean norm of the n + 1 by n + 1 coefficients, each
   measured with the norm of V (the port of MatrixDefinitions keeps
   Coquelicot's product norm), so the norm of L is the same number as in the
   original.

   One thing changes, as in the port of MatrixDefinitions: the ball.
   Coquelicot's ball of L is the ball of operator_encode n V L in
   operator_coefficients n V, that is, a conjunction of component balls. Here
   it is also the ball of operator_encode n V L (NormedTransport,
   transport_ball), but the ball of operator_coefficients n V is the ball of
   its norm, so ball L e M <-> `|L - M| < e. The uniform structure therefore
   differs from Coquelicot's, while the neighbourhood filters, and so the
   topology, continuity and derivatives, are the same. *)

(* Hierarchy Builder reports redundant canonical projections when it copies
   the structure. They are harmless. *)
Local Set Warnings "-redundant-canonical-projection".

HB.instance Definition _ (n : nat) (V : normedModType R) :=
  NormedModule.copy (bounded_matrix_map n V)
    (transport_NormedModule (operator_coefficients n V) (bounded_matrix_map n V)
      (operator_encode n V) (operator_decode n V)
      (operator_decode_encode n V) (operator_encode_decode n V)).

Definition bounded_matrix_NormedModule n V : normedModType R :=
  NormedModule.clone R (bounded_matrix_map n V) _.
