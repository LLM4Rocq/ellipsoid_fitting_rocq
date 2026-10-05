From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import NormedTransport BlockOperatorDefinitions BlockOperatorRepresentation.
Open Scope R_scope.

(* Port of theories/BlockOperatorNormedDefinitions.v from Coquelicot to
   MathComp-Analysis. It follows the port of OperatorNormedDefinitions, which
   does the same for bounded_matrix_map n V.

   The original declares one canonical structure,
     Canonical bounded_block_NormedModule n m V : NormedModule R_AbsRing :=
       transport_NormedModule (block_operator_coefficients n m V)
         (bounded_block_map n m V) (block_operator_encode n m V)
         (block_operator_decode n m V) (block_operator_decode_encode n m V)
         (block_operator_encode_decode n m V).
   Its carrier is bounded_block_map n m V, and because it is canonical, every
   term of type bounded_block_map n m V has its operations.

   Hierarchy Builder keys instances on a type, so the port does this in two
   steps.
   1. The instance below copies the normed module structure of
      transport_NormedModule, applied to the same six arguments as in the
      original, onto bounded_block_map n m V. This plays the part of the word
      Canonical: a term of type bounded_block_map n m V has these operations
      and this norm, as in the original.
   2. bounded_block_NormedModule n m V is the normedModType R of that
      instance. Its carrier is bounded_block_map n m V, as in the original.

   What the structure says is the transport of NormedTransport, as in the
   original. The operations are those of the coefficients: L + M is
   block_operator_decode n m V (block_operator_encode n m V L +
   block_operator_encode n m V M), c *: L and - L are defined in the same
   way, and 0 is block_operator_decode n m V 0. The norm of L is the norm of
   block_operator_encode n m V L. block_operator_coefficients n m V is a
   nested tuple of MatrixDefinitions, which keeps Coquelicot's product norm,
   so it carries the Euclidean norm of the m + 1 operators
   block_operator_restrict n m V L i, each measured with the norm of
   bounded_matrix_NormedModule n V (OperatorNormedDefinitions). The norm of L
   is therefore the same number as in the original.

   One thing changes, as in the ports of MatrixDefinitions and
   OperatorNormedDefinitions: the ball. Coquelicot's ball of L is the ball of
   block_operator_encode n m V L in block_operator_coefficients n m V, that
   is, a conjunction of component balls. Here it is also the ball of
   block_operator_encode n m V L (NormedTransport, transport_ball), but the
   ball of block_operator_coefficients n m V is the ball of its norm, so
   ball L e M <-> `|L - M| < e. The uniform structure therefore differs from
   Coquelicot's, while the neighbourhood filters, and so the topology,
   continuity and derivatives, are the same.

   The original opened no scope and wrote no arithmetic. The port opens
   R_scope after the MathComp imports, as the other ported definitions
   modules do. *)

(* Hierarchy Builder reports redundant canonical projections when it copies
   the structure. They are harmless. *)
Local Set Warnings "-redundant-canonical-projection".

HB.instance Definition _ (n m : nat) (V : normedModType R) :=
  NormedModule.copy (bounded_block_map n m V)
    (transport_NormedModule (block_operator_coefficients n m V) (bounded_block_map n m V)
      (block_operator_encode n m V) (block_operator_decode n m V)
      (block_operator_decode_encode n m V) (block_operator_encode_decode n m V)).

Definition bounded_block_NormedModule n m V : normedModType R :=
  NormedModule.clone R (bounded_block_map n m V) _.
