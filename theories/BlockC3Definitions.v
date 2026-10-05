From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import LowerDefinitions BlockOperatorDefinitions BlockOperatorNormedDefinitions.
Open Scope R_scope.

(* Port of theories/BlockC3Definitions.v from Coquelicot to MathComp-Analysis.
   It follows the port of OperatorC3Definitions, which does the same for
   matrix n.

   Every definition keeps its name, its arguments and their order.

   1. Real values. Coquelicot's R_NormedModule becomes R^o, the normed module
      view of R, as in OperatorEmbeddings. block_first_operator_space n m is
      bounded_block_NormedModule n m R^o, and the second and third operator
      spaces are nested over it as in the original. Their structure is the
      transport of BlockOperatorNormedDefinitions: the norm of an operator L
      is the norm of its coefficients block_operator_encode n m V L, the
      Euclidean norm of its m + 1 restrictions to the blocks, each measured
      with the norm of bounded_matrix_NormedModule n V, as in the original.
      The three evaluations keep the text of the original with R^o in place
      of R_NormedModule. block_first_evaluation n m L U has type R^o, which
      is R by definition, so Rabs and Stdlib's arithmetic apply to it as
      before.

   2. Frechet derivatives. In block_operator_C3, Coquelicot's
      filterdiff f (locally A) l becomes is_diff A f l of MathComp-Analysis
      (README, difference 2). Coquelicot's filterdiff says that l is linear
      with a norm bound, that is, continuous and linear, and that
      f y - f A - l (y - A) is negligible against y - A as y tends to A.
      is_diff A f l says that the differential 'd f A is a continuous linear
      map, that f y = f A + 'd f A (y - A) plus a term negligible against
      y - A as y tends to A, and that 'd f A = l. The two say the same thing.
      F keeps its type block_array n m -> R and is written
      (F : block_array n m -> R^o) inside is_diff, which needs a normed
      module structure on the codomain. R^o is R by definition, so this is
      the same map.

   3. Pointwise continuity. Coquelicot's continuous D3 A, continuity of D3 at
      the point A, becomes {for A, continuous D3} (README, difference 5).
      MathComp's continuous D3 alone would mean continuity everywhere.

   The norms, and so the topologies, are those of the original: the
   Euclidean norm of all entries on block_array n m (LowerDefinitions) and
   the transported norms of point 1 on the operator spaces. The balls are
   the norm balls, where Coquelicot's were conjunctions of component balls
   (MatrixDefinitions, BlockOperatorNormedDefinitions); they define the same
   neighbourhoods, so differentiability and continuity mean the same as in
   the original.

   The original opened no scope. The port opens R_scope after the MathComp
   imports, as the other ported definitions modules do; no arithmetic is
   written here. *)

Definition block_first_operator_space n m := bounded_block_NormedModule n m R^o.
Definition block_second_operator_space n m := bounded_block_NormedModule n m (block_first_operator_space n m).
Definition block_third_operator_space n m := bounded_block_NormedModule n m (block_second_operator_space n m).

Definition block_first_evaluation n m (L : block_first_operator_space n m) U :=
  block_operator_apply n m R^o L U.
Definition block_second_evaluation n m (H : block_second_operator_space n m) U V :=
  block_first_evaluation n m (block_operator_apply n m (block_first_operator_space n m) H V) U.
Definition block_third_evaluation n m (T : block_third_operator_space n m) U V W :=
  block_second_evaluation n m (block_operator_apply n m (block_second_operator_space n m) T W) U V.

Definition block_operator_C3 n m (F : block_array n m -> R)
    (D1 : block_array n m -> block_first_operator_space n m)
    (D2 : block_array n m -> block_second_operator_space n m)
    (D3 : block_array n m -> block_third_operator_space n m) : Prop :=
  forall A,
    is_diff A (F : block_array n m -> R^o) (block_operator_apply n m R^o (D1 A)) /\
    is_diff A D1 (block_operator_apply n m (block_first_operator_space n m) (D2 A)) /\
    is_diff A D2 (block_operator_apply n m (block_second_operator_space n m) (D3 A)) /\
    {for A, continuous D3}.
