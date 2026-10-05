From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions VectorCoordinateDefinitions
  JointDefinitions GoeDefinitions GaussianProductDefinitions
  RowCoordinateDefinitions RowCoordinates RowArrayDefinitions RowMarginalDefinitions
  MaximumRadiusDefinitions InterleavedMaximumRadius.
Open Scope R_scope.

(* Port of theories/RowRadiusNorm.v from Coquelicot to MathComp-Analysis.

   Every lemma and theorem keeps its name and its arguments in the same order.
   One notion changes notation: Coquelicot's norm becomes MathComp's norm,
   written `|x|%R. The vectors are the nested tuples of MatrixDefinitions,
   whose products are euclidean_product of MatrixEuclideanProduct and keep
   Coquelicot's product norm sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2) (not
   MathComp's max norm, difference 1 of analysis/README.md). On the last
   coordinate, R^o, the norm is Rabs, as Coquelicot's norm on R_NormedModule
   was. So `|vector_of_list n xs|%R is still the Euclidean norm of the S n
   coordinates, and every statement below means what the original meant:
   the square of the norm of fst (gaussian_row_pair n i xs), the first
   component of the joint vector of row i, is the sum of the squares of the
   first S n coordinates of that row.

   In gaussian_joint_expected_maximum_radius, gaussian_iterated_integrable,
   gaussian_iterated_absolutely_integrable and
   gaussian_iterated_has_expectation of GaussianProductDefinitions now ask,
   at each level, for Lebesgue integrability over the line against the
   Gaussian kernel, and record Lebesgue integrals against gaussian_density,
   in place of Coquelicot's improper Riemann integrals (difference 4 of
   analysis/README.md). The statement keeps the original text, and it is
   proved, as before, from gaussian_interleaved_expected_maximum_radius of
   InterleavedMaximumRadius, whose port states the same conjunction under
   the same meaning. No statement is weakened.

   The MathComp imports are limited to ssralg, ssrnum, Rstruct and
   normedtype, which are what the norm on vector n needs. None of them
   imports MathComp's ssreflect, ssrnat or exp into this file. So (i<N)%nat
   is Stdlib's Peano lt, which lia proves, as in the original, and the proofs
   use Stdlib's tactic syntax. The logarithm of the last theorem is written
   Rpower.ln. It is Stdlib's ln, the constant the original named and the one
   of InterleavedMaximumRadius; the qualified name keeps that meaning in an
   importer that loads MathComp's exp, where a bare ln is exp.ln. R_scope is
   opened after the imports, so the arithmetic, ^, sqrt and INR are
   Stdlib's. *)

Lemma vector_of_list_sum_squares n xs :
  length xs=S n -> `|vector_of_list n xs|%R^2 = gaussian_sum_squares xs.
Proof.
  revert xs; induction n as [|n IH]; intros xs HL.
  - destruct xs as [|a xs]; [discriminate|]; destruct xs; [|discriminate].
    change (Rabs a ^2 = a*a+0).
    destruct (Rcase_abs a); [rewrite Rabs_left|rewrite Rabs_right]; nra.
  - destruct xs as [|a xs]; [discriminate|].
    change (sqrt(Rabs a^2+`|vector_of_list n xs|%R^2)^2 = a*a+gaussian_sum_squares xs).
    rewrite pow2_sqrt by nra.
    rewrite IH by (simpl in HL; lia).
    destruct (Rcase_abs a); [rewrite Rabs_left|rewrite Rabs_right]; nra.
Qed.

Theorem gaussian_row_first_norm_squared n N i xs :
  length xs=(N*(S n+S(goe_vector_index n)))%nat -> (i<N)%nat ->
  `|fst (gaussian_row_pair n i xs)|%R^2 =
    gaussian_sum_squares (firstn (S n) (row_chunk (S n+S(goe_vector_index n)) i xs)).
Proof.
  intros HL Hi; unfold gaussian_row_pair, joint_vector_of_list; cbn [fst].
  apply vector_of_list_sum_squares; rewrite length_firstn.
  rewrite (row_chunk_length N _ i xs HL Hi), Nat.min_l by lia; reflexivity.
Qed.

Theorem gaussian_interleaved_maximum_norm_characterization n N xs :
  length xs=(N*(S n+S(goe_vector_index n)))%nat -> (0<N)%nat ->
  (forall i, (i<N)%nat -> `|fst(gaussian_row_pair n i xs)|%R^2 <=
    gaussian_maximum_radius N (S n) (row_prefixes N (S n) (S(goe_vector_index n)) xs)) /\
  (exists i, (i<N)%nat /\
    gaussian_maximum_radius N (S n) (row_prefixes N (S n) (S(goe_vector_index n)) xs) =
    `|fst(gaussian_row_pair n i xs)|%R^2).
Proof.
  intros HL HN; split.
  - intros i Hi; rewrite (gaussian_row_first_norm_squared n N i xs HL Hi).
    apply gaussian_interleaved_maximum_ge_row; assumption.
  - destruct (gaussian_interleaved_maximum_attained N (S n) (S(goe_vector_index n)) xs HL HN)
      as [i [Hi HE]].
    exists i; split; [exact Hi|].
    rewrite (gaussian_row_first_norm_squared n N i xs HL Hi); exact HE.
Qed.
