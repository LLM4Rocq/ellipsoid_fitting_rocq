From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import Rstruct.
From mathcomp Require Import normedtype.
From mathcomp Require Import ereal.
From EllipsoidFitting Require Import Soft.Definitions Matrix.Definitions
  Matrix.OperatorDefinitions Goe.Definitions Tensor.Definitions
  Gibbs.MatrixThirdDerivativeDefinitions Chaos.SecondOrderDefinitions
  Soft.MatrixDefinitions Soft.BlockSliceDefinitions
  Soft.MinimaxDerivativeDefinitions Soft.LowerThirdDefinitions
  Matrix.BlockInjection Row.BlockDirectionDerivatives Row.ArrayDefinitions
  Row.ObservableDefinitions Row.PrefixDefinitions Row.RadiusNorm
  Radius.Definitions Radius.Regularity.
From EllipsoidFitting Require Import Tensor.GibbsCumulantAtoms
  Tensor.NestedRepresentation Chaos.SecondContractionBounds Soft.BlockSlice
  Chaos.CubicMassBounds.
Import ListNotations.
Open Scope R_scope.

(* Bounds on the sum over the rows of the third-order remainders. The
   remainder gaussian_row_remainder of row i is the chaos contraction of
   the third derivative of the nested Gibbs function of that row at the
   vector x_i = fst (gaussian_row_pair n i xs)
   (gaussian_row_remainder_slice). When the B s are symmetric, it is at
   most 4 |x_i| ^ 2 times the projective norm of that third derivative
   (gaussian_row_remainder_projective_bound). If moreover each y z is a
   unit vector with entries at most theta / sqrt (n + 1) in absolute value
   and the operator norms of the B s are at most k, then the sum over the
   rows of the absolute remainders is at most
   40 k^3 (beta + gamma)^2 theta / sqrt (n + 1) times any bound Rmax on the
   |x_i| ^ 2 (gaussian_row_remainder_radial_sum), hence times the maximum
   radius of the row prefixes (gaussian_row_remainder_maximum_sum,
   gaussian_row_remainder_absolute_sum).

   The norm on vector n is the Euclidean norm. The projective norm is an
   extended real, read through fine, which sends the infinite values to 0.
   The MathComp imports do not load ssreflect, so (i<=m)%nat is Stdlib's
   le, and R_scope is opened last, so the arithmetic is Stdlib's. *)

Theorem gaussian_row_remainder_slice n m beta gamma y B Y S t i xs :
  (i<=m)%nat ->
  gaussian_row_remainder n m beta gamma y B Y S t i xs =
  chaos_contraction n
    (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))
    (fst(gaussian_row_pair n i xs)).
Proof.
  intro Hi; unfold gaussian_row_remainder, gaussian_row_array.
  apply chaos_contraction_ext; intros U V W HU HV HW.
  apply block_row_third_from_array; exact Hi.
Qed.

Theorem gaussian_row_remainder_projective_bound n m beta gamma y B Y S t i xs :
  (i<=m)%nat -> S<>[] -> (forall s, In s S -> symmetric_matrix n (B s)) ->
  Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs) <=
  4*(`|fst(gaussian_row_pair n i xs)|)%R^2 * fine(projective_operator_norm
    (matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))).
Proof.
  intros Hi HS Hsym; rewrite gaussian_row_remainder_slice by exact Hi.
  pose proof (nested_third_atoms_represents n beta gamma
    (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
    (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs) HS) as HR.
  assert (HC : forall z s, In z Y -> In s S -> symmetric_matrix n (soft_matrix_coefficients n y B i z s)).
  { intros z s Hz Hs; unfold soft_matrix_coefficients; apply matrix_scale_symmetric, Hsym; exact Hs. }
  specialize (HR HC).
  destruct (chaos_projective_bound n _ _ (fst(gaussian_row_pair n i xs)) HR) as [r [HE [Hpos HB]]].
  rewrite HE; exact HB.
Qed.

Lemma row_finite_sum_abs_le f I : Rabs(finite_sum f I) <= finite_sum (fun i=>Rabs(f i)) I.
Proof.
  induction I as [|i I IH]; simpl; [rewrite Rabs_R0; lra|].
  eapply Rle_trans; [apply Rabs_triang|]; lra.
Qed.

Theorem gaussian_row_remainder_radial_sum n m beta gamma y B Y S t theta k xs Rmax :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  0<=Rmax -> (forall i, In i (List.seq 0 (Datatypes.S m)) -> (`|fst(gaussian_row_pair n i xs)|)%R^2<=Rmax) ->
  finite_sum (fun i=>Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*Rmax.
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HR Hr.
  pose proof (soft_matrix_row_radial_sum n beta gamma y B (List.seq 0 (Datatypes.S m)) Y S
    (fun j=>gaussian_row_matrix n t j xs) theta k (fun i=>(`|fst(gaussian_row_pair n i xs)|)%R^2) Rmax
    Hb Hg Hk Htheta HY HS (seq_NoDup _ _) Hy Hcap Hsym HB HR Hr) as Hsum.
  eapply Rle_trans with (finite_sum (fun i=>4*((`|fst(gaussian_row_pair n i xs)|)%R^2*
    fine(projective_operator_norm(matrix_nested_third_derivative n beta gamma
      (soft_matrix_row_offset n y B (List.seq 0 (Datatypes.S m)) (fun j=>gaussian_row_matrix n t j xs) i)
      (soft_matrix_coefficients n y B i) Y S (gaussian_row_matrix n t i xs))))) (List.seq 0 (Datatypes.S m))).
  - apply cubic_sum_le; intros i Hi.
    rewrite <- Rmult_assoc; apply gaussian_row_remainder_projective_bound; try assumption.
    apply in_seq in Hi; lia.
  - rewrite cubic_sum_scale.
    eapply Rle_trans; [apply Rmult_le_compat_l; [lra|exact Hsum]|].
    right; unfold Rdiv; ring.
Qed.

Theorem gaussian_row_remainder_maximum_sum n m beta gamma y B Y S t theta k xs :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  length xs=(Datatypes.S m*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  finite_sum (fun i=>Rabs(gaussian_row_remainder n m beta gamma y B Y S t i xs))
    (List.seq 0 (Datatypes.S m)) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*
    gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)
      (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S(goe_vector_index n)) xs).
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL.
  apply gaussian_row_remainder_radial_sum; try assumption.
  - exact (proj1 (gaussian_maximum_radius_bounds _ _ _)).
  - intros i Hi; apply in_seq in Hi.
    exact (proj1 (gaussian_interleaved_maximum_norm_characterization n (Datatypes.S m) xs HL ltac:(lia)) i ltac:(lia)).
Qed.

Theorem gaussian_row_remainder_absolute_sum n m beta gamma y B Y S t theta k xs :
  0<beta -> 0<gamma -> 0<=k -> 0<theta -> Y<>[] -> S<>[] ->
  (forall z, In z Y -> euclidean_norm(y z)(List.seq 0 (Datatypes.S m))=1) ->
  (forall z i, In z Y -> In i (List.seq 0 (Datatypes.S m)) -> Rabs(y z i)<=theta/sqrt(INR(Datatypes.S n))) ->
  (forall s, In s S -> symmetric_matrix n (B s)) ->
  (forall s, In s S -> matrix_operator_norm n (B s)<=k) ->
  length xs=(Datatypes.S m*(Datatypes.S n+Datatypes.S(goe_vector_index n)))%nat ->
  Rabs(finite_sum (fun i=>gaussian_row_remainder n m beta gamma y B Y S t i xs)
    (List.seq 0 (Datatypes.S m))) <=
  40*k^3*(beta+gamma)^2*theta/sqrt(INR(Datatypes.S n))*
    gaussian_maximum_radius (Datatypes.S m) (Datatypes.S n)
      (row_prefixes (Datatypes.S m) (Datatypes.S n) (Datatypes.S(goe_vector_index n)) xs).
Proof.
  intros Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL.
  eapply Rle_trans; [apply row_finite_sum_abs_le|].
  exact (gaussian_row_remainder_maximum_sum n m beta gamma y B Y S t theta k xs
    Hb Hg Hk Htheta HY HS Hy Hcap Hsym HB HL).
Qed.
