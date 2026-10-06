(* Coordinates of symmetric matrices and the Gordon width of a set of unit
   matrices. A matrix S : 'M[R]_(S n) is encoded by its coefficients in the
   orthonormal basis goe_basis:
     paper_main_cone_code n S k =
       trace_pair n (goe_basis n k) (paper_main_matrix_from_public n S).
   For symmetric S and U, the Gordon dot of the codes is
   paper_main_pairing S U (Parseval and the matrix roundtrip), the Euclidean
   norm of the code is paper_main_frobenius S, and the Gaussian linear form
   on the code at xs is <Zp(xs), S> for the isotropic Gaussian Zp of
   Gaussian.Symmetric.PublicLaw.

   For a nonempty set A of symmetric matrices of Frobenius norm 1,
   paper_main_cone_code_set n A is the set of nat -> R vectors whose first
   D coordinates are the code of a member. It is a nonempty set of unit
   vectors for paper_main_gordon_dot D. At every list xs of length D its
   genuine Gordon support equals paper_main_head_support (Zp xs) A: both
   suprema are compared directly and neither is assumed attained. Hence
   its Gordon set width is E_D[paper_main_head_support (Zp xs) A]. *)
From Stdlib Require Import Reals List Lia Lra Psatz Epsilon.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Matrix.Definitions Matrix.EntriesAndLinearMaps Matrix.Trace
  Tensor.Definitions Goe.Definitions Goe.MatrixBasis
  Gaussian.Iterated.Definitions Gaussian.Iterated.Expectation
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Geometry.HeadWidth
  Spectral.Transport Gordon.ProcessCovariance Gordon.Scalar Gordon.Bilinear
  Gordon.SetWidth Gaussian.Lipschitz.EuclideanNorm
  Gaussian.Symmetric.Coordinates Gaussian.Symmetric.Law
  Gaussian.Symmetric.PublicLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_cone_code n (S : 'M[R]_(S n)) : nat -> R :=
  paper_main_symmetric_coordinates n (paper_main_matrix_from_public n S).

Definition paper_main_cone_code_set n (A : set 'M[R]_(S n)) : (nat -> R) -> Prop :=
  fun u => exists S, A S /\
    forall k, (k < paper_main_symmetric_dimension n)%coq_nat -> u k = paper_main_cone_code n S k.

(* The code of a symmetric matrix. *)

Lemma paper_main_cone_code_basis n (S : 'M[R]_(S n)) k :
  paper_main_symmetric S ->
  paper_main_cone_code n S k = paper_main_pairing (paper_main_public_symmetric_basis n k) S.
Proof.
move=> HS.
rewrite /paper_main_cone_code /paper_main_symmetric_coordinates
  /paper_main_public_symmetric_basis.
rewrite (paper_main_matrix_public_pairing _ _ _ (paper_main_matrix_internal_symmetric n S HS)).
by rewrite paper_main_matrix_public_roundtrip.
Qed.

Theorem paper_main_cone_code_dot n (S U : 'M[R]_(S n)) :
  paper_main_symmetric S -> paper_main_symmetric U ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_cone_code n S) (paper_main_cone_code n U) = paper_main_pairing S U.
Proof.
move=> HS HU.
have HS' := paper_main_matrix_internal_symmetric n S HS.
have HU' := paper_main_matrix_internal_symmetric n U HU.
rewrite /paper_main_cone_code (paper_main_symmetric_coordinate_pairing n _ _ HS' HU').
rewrite (paper_main_matrix_public_pairing _ _ _ HU').
by rewrite !paper_main_matrix_public_roundtrip.
Qed.

Theorem paper_main_cone_code_norm n (S : 'M[R]_(S n)) :
  paper_main_symmetric S ->
  euclidean_norm (paper_main_cone_code n S) (List.seq 0 (paper_main_symmetric_dimension n)) =
    paper_main_frobenius S.
Proof.
move=> HS.
rewrite /paper_main_cone_code (paper_main_symmetric_coordinate_norm n _
  (paper_main_matrix_internal_symmetric n S HS)).
exact: paper_main_matrix_internal_frobenius.
Qed.

Theorem paper_main_cone_code_norm_squared n (S : 'M[R]_(S n)) :
  paper_main_symmetric S ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_cone_code n S) (paper_main_cone_code n S) = paper_main_frobenius S ^ 2.
Proof.
move=> HS.
by rewrite -paper_main_gordon_euclidean_squared (paper_main_cone_code_norm n S HS).
Qed.

Lemma paper_main_cone_code_unit n (S : 'M[R]_(S n)) :
  paper_main_symmetric S -> paper_main_frobenius S = 1 ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (paper_main_cone_code n S) (paper_main_cone_code n S) = 1.
Proof.
move=> HS H1.
rewrite (paper_main_cone_code_norm_squared n S HS) H1; exact: pow1.
Qed.

Theorem paper_main_cone_code_gaussian n (S : 'M[R]_(S n)) xs :
  paper_main_symmetric S ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n) (paper_main_cone_code n S)
    (fun i => List.nth i xs 0) =
  paper_main_pairing (paper_main_public_symmetric_gaussian n xs) S.
Proof.
move=> HS.
have HS' := paper_main_matrix_internal_symmetric n S HS.
transitivity (paper_main_pairing (paper_main_public_symmetric_gaussian n xs)
  (paper_main_matrix_to_public n (paper_main_matrix_from_public n S))); last first.
  by rewrite paper_main_matrix_public_roundtrip.
rewrite /paper_main_public_symmetric_gaussian -(paper_main_matrix_public_pairing _ _ _ HS').
rewrite -(paper_main_symmetric_coordinate_pairing n _ _
  (paper_main_symmetric_gaussian_symmetric n xs) HS').
rewrite /paper_main_gordon_dot /paper_main_cone_code; apply: finite_sum_ext => k Hk.
have Hk' := proj1 (List.in_seq _ _ _) Hk.
have HkD : (k < paper_main_symmetric_dimension n)%coq_nat by lia.
by rewrite (paper_main_symmetric_gaussian_coordinate n xs k HkD) Rmult_comm.
Qed.

(* The coordinate set of a set of unit matrices. *)

Lemma paper_main_cone_code_set_agree n u (S : 'M[R]_(S n)) xs :
  (forall k, (k < paper_main_symmetric_dimension n)%coq_nat -> u k = paper_main_cone_code n S k) ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n) u (fun i => List.nth i xs 0) =
  paper_main_gordon_dot (paper_main_symmetric_dimension n) (paper_main_cone_code n S)
    (fun i => List.nth i xs 0).
Proof.
move=> Hu; rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk.
have Hk' := proj1 (List.in_seq _ _ _) Hk.
have HkD : (k < paper_main_symmetric_dimension n)%coq_nat by lia.
by rewrite (Hu k HkD).
Qed.

Theorem paper_main_cone_code_set_nonempty n (A : set 'M[R]_(S n)) :
  (exists S, A S) -> exists u, paper_main_cone_code_set n A u.
Proof.
move=> [S HS]; exists (paper_main_cone_code n S); exists S; split => //.
Qed.

Theorem paper_main_cone_code_set_unit n (A : set 'M[R]_(S n)) :
  (forall S, A S -> paper_main_symmetric S) ->
  (forall S, A S -> paper_main_frobenius S = 1) ->
  forall u, paper_main_cone_code_set n A u ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n) u u = 1.
Proof.
move=> Hsym Hunit u [S [HS Hu]].
transitivity (paper_main_gordon_dot (paper_main_symmetric_dimension n)
  (paper_main_cone_code n S) (paper_main_cone_code n S)).
- rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk.
  have Hk' := proj1 (List.in_seq _ _ _) Hk.
  have HkD : (k < paper_main_symmetric_dimension n)%coq_nat by lia.
  by rewrite (Hu k HkD).
- exact: (paper_main_cone_code_unit n S (Hsym S HS) (Hunit S HS)).
Qed.

Lemma paper_main_cone_code_pairing_bound n xs (S : 'M[R]_(S n)) :
  List.length xs = paper_main_symmetric_dimension n ->
  paper_main_symmetric S -> paper_main_frobenius S = 1 ->
  paper_main_pairing (paper_main_public_symmetric_gaussian n xs) S <=
    paper_main_gaussian_norm xs.
Proof.
move=> Hxs HS H1.
rewrite -(paper_main_cone_code_gaussian n S xs HS).
have H := paper_main_gaussian_unit_dot_bound _ (paper_main_cone_code n S) xs Hxs
  (paper_main_cone_code_unit n S HS H1).
exact: (Rle_trans _ _ _ (Rle_abs _) H).
Qed.

Theorem paper_main_cone_code_set_support n (A : set 'M[R]_(S n)) xs :
  List.length xs = paper_main_symmetric_dimension n ->
  (exists S, A S) -> (forall S, A S -> paper_main_symmetric S) ->
  (forall S, A S -> paper_main_frobenius S = 1) ->
  paper_main_gordon_set_support (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n A) xs =
  paper_main_head_support (paper_main_public_symmetric_gaussian n xs) A.
Proof.
move=> Hxs HA Hsym Hunit.
have HT := paper_main_cone_code_set_nonempty n A HA.
have HU := paper_main_cone_code_set_unit n A Hsym Hunit.
have Hub : ubound [set paper_main_pairing (paper_main_public_symmetric_gaussian n xs) S | S in A]
    (paper_main_gaussian_norm xs).
  move=> _ [S HS <-]; apply/RleP.
  exact: (paper_main_cone_code_pairing_bound n xs S Hxs (Hsym S HS) (Hunit S HS)).
apply: Rle_antisym.
- apply: (paper_main_gordon_set_support_le _ _ _ _ Hxs HT HU).
  move=> u [S [HS Hu]].
  rewrite (paper_main_cone_code_set_agree n u S xs Hu).
  rewrite (paper_main_cone_code_gaussian n S xs (Hsym S HS)).
  apply/RleP; apply: ub_le_sup; last by exists S.
  by exists (paper_main_gaussian_norm xs).
- apply/RleP; apply: ge_sup.
    by case: HA => S HS; exists (paper_main_pairing (paper_main_public_symmetric_gaussian n xs) S), S.
  move=> _ [S HS <-]; apply/RleP.
  rewrite -(paper_main_cone_code_gaussian n S xs (Hsym S HS)).
  apply: (paper_main_gordon_set_support_member _ _ _ _ Hxs _ HU).
  by exists S; split.
Qed.

Theorem paper_main_cone_code_set_width n (A : set 'M[R]_(S n)) :
  (exists S, A S) -> (forall S, A S -> paper_main_symmetric S) ->
  (forall S, A S -> paper_main_frobenius S = 1) ->
  paper_main_gordon_set_width (paper_main_symmetric_dimension n) (paper_main_cone_code_set n A) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_head_support (paper_main_public_symmetric_gaussian n xs) A).
Proof.
move=> HA Hsym Hunit; rewrite /paper_main_gordon_set_width.
apply: gaussian_iterated_expectation_ext => xs Hxs.
exact: (paper_main_cone_code_set_support n A xs Hxs HA Hsym Hunit).
Qed.
