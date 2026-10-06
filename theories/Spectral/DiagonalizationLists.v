(* Bridge from the real orthogonal diagonalization to the list forms of
   Gaussian.Orthogonal. For O : 'M[R]_d and a : 'rV[R]_d, the loading
   paper_main_symmetric_loading O : nat -> nat -> R and the coefficients
   paper_main_symmetric_coefficients a : nat -> R read the entries with
   indices below d and are 0 elsewhere. For any list xs and its public
   column x = paper_main_symmetric_column xs = \col_(k < d) nth k xs 0:
   - the row gaussian_covariance_row d L i xs is (O x)_i for i < d;
   - the weighted square of the image gaussian_covariance_image d d L xs
     is sum_(i < d) a_i ((O x)_i^2 - 1), so the column and list forms are the
     same number;
   - if O^T O = 1, the loading has orthonormal rows in the exact predicate
     paper_main_gaussian_orthonormal_rows of Gaussian.Orthogonal.
   For a symmetric B the diagonalization of Spectral.SymmetricDiagonalization
   gives, for EVERY column x,
     x^T B x - trace B = sum_(i < d) a_i ((O x)_i^2 - 1),
   with O^T O = O O^T = 1, sum_i a_i^2 = paper_main_pairing B B and
   |a_i| <= b under paper_main_cone_opnorm_le B b, 0 <= b; and the same
   identity, constants and bounds in the list form. The case d = 0
   and the zero form are included. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import ring_tactic.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  Gaussian.CovarianceDefinitions PaperMainDefinitions Geometry.Psd
  Cone.ConditionOperator Spectral.Duality Gaussian.WeightedSquare
  Gaussian.Orthogonal Spectral.SymmetricDiagonalization.
From EllipsoidFitting Require Import Analysis.RealsBridge.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Definition paper_main_symmetric_loading {d : nat} (O : 'M[R]_d) (i k : nat) : R :=
  oapp (fun i' : 'I_d => oapp (fun k' : 'I_d => O i' k') 0 (insub k)) 0 (insub i).

Definition paper_main_symmetric_coefficients {d : nat} (a : 'rV[R]_d) (i : nat) : R :=
  oapp (fun i' : 'I_d => a 0 i') 0 (insub i).

Definition paper_main_symmetric_column {d : nat} (xs : list R) : 'cV[R]_d :=
  \col_(k < d) List.nth k xs 0.

Lemma paper_main_symmetric_loading_val {d : nat} (O : 'M[R]_d) (i k : 'I_d) :
  paper_main_symmetric_loading O i k = O i k.
Proof. by rewrite /paper_main_symmetric_loading !valK. Qed.

Lemma paper_main_symmetric_coefficients_val {d : nat} (a : 'rV[R]_d) (i : 'I_d) :
  paper_main_symmetric_coefficients a i = a 0 i.
Proof. by rewrite /paper_main_symmetric_coefficients valK. Qed.

(* Rows, images and the weighted square: column and list forms agree. *)

Lemma paper_main_symmetric_row {d : nat} (O : 'M[R]_d) (xs : list R) (i : 'I_d) :
  gaussian_covariance_row d (paper_main_symmetric_loading O) i xs =
  (O *m paper_main_symmetric_column xs) i 0.
Proof.
rewrite /gaussian_covariance_row finite_sum_seqE mxE.
by apply: eq_bigr => k _; rewrite paper_main_symmetric_loading_val mxE.
Qed.

Lemma paper_main_symmetric_image_nth {d : nat} (O : 'M[R]_d) (xs : list R) (i : 'I_d) :
  List.nth i (gaussian_covariance_image d d (paper_main_symmetric_loading O) xs) 0 =
  (O *m paper_main_symmetric_column xs) i 0.
Proof.
rewrite /gaussian_covariance_image (nth_map_seq _ d i (elimT ssrnat.ltP (ltn_ord i))).
exact: paper_main_symmetric_row.
Qed.

Theorem paper_main_symmetric_column_list {d : nat} (O : 'M[R]_d) (a : 'rV[R]_d)
    (xs : list R) :
  paper_main_weighted_square d (paper_main_symmetric_coefficients a)
    (gaussian_covariance_image d d (paper_main_symmetric_loading O) xs) =
  \sum_(i < d) a 0 i * ((O *m paper_main_symmetric_column xs) i 0 ^+ 2 - 1).
Proof.
rewrite /paper_main_weighted_square finite_sum_seqE.
apply: eq_bigr => i _.
by rewrite paper_main_symmetric_coefficients_val paper_main_symmetric_image_nth RpowE.
Qed.

(* Orthonormal rows in the predicate of Gaussian.Orthogonal. *)

Lemma paper_main_symmetric_loading_entry {d : nat} (O : 'M[R]_d) (i j : 'I_d) :
  gaussian_covariance_entry d (paper_main_symmetric_loading O) i j = (O *m O^T) i j.
Proof.
rewrite /gaussian_covariance_entry finite_sum_seqE mxE.
by apply: eq_bigr => k _; rewrite !paper_main_symmetric_loading_val mxE.
Qed.

Theorem paper_main_symmetric_loading_orthonormal {d : nat} (O : 'M[R]_d) :
  O^T *m O = 1%:M ->
  paper_main_gaussian_orthonormal_rows d (paper_main_symmetric_loading O).
Proof.
move=> HO a b Ha Hb.
have HO' := paper_main_symmetric_orthogonal_tr _ _ HO.
have Ha' : (a < d)%N by apply/ssrnat.ltP.
have Hb' : (b < d)%N by apply/ssrnat.ltP.
have := paper_main_symmetric_loading_entry O (Ordinal Ha') (Ordinal Hb').
rewrite HO' mxE /= => ->.
case: (Nat.eqb_spec a b) => [Hab|Hab].
  have -> : Ordinal Ha' = Ordinal Hb' by apply: val_inj.
  by rewrite eqxx mulr1n.
have Hne : (Ordinal Ha' == Ordinal Hb') = false.
  by apply/negbTE/eqP => Heq; apply: Hab; have := congr1 val Heq.
by rewrite Hne mulr0n.
Qed.

(* The quadratic identity for every column, and in list form. *)

Theorem paper_main_symmetric_quadratic_identity d (B : 'M[R]_d) :
  paper_main_symmetric B ->
  exists (O : 'M[R]_d) (a : 'rV[R]_d),
    O^T *m O = 1%:M /\ O *m O^T = 1%:M /\
    (forall x : 'cV[R]_d,
      paper_main_quadratic_form B x - paper_main_trace B =
      \sum_(i < d) a 0 i * ((O *m x) i 0 ^+ 2 - 1)) /\
    \sum_(i < d) a 0 i ^+ 2 = paper_main_pairing B B /\
    (forall b, 0 <= b -> paper_main_cone_opnorm_le B b -> forall i, `|a 0 i| <= b).
Proof.
move=> HB.
have [O [a [HO HBd]]] := paper_main_symmetric_diagonalization _ _ HB.
exists O, a; split; first exact: HO.
split; first exact: (paper_main_symmetric_orthogonal_tr _ _ HO).
split.
  move=> x.
  rewrite (paper_main_symmetric_form_diagonal _ _ _ _ HBd x).
  rewrite (paper_main_symmetric_trace_diagonal _ _ _ _ HO HBd) -sumrB.
  by apply: eq_bigr => i _; ring.
split; first by rewrite (paper_main_symmetric_frobenius_diagonal _ _ _ _ HO HBd).
move=> b Hb HBb i.
exact: (paper_main_symmetric_coefficient_bound _ _ _ _ _ HO HBd Hb HBb i).
Qed.

Theorem paper_main_symmetric_quadratic_list d (B : 'M[R]_d) :
  paper_main_symmetric B ->
  exists (L : nat -> nat -> R) (c : nat -> R),
    paper_main_gaussian_orthonormal_rows d L /\
    (forall xs : list R,
      paper_main_quadratic_form B (paper_main_symmetric_column xs) - paper_main_trace B =
      paper_main_weighted_square d c (gaussian_covariance_image d d L xs)) /\
    finite_sum (fun i => pow (c i) 2) (List.seq 0 d) = paper_main_pairing B B /\
    (forall b, 0 <= b -> paper_main_cone_opnorm_le B b ->
      forall i, (i < d)%coq_nat -> Rabs (c i) <= b).
Proof.
move=> HB.
have [O [a [HO [_ [Hid [Hfr Hbd]]]]]] := paper_main_symmetric_quadratic_identity _ _ HB.
exists (paper_main_symmetric_loading O), (paper_main_symmetric_coefficients a).
split; first exact: paper_main_symmetric_loading_orthonormal.
split.
  by move=> xs; rewrite paper_main_symmetric_column_list Hid.
split.
  rewrite finite_sum_seqE -Hfr; apply: eq_bigr => i _.
  by rewrite paper_main_symmetric_coefficients_val RpowE.
move=> b Hb HBb i Hi.
have Hi' : (i < d)%N by apply/ssrnat.ltP.
have := Hbd b Hb HBb (Ordinal Hi').
by rewrite -(paper_main_symmetric_coefficients_val a (Ordinal Hi')) RabsE.
Qed.
