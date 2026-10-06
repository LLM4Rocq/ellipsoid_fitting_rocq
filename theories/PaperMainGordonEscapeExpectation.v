(* Gordon's expectation bound for the escape statistic. For N > 0 and a
   nonempty set T of unit vectors of R^M,
     E ||g_N|| - w(T) <= E inf_(v in T) ||A v||,
   where A is an N-by-M standard Gaussian matrix in row-major coordinates,
   g_N is a standard Gaussian vector of R^N and w(T) is the set width
   paper_main_gordon_set_width M T. No compactness of T and no attained
   infimum is assumed.

   The proof is gordon_escape of the library. The statistic, the support
   of T and the norm of g_N are read on row vectors
   (paper_main_gordon_escape_list_of_row,
   paper_main_gordon_set_support_list_of_row,
   paper_main_gaussian_norm_list_of_row), where they are the infimum, the
   supremum and the Euclidean norm of the library for the set of column
   vectors of T, and GaussianLawBridge turns the iterated expectations into
   integrals against gauss. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality Epsilon.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCovarianceSums PaperMainGordonProcessCovariance PaperMainGaussianNorm
  PaperMainGordonSetWidth PaperMainGordonEscape.
Open Scope R_scope.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix gauss euclidean gordon escape.
From EllipsoidFitting Require Import GaussianLawBridge.
Import GRing.Theory Num.Theory Order.TTheory.

Local Open Scope classical_set_scope.

Section escape_library.
Local Notation RR := (R : realType).

Lemma paper_main_gordon_escape_finite_sum_seq n (f : nat -> R) :
  finite_sum f (List.seq 0 n) = (\sum_(j < n) f j)%R.
Proof.
revert f; induction n as [|n IH]; intro f.
- by rewrite big_ord0.
- rewrite big_ord_recl /= finite_sum_seq_shift.
  change (f 0%nat + finite_sum (fun j => f (S j)) (List.seq 0 n) =
    f 0%nat + (\sum_(j < n) f (S j))%R).
  by rewrite IH.
Qed.

Local Notation fsum_seq := paper_main_gordon_escape_finite_sum_seq.

(* The column vector of the first M values of v. *)
Definition paper_main_gordon_col M (v : nat -> R) : 'cV[RR]_M := (\col_j v j)%R.

Lemma paper_main_gordon_dot_col M (u w : nat -> R) :
  paper_main_gordon_dot M u w =
  mxdot (paper_main_gordon_col M u) (paper_main_gordon_col M w).
Proof.
rewrite /paper_main_gordon_dot fsum_seq /mxdot.
by apply: eq_bigr => i _; rewrite big_ord1 !mxE.
Qed.

Lemma paper_main_gaussian_norm_list_of_row d (g : 'rV[RR]_d) :
  paper_main_gaussian_norm (list_of_row g) = frobenius g.
Proof.
rewrite /paper_main_gaussian_norm.
rewrite -(paper_main_gaussian_squares_coordinates d _ (list_of_row_length g)).
rewrite fsum_seq RsqrtE /frobenius /mxdot big_ord1; congr Num.sqrt.
by apply: eq_bigr => i _; rewrite list_of_row_nth RpowE expr2.
Qed.

Section set_of_vectors.
Variables (M : nat) (T : (nat -> R) -> Prop).
Hypothesis HT : exists v, T v.
Hypothesis HU : forall v, T v -> paper_main_gordon_dot M v v = 1.

Let T' : set 'cV[RR]_M := [set paper_main_gordon_col M v | v in T].

Let T'1 x : T' x -> frobenius x = 1%R.
Proof. by case=> v Tv <-; rewrite /frobenius -paper_main_gordon_dot_col HU// R1E sqrtr1. Qed.

Let T'0 : T' !=set0.
Proof. by case: HT => v Tv; exists (paper_main_gordon_col M v), v. Qed.

Lemma paper_main_gordon_set_support_list_of_row (h : 'rV[RR]_M) :
  paper_main_gordon_set_support M T (list_of_row h) = gwidth_fun T' h.
Proof.
have key u : paper_main_gordon_dot M u (fun i => List.nth i (list_of_row h) 0) =
    mxdot h^T (paper_main_gordon_col M u).
  rewrite /paper_main_gordon_dot fsum_seq /mxdot; apply: eq_bigr => i _.
  by rewrite big_ord1 !mxE list_of_row_nth mulrC.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply/RleP; apply: paper_main_gordon_set_support_le => //.
    exact: list_of_row_length.
  move=> u Tu; rewrite key; apply/RleP; apply: (gwidth_ge T'1).
  by exists u.
- apply: (gwidth_le T'0) => _ [v Tv <-]; rewrite -key; apply/RleP.
  exact: paper_main_gordon_set_support_member (list_of_row_length h) Tv HU.
Qed.

Lemma paper_main_gordon_escape_list_of_row N (a : 'rV[RR]_(N * M)) :
  paper_main_gordon_escape N M T (list_of_row a) =
  escape_inf T' (vec_mx a : 'M[RR]_(N, M)).
Proof.
have key v : paper_main_gordon_escape_norm N M v (list_of_row a) =
    frobenius ((vec_mx a : 'M[RR]_(N, M)) *m paper_main_gordon_col M v).
  rewrite /paper_main_gordon_escape_norm /euclidean_norm /squared_norm fsum_seq.
  rewrite RsqrtE /frobenius /mxdot; congr Num.sqrt; apply: eq_bigr => i _.
  rewrite big_ord1 RpowE expr2 !mxE /paper_main_gordon_escape_image fsum_seq.
  suff -> : (\sum_(j < M) v j * List.nth (i * M + j)%coq_nat (list_of_row a) 0)%R =
    (\sum_j vec_mx a i j * paper_main_gordon_col M v j 0)%R by [].
  apply: eq_bigr => j _; rewrite !mxE mulrC; congr (_ * _)%R.
  by rewrite -(list_of_row_nth a (mxvec_index i j)) mxvec_index_val.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (escape_inf_ge T'0) => _ [v Tv <-]; rewrite -key; apply/RleP.
  exact: paper_main_gordon_escape_le.
- apply/RleP; apply: paper_main_gordon_escape_ge => // v Tv.
  by rewrite key; apply/RleP; apply: escape_inf_le; exists v.
Qed.

End set_of_vectors.

(* Gordon's escape bound: for an N x M Gaussian matrix A in row-major
   coordinates and a nonempty set T of unit vectors of R^M,
     E ||g_N|| - w(T) <= E inf_(v in T) ||A v||. *)
Theorem paper_main_gordon_escape_expectation N M T :
  (0 < N)%coq_nat -> (exists v, T v) ->
  (forall v, T v -> paper_main_gordon_dot M v v = 1) ->
  gaussian_iterated_expectation N paper_main_gaussian_norm -
    paper_main_gordon_set_width M T <=
  gaussian_iterated_expectation (N * M)%coq_nat (paper_main_gordon_escape N M T).
Proof.
move=> HN HT HU.
have [_ EN] := gaussian_iterated_expectation_gauss_poly _ _ _ _
  (paper_main_gaussian_norm_continuous N) (paper_main_gaussian_norm_polynomial N).
have [IW [AW _]] := paper_main_gordon_set_support_domain M T HT HU.
have [_ EW] := @gaussian_iterated_expectation_gauss _ _
  (paper_main_gordon_set_support_continuous M T HT HU) IW AW.
have [IE AE] := paper_main_gordon_escape_domain N M T HN HT HU.
have [_ EE] := @gaussian_iterated_expectation_gauss _ _
  (paper_main_gordon_escape_continuous N M T HN HT HU) IE AE.
rewrite /paper_main_gordon_set_width EN EW EE.
under [X in (X - _)]eq_Rintegral do rewrite paper_main_gaussian_norm_list_of_row.
under [X in (_ - X)]eq_Rintegral do
  rewrite (paper_main_gordon_set_support_list_of_row M T HT HU).
under [X in _ <= X]eq_Rintegral do rewrite (paper_main_gordon_escape_list_of_row M T HT N).
apply/RleP; apply: gordon_escape.
- move=> _ [v Tv <-].
  by rewrite /frobenius -paper_main_gordon_dot_col HU// R1E sqrtr1.
- by case: HT => v Tv; exists (paper_main_gordon_col M v), v.
- by apply/ssrnat.ltP.
Qed.

End escape_library.
