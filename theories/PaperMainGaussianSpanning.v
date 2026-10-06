(* Almost-sure spanning for the exact Gaussian sample law of the statement.
   The first d points provide a square submatrix when d <= n. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions PaperMainGeometryHomogeneous
  PaperMainGaussianMultivariate PaperMainPolynomialAlgebra.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.
Local Notation RT := (measurableTypeR R).

Definition paper_main_square_sample (n d : nat) (x : paper_main_sample n d) : 'M[R]_d :=
  \matrix_(i, j) paper_main_point x i j 0.

Definition paper_main_identity_sample (n d : nat) : paper_main_sample n d :=
  [tuple (((k %/ d)%N == (k %% d)%N)%:R : R) | k < (n * d)%N].

Lemma paper_main_square_sample_polynomial (n d : nat) :
  paper_main_polynomial_function (n * d)%N
    (fun x => \det (paper_main_square_sample n d x)).
Proof.
apply: paper_main_polynomial_determinant => i j.
under eq_fun do rewrite /paper_main_square_sample /paper_main_point !mxE.
exact: paper_main_polynomial_list_coordinate.
Qed.

Lemma paper_main_identity_sample_square (n d : nat) :
  (d <= n)%N -> paper_main_square_sample n d (paper_main_identity_sample n d) = 1%:M.
Proof.
move=> hdn; apply/matrixP => i j.
have hi : (i < n)%N := ltn_leq_trans (ltn_ord i) hdn.
have hk : (i * d + j < n * d)%N.
  apply: ltn_leq_trans (_ : (i * d + j < i.+1 * d)%N) _.
  + by rewrite mulSn addnC ltn_add2r.
  + exact: leq_mul.
rewrite /paper_main_square_sample /paper_main_point !mxE.
have en (s : seq R) (k : nat) : List.nth k s 0 = nth 0 s k
  by elim: s k => [|a s IH] [|k] //=.
rewrite en.
change (nth 0 (paper_main_identity_sample n d) (Ordinal hk) = (i == j)%:R).
rewrite -(tnth_nth 0) /paper_main_identity_sample tnth_mktuple /=.
have d0 : (0 < d)%N := leq_ltn_trans (leq0n j) (ltn_ord j).
by rewrite divnMDl // divn_small // addn0 modnMDl modn_small.
Qed.

Lemma paper_main_square_sample_singular_null (n d : nat) :
  (d <= n)%N ->
  gaussian_product_law (n * d)%N
    [set x | \det (paper_main_square_sample n d x) = 0] = 0%E.
Proof.
move=> hdn.
apply: paper_main_gaussian_multivariate_null;
  first exact: paper_main_square_sample_polynomial.
exists (paper_main_identity_sample n d).
by rewrite paper_main_identity_sample_square // det1 oner_eq0.
Qed.

Lemma paper_main_square_sample_spans (n d : nat) (x : paper_main_sample n d) :
  (d <= n)%N -> \det (paper_main_square_sample n d x) != 0 -> paper_main_spanning x.
Proof.
move=> hdn hdet v hv.
have hunit : paper_main_square_sample n d x \in unitmx
  by rewrite unitmxE unitfE.
have hAv : paper_main_square_sample n d x *m v = 0.
  apply/matrixP => i j.
  have hi : (i < n)%N := ltn_leq_trans (ltn_ord i) hdn.
  have h := congr1 (fun A : 'M[R]_1 => A 0 0) (hv (Ordinal hi)).
  rewrite !mxE in h.
  rewrite !mxE.
  transitivity (\sum_k (paper_main_point x (Ordinal hi))^T 0 k * v k 0);
    last exact: h.
  apply: eq_bigr => k _.
  by rewrite /paper_main_square_sample !mxE (ord1 j).
have h := congr1 (fun A : 'cV[R]_d =>
  invmx (paper_main_square_sample n d x) *m A) hAv.
by rewrite mulKmx // mulmx0 in h.
Qed.

Lemma paper_main_gaussian_spanning_ae (n d : nat) :
  (d <= n)%N ->
  {ae gaussian_product_law (n * d)%N, forall x, paper_main_spanning x}.
Proof.
move=> hdn.
exists [set x | \det (paper_main_square_sample n d x) = 0].
split.
- exact: paper_main_multivariate_zero_measurable (paper_main_square_sample_polynomial n d).
- exact: paper_main_square_sample_singular_null hdn.
- move=> x /= hnspan.
  case: (eqVneq (\det (paper_main_square_sample n d x)) 0) => // hdet.
  exfalso; apply: hnspan.
  exact: paper_main_square_sample_spans hdn hdet.
Qed.
