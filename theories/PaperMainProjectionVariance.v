(* Reuse the checked quadratic-feature moments for nat-indexed projections. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  GaussianProductDefinitions GaussianProduct PaperMainDefinitions PaperMainGeometryPsd PaperMainMatrixDuality
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainProjectionStein PaperMainProjectionRegular.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Definition paper_main_projection_matrix d (A : nat -> nat -> R) : 'M[R]_d :=
  \matrix_(i,j) A i j.
Definition paper_main_projection_square_coefficients d (A : nat -> nat -> R) :=
  finite_sum (fun i => finite_sum (fun j => A i j^2) (List.seq 0 d)) (List.seq 0 d).

Lemma paper_main_projection_quad_matrix n A xs :
  paper_main_projection_quadratic (S n) A xs=
    pmdf_quad n (paper_main_projection_matrix (S n) A) xs.
Proof.
unfold paper_main_projection_quadratic,pmdf_quad.
rewrite paper_main_finite_sum_public; apply: eq_bigr => i _.
rewrite paper_main_finite_sum_public; apply: eq_bigr => j _.
rewrite /paper_main_projection_matrix mxE.
reflexivity.
Qed.

Theorem paper_main_projection_quadratic_covariance n A B :
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*
    paper_main_projection_quadratic (S n) B xs) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_quadratic (S n) A xs*
    paper_main_projection_quadratic (S n) B xs)=
    finite_sum (fun i => finite_sum (fun j => A i j*(B i j+B j i)) (List.seq 0 (S n))) (List.seq 0 (S n)).
Proof.
split.
- apply pmdf_regular_integrable; apply pmdf_regular_mult; apply paper_main_projection_regular_quadratic.
- transitivity (gaussian_iterated_expectation (S n)
    (fun xs => pmdf_quad n (paper_main_projection_matrix (S n) A) xs*
      pmdf_quad n (paper_main_projection_matrix (S n) B) xs)).
  + apply gaussian_iterated_expectation_ext; intros xs Hxs; rewrite !paper_main_projection_quad_matrix; reflexivity.
  + rewrite (proj2(pmdf_quad_covariance n (paper_main_projection_matrix (S n) A)
      (paper_main_projection_matrix (S n) B))).
    unfold paper_main_pairing; rewrite -big_split paper_main_finite_sum_public.
    apply: eq_bigr => i _.
    rewrite -big_split paper_main_finite_sum_public; apply: eq_bigr => j _.
    rewrite /paper_main_projection_matrix !mxE.
    change (A i j*B i j+A i j*B j i=A i j*(B i j+B j i)); ring.
Qed.

Theorem paper_main_projection_quadratic_variance n A :
  gaussian_iterated_integrable (S n) (fun xs => paper_main_projection_quadratic (S n) A xs^2) /\
  gaussian_iterated_expectation (S n) (fun xs => paper_main_projection_quadratic (S n) A xs^2)<=
    2*paper_main_projection_square_coefficients (S n) A.
Proof.
destruct(paper_main_projection_quadratic_covariance n A A) as [HI HE].
assert (EF : (fun xs => paper_main_projection_quadratic (S n) A xs^2)=
  (fun xs => paper_main_projection_quadratic (S n) A xs*paper_main_projection_quadratic (S n) A xs)).
{ apply functional_extensionality; intro xs; ring. }
rewrite EF; split; [exact HI|].
rewrite HE.
eapply Rle_trans with (finite_sum (fun i => finite_sum
  (fun j => (3/2)*A i j^2+(1/2)*A j i^2) (List.seq 0 (S n))) (List.seq 0 (S n))).
- apply finite_sum_le; intros i Hi; apply finite_sum_le; intros j Hj.
  pose proof(pow2_ge_0 (A i j-A j i)) as HP; nra.
- assert (ES : finite_sum (fun i => finite_sum (fun j => A j i^2) (List.seq 0 (S n))) (List.seq 0 (S n))=
    paper_main_projection_square_coefficients (S n) A).
  { rewrite finite_sum_swap; reflexivity. }
  transitivity ((3/2)*paper_main_projection_square_coefficients (S n) A+
    (1/2)*finite_sum (fun i => finite_sum (fun j => A j i^2) (List.seq 0 (S n))) (List.seq 0 (S n))).
  + right; unfold paper_main_projection_square_coefficients.
    rewrite -finite_sum_scale -finite_sum_scale -finite_sum_plus.
    apply finite_sum_ext; intros i Hi; rewrite finite_sum_plus !finite_sum_scale; reflexivity.
  + rewrite ES; lra.
Qed.
