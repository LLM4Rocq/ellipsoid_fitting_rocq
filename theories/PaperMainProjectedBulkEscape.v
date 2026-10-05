(* Escape through the mesh for a projected standard Gaussian array. For a
   loading U whose first s rows are orthonormal in R^N
   (paper_main_projected_orthonormal) and the projected array U X of an
   N-by-M standard Gaussian array X (paper_main_projected_map), the exact law
   of PaperMainProjectedBulkLaw transports the escape tail of
   PaperMainGaussianEscapeTail: for s > 0, a nonempty set T of unit vectors
   of R^M and u > 0, the event
     inf_(v in T) |U X v| <= sqrt (s - 1) - w(T) - u
   is measurable and has probability at most exp (- u^2 / 2)
   (paper_main_projected_escape_tail). For s = 0 and w(T) >= 0 the event is
   empty (paper_main_projected_escape_zero).
   PSD instance: T is the coded PSD unit sphere of size n + 1 in
   R^D, D = paper_main_symmetric_dimension n (nonempty, unit vectors), with
   0 <= w(T) <= sqrt (D / 2) (paper_main_projected_psd_width). For the
   entries N(0, 2) of the manuscript the statistic and the threshold are
   multiplied by sqrt 2 (paper_main_projected_psd_escape). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability numfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity
  PaperMainGordonProcessCovariance PaperMainGordonSetWidth PaperMainGordonEscape
  PaperMainGaussianGordonTail PaperMainGaussianEscapeTail
  PaperMainGaussianFeatureCoordinates PaperMainConeGaussianCoordinates
  PaperMainConeGaussianCoordinatesSpheres PaperMainGaussianPsdWidth PaperMainConeProjectionSupport
  PaperMainProjectedBulkLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Local Notation T := (measurableTypeR R).

(* The escape tail of the projected array. *)

Theorem paper_main_projected_escape_tail s N M (U : nat -> nat -> R)
    (A : (nat -> R) -> Prop) (u : R) :
  (0 < s)%coq_nat -> paper_main_projected_orthonormal s N U ->
  (exists v, A v) -> (forall v, A v -> paper_main_gordon_dot M v v = 1) -> 0 < u ->
  measurable [set x : (N * M).-tuple T |
    Rle (paper_main_gordon_escape s M A (tval (paper_main_projected_map s N M U x)))
      (sqrt (INR s - 1) - paper_main_gordon_set_width M A - u)] /\
  (gaussian_product_law (N * M) [set x : (N * M).-tuple T |
    Rle (paper_main_gordon_escape s M A (tval (paper_main_projected_map s N M U x)))
      (sqrt (INR s - 1) - paper_main_gordon_set_width M A - u)] <=
    ((exp (- u ^ 2 / 2))%Rcoq)%:E)%E.
Proof.
move=> Hs HU HA HAu Hu.
set c := sqrt (INR s - 1) - paper_main_gordon_set_width M A - u.
set E := [set y : (s * M).-tuple T | Rle (paper_main_gordon_escape s M A (tval y)) c].
have mE : measurable E.
  exact: (paper_main_gaussian_continuous_le_measurable (s * M) _ c
    (paper_main_gordon_escape_continuous s M A Hs HA HAu)).
have -> : [set x : (N * M).-tuple T |
    Rle (paper_main_gordon_escape s M A (tval (paper_main_projected_map s N M U x))) c] =
  paper_main_projected_map s N M U @^-1` E by [].
split.
  have := paper_main_projected_map_measurable s N M U measurableT _ mE.
  by rewrite setTI.
rewrite (paper_main_projected_law s N M U E HU mE).
exact: (paper_main_gaussian_escape_sqrt_tail s M A u Hs HA HAu Hu).
Qed.

(* No remaining rows: the event is empty. *)

Theorem paper_main_projected_escape_zero N M (U : nat -> nat -> R)
    (A : (nat -> R) -> Prop) (u : R) :
  (exists v, A v) -> 0 <= paper_main_gordon_set_width M A -> 0 < u ->
  [set x : (N * M).-tuple T |
    Rle (paper_main_gordon_escape 0 M A (tval (paper_main_projected_map 0 N M U x)))
      (sqrt (INR 0 - 1) - paper_main_gordon_set_width M A - u)] = set0.
Proof.
move=> HA Hw Hu.
apply/seteqP; split => x //= Hx.
have Hsq : sqrt (INR 0 - 1) = 0 by apply: sqrt_neg_0; rewrite /=; lra.
rewrite Hsq in Hx.
have H1 := paper_main_gordon_escape_nonnegative 0 M A
  (paper_main_projected_image 0 N M U (tval x)) HA.
have := Rle_trans _ _ _ H1 Hx; lra.
Qed.

(* The PSD unit sphere. *)

Definition paper_main_projected_psd_set (n : nat) : (nat -> R) -> Prop :=
  paper_main_cone_code_set n (@paper_main_psd_sphere (S n)).

Lemma paper_main_projected_psd_width n :
  0 <= paper_main_gordon_set_width (paper_main_symmetric_dimension n)
    (paper_main_projected_psd_set n) <=
  sqrt (INR (paper_main_symmetric_dimension n) / 2).
Proof.
rewrite /paper_main_projected_psd_set paper_main_cone_psd_sphere_width.
have H0 := paper_main_gaussian_psd_width_nonnegative n.
have [_ H1] := paper_main_gaussian_psd_width_bounds n.
rewrite /paper_main_gaussian_psd_width /paper_main_gaussian_psd_support in H0 H1.
by split.
Qed.

Lemma paper_main_projected_scale_le (a b : R) :
  (Rle (sqrt 2 * a) (sqrt 2 * b)) <-> Rle a b.
Proof.
have H2 : 0 < sqrt 2 by apply: sqrt_lt_R0; lra.
split => H; first by apply: (Rmult_le_reg_l (sqrt 2)).
by apply: Rmult_le_compat_l; lra.
Qed.

(* The PSD instance, with the N(0, 2) normalization of the manuscript. *)

Theorem paper_main_projected_psd_escape s N n (U : nat -> nat -> R) (u : R) :
  (0 < s)%coq_nat -> paper_main_projected_orthonormal s N U -> 0 < u ->
  measurable [set x : (N * paper_main_symmetric_dimension n).-tuple T |
    Rle (sqrt 2 * paper_main_gordon_escape s (paper_main_symmetric_dimension n)
        (paper_main_projected_psd_set n)
        (tval (paper_main_projected_map s N (paper_main_symmetric_dimension n) U x)))
      (sqrt 2 * (sqrt (INR s - 1) -
        paper_main_gordon_set_width (paper_main_symmetric_dimension n)
          (paper_main_projected_psd_set n) - u))] /\
  (gaussian_product_law (N * paper_main_symmetric_dimension n)
    [set x : (N * paper_main_symmetric_dimension n).-tuple T |
    Rle (sqrt 2 * paper_main_gordon_escape s (paper_main_symmetric_dimension n)
        (paper_main_projected_psd_set n)
        (tval (paper_main_projected_map s N (paper_main_symmetric_dimension n) U x)))
      (sqrt 2 * (sqrt (INR s - 1) -
        paper_main_gordon_set_width (paper_main_symmetric_dimension n)
          (paper_main_projected_psd_set n) - u))] <=
    ((exp (- u ^ 2 / 2))%Rcoq)%:E)%E /\
  0 <= paper_main_gordon_set_width (paper_main_symmetric_dimension n)
    (paper_main_projected_psd_set n) <=
  sqrt (INR (paper_main_symmetric_dimension n) / 2).
Proof.
move=> Hs HU Hu.
set D := paper_main_symmetric_dimension n.
set A := paper_main_projected_psd_set n.
have [HA HAu] := paper_main_cone_psd_sphere_code_set n.
have Hset : [set x : (N * D).-tuple T |
    Rle (sqrt 2 * paper_main_gordon_escape s D A (tval (paper_main_projected_map s N D U x)))
      (sqrt 2 * (sqrt (INR s - 1) - paper_main_gordon_set_width D A - u))] =
  [set x : (N * D).-tuple T |
    Rle (paper_main_gordon_escape s D A (tval (paper_main_projected_map s N D U x)))
      (sqrt (INR s - 1) - paper_main_gordon_set_width D A - u)].
  by apply/seteqP; split => x /= /paper_main_projected_scale_le.
rewrite Hset.
have [mE PE] := paper_main_projected_escape_tail s N D U A u Hs HU HA HAu Hu.
split => //; split => //.
exact: paper_main_projected_psd_width.
Qed.

Lemma paper_main_projected_psd_set_unit n :
  (exists v, paper_main_projected_psd_set n v) /\
  (forall v, paper_main_projected_psd_set n v ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n) v v = 1).
Proof. exact: paper_main_cone_psd_sphere_code_set. Qed.

Theorem paper_main_projected_psd_escape_zero N n (U : nat -> nat -> R) (u : R) :
  0 < u ->
  [set x : (N * paper_main_symmetric_dimension n).-tuple T |
    Rle (sqrt 2 * paper_main_gordon_escape 0 (paper_main_symmetric_dimension n)
        (paper_main_projected_psd_set n)
        (tval (paper_main_projected_map 0 N (paper_main_symmetric_dimension n) U x)))
      (sqrt 2 * (sqrt (INR 0 - 1) -
        paper_main_gordon_set_width (paper_main_symmetric_dimension n)
          (paper_main_projected_psd_set n) - u))] = set0.
Proof.
move=> Hu.
have [HA _] := paper_main_projected_psd_set_unit n.
have [Hw _] := paper_main_projected_psd_width n.
rewrite -(paper_main_projected_escape_zero N (paper_main_symmetric_dimension n) U
  (paper_main_projected_psd_set n) u HA Hw Hu).
by apply/seteqP; split => x /= /paper_main_projected_scale_le.
Qed.
