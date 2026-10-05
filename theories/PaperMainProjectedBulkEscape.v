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

(* The PSD instance, with the N(0, 2) normalization of the manuscript. *)

Lemma paper_main_projected_psd_set_unit n :
  (exists v, paper_main_projected_psd_set n v) /\
  (forall v, paper_main_projected_psd_set n v ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n) v v = 1).
Proof. exact: paper_main_cone_psd_sphere_code_set. Qed.
