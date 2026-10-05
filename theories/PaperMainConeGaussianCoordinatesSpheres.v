(* Specializations of the cone-coordinate width bridge to the actual sets of
   the paper, for matrices of size d = n+1 > 0: the PSD unit sphere
   paper_main_psd_sphere, the condition-cone sphere
   paper_main_head_cone_sphere kappa for kappa >= 1, and, under an explicit
   nonemptiness hypothesis, the head-kernel section
   paper_main_head_section kappa W. Members are symmetric (PSD by
   definition, or by pmh_loewner_psd for the condition) and have Frobenius
   norm 1. The two spheres are nonempty by pmcs_sphere_nonempty and
   paper_main_head_cone_sphere_nonempty. For each set A, the coordinate set
   paper_main_cone_code_set n A is a nonempty set of unit vectors for
   paper_main_gordon_dot D, its genuine Gordon support at a length-D list is
   paper_main_head_support (Zp xs) A, and its Gordon set width is
   E_D[paper_main_head_support (Zp xs) A]. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadCorrection PaperMainGeometryHeadSpectral
  PaperMainGeometryHeadWidth PaperMainGeometryHeadWidthCompact
  PaperMainConeProjectionSupport
  PaperMainGordonProcessCovariance PaperMainGordonSetWidth
  PaperMainGaussianFeatureCoordinates PaperMainGaussianSymmetricLawPublic
  PaperMainConeGaussianCoordinates.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Facts about the three sets. *)

Lemma paper_main_cone_psd_sphere_nonempty n :
  exists P : 'M[R]_(S n), paper_main_psd_sphere P.
Proof. by eexists; exact: (pmcs_sphere_nonempty (S n) (ltn0Sn n)). Qed.

Lemma paper_main_cone_psd_sphere_symmetric n (P : 'M[R]_(S n)) :
  paper_main_psd_sphere P -> paper_main_symmetric P.
Proof. by move=> [[HP _] _]. Qed.

Lemma paper_main_cone_psd_sphere_unit n (P : 'M[R]_(S n)) :
  paper_main_psd_sphere P -> paper_main_frobenius P = 1.
Proof. by move=> [_ H]. Qed.

Lemma paper_main_cone_condition_sphere_nonempty n kappa :
  1 <= kappa -> exists P : 'M[R]_(S n), paper_main_head_cone_sphere kappa P.
Proof.
move=> Hk.
have Hk' : (1 <= kappa)%R by apply/RleP.
by eexists; exact: (paper_main_head_cone_sphere_nonempty (S n) kappa (ltn0Sn n) Hk').
Qed.

Lemma paper_main_cone_condition_sphere_symmetric n kappa (P : 'M[R]_(S n)) :
  paper_main_head_cone_sphere kappa P -> paper_main_symmetric P.
Proof.
move=> [[lam [Hlam [Hlow _]]] _].
by have [Hs _] := pmh_loewner_psd _ P lam (ltW Hlam) Hlow.
Qed.

Lemma paper_main_cone_condition_sphere_unit n kappa (P : 'M[R]_(S n)) :
  paper_main_head_cone_sphere kappa P -> paper_main_frobenius P = 1.
Proof. by move=> [_ H]. Qed.

Lemma paper_main_cone_section_symmetric n m kappa (W : 'I_m -> 'M[R]_(S n)) P :
  paper_main_head_section kappa W P -> paper_main_symmetric P.
Proof.
move=> [[lam [Hlam [Hlow _]]] _].
by have [Hs _] := pmh_loewner_psd _ P lam (ltW Hlam) Hlow.
Qed.

Lemma paper_main_cone_section_unit n m kappa (W : 'I_m -> 'M[R]_(S n)) P :
  paper_main_head_section kappa W P -> paper_main_frobenius P = 1.
Proof. by move=> [_ [H _]]. Qed.

(* The PSD unit sphere. *)

Theorem paper_main_cone_psd_sphere_code_set n :
  (exists u, paper_main_cone_code_set n (@paper_main_psd_sphere (S n)) u) /\
  (forall u, paper_main_cone_code_set n (@paper_main_psd_sphere (S n)) u ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n) u u = 1).
Proof.
split.
- exact: (paper_main_cone_code_set_nonempty n _ (paper_main_cone_psd_sphere_nonempty n)).
- exact: (paper_main_cone_code_set_unit n _ (@paper_main_cone_psd_sphere_symmetric n)
    (@paper_main_cone_psd_sphere_unit n)).
Qed.

Theorem paper_main_cone_psd_sphere_width n :
  paper_main_gordon_set_width (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n (@paper_main_psd_sphere (S n))) =
  gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_head_support (paper_main_public_symmetric_gaussian n xs)
      (@paper_main_psd_sphere (S n))).
Proof.
exact: (paper_main_cone_code_set_width n _ (paper_main_cone_psd_sphere_nonempty n)
  (@paper_main_cone_psd_sphere_symmetric n) (@paper_main_cone_psd_sphere_unit n)).
Qed.

(* The condition-cone sphere, kappa >= 1. *)

(* The head-kernel section, under explicit nonemptiness. *)

Theorem paper_main_cone_section_code_set n m kappa (W : 'I_m -> 'M[R]_(S n)) :
  (exists P, paper_main_head_section kappa W P) ->
  (exists u, paper_main_cone_code_set n (paper_main_head_section kappa W) u) /\
  (forall u, paper_main_cone_code_set n (paper_main_head_section kappa W) u ->
    paper_main_gordon_dot (paper_main_symmetric_dimension n) u u = 1).
Proof.
move=> HA; split.
- exact: (paper_main_cone_code_set_nonempty n _ HA).
- exact: (paper_main_cone_code_set_unit n _
    (@paper_main_cone_section_symmetric n m kappa W)
    (@paper_main_cone_section_unit n m kappa W)).
Qed.

Theorem paper_main_cone_section_support n m kappa (W : 'I_m -> 'M[R]_(S n)) xs :
  (exists P, paper_main_head_section kappa W P) ->
  List.length xs = paper_main_symmetric_dimension n ->
  paper_main_gordon_set_support (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n (paper_main_head_section kappa W)) xs =
  paper_main_head_support (paper_main_public_symmetric_gaussian n xs)
    (paper_main_head_section kappa W).
Proof.
move=> HA Hxs.
exact: (paper_main_cone_code_set_support n _ xs Hxs HA
  (@paper_main_cone_section_symmetric n m kappa W)
  (@paper_main_cone_section_unit n m kappa W)).
Qed.
