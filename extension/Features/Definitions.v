(* The laws of one feature: the quadratic feature of a point with independent
   coordinates and the Gaussian feature, for Koehler and Sohn, "Universality
   and sharp thresholds for ellipsoid fitting" (arXiv 2608.27372, lines
   249-302 and 1004-1086 of arxiv_v1.tex). They are shared by the proofs of
   the unsatisfiable phase and of the Gaussian model.

   Features are row vectors of size d * d through mxvec, as in
   Unsat/LeastSquares: the feature of a point x of R^d is unsat_feature d x,
   the mxvec of W(x) = (x x^T - I) / sqrt d, and the inner product of
   features is mxdot, which is the Frobenius product of the matrices.

   1. tuple_point t is the column vector of the coordinates of a d-tuple t,
      as paper_main_point reads a point of a sample.
   2. data_feature_law nu d is the law of unsat_feature d x when the
      coordinates of x are independent with laws nu 0, ..., nu (d - 1): the
      image of tuple_prod nu d. For a sample of law
      universality_sample_law nu n d, the features of the n points are
      independent with this law (Model/Rows).
   3. gaussian_feature_law kappa d is the law of
      mxvec (gaussian_feature kappa A) (Gaussian/Cones) for a d x d matrix A
      with independent standard normal entries: the image of gauss (d * d)
      under g |-> g *m gaussian_feature_mx kappa d, where
      gaussian_feature_mx kappa d is the matrix of the linear map
      g |-> mxvec (gaussian_feature kappa (vec_mx g)). Its covariance is
      unsat_cov kappa d, the covariance of the quadratic feature of a point
      whose coordinates have fourth moment kappa (eq:C-kappa-trace,
      line 271), so it is the Gaussian feature of the paper's Theorem 2.9
      and Corollary 2.13. n independent Gaussian features have the law
      tuple_prod (fun=> gaussian_feature_law kappa d) n; at kappa = 3 they
      are independent GOE matrices with variance 2/d on the diagonal and
      1/d off it.

   Planned results (phase 5, stage 1), here or in Features/Regular:
   - mxvec (gaussian_feature kappa (vec_mx g)) = g *m gaussian_feature_mx
     kappa d, and (gaussian_feature_mx kappa d)^T *m gaussian_feature_mx
     kappa d = unsat_cov kappa d, so that the regularity of Gaussian features
     of convex/barrier_lindeberg.v applies to gaussian_feature_law. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Cones.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
Import GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure, which carries the
   measurable structure of MathComp-Analysis on matrices. *)
Local Notation RR := (R : realType).

(* 1. The point of a tuple of coordinates. *)

Definition tuple_point {d : nat} (t : d.-tuple (measurableTypeR R)) : 'cV[R]_d :=
  \col_(j < d) tnth t j.

(* 2. The law of the quadratic feature of a point with independent
   coordinates. *)

Definition data_feature_map d (t : d.-tuple (measurableTypeR R)) :
    'rV[RR]_(d * d) :=
  unsat_feature d (tuple_point t).

Lemma measurable_data_feature_map d :
  measurable_fun [set: d.-tuple (measurableTypeR R)] (data_feature_map d).
Proof.
apply/measurable_fun_mxP => i k; rewrite ord1; case/mxvec_indexP: k => a b.
apply: (eq_measurable_fun (fun t : d.-tuple (measurableTypeR R) =>
    ((Num.sqrt d%:R)^-1 * (tnth t a * tnth t b - (a == b)%:R)) : RR)).
  move=> t _; rewrite /data_feature_map /unsat_feature mxvecE !mxE.
  by rewrite big_ord1 !mxE.
apply: measurable_funM => //; apply: measurable_funB => //.
by apply: measurable_funM; exact: measurable_tnth.
Qed.

HB.instance Definition _ d :=
  isMeasurableFun.Build _ _ _ _ (data_feature_map d)
    (measurable_data_feature_map d).

Definition data_feature_law (nu : nat -> probability (measurableTypeR R) R)
    d : probability 'rV[RR]_(d * d) RR :=
  distribution (tuple_prod nu d) (data_feature_map d).

(* 3. The law of the Gaussian feature. *)

Definition gaussian_feature_mx (kappa : R) d : 'M[RR]_(d * d) :=
  \matrix_(p, q)
    mxvec (gaussian_feature kappa (vec_mx (delta_mx 0 p : 'rV[R]_(d * d)))) 0 q.

Definition gaussian_feature_vec (kappa : R) d (g : 'rV[RR]_(d * d)) :
    'rV[RR]_(d * d) :=
  g *m gaussian_feature_mx kappa d.

Lemma measurable_gaussian_feature_vec (kappa : R) d :
  measurable_fun [set: 'rV[RR]_(d * d)] (gaussian_feature_vec kappa d).
Proof.
rewrite /gaussian_feature_vec.
by apply: measurable_mulmx; [exact: measurable_id | exact: measurable_cst].
Qed.

HB.instance Definition _ (kappa : R) d :=
  isMeasurableFun.Build _ _ _ _ (gaussian_feature_vec kappa d)
    (measurable_gaussian_feature_vec kappa d).

Definition gaussian_feature_law (kappa : R) d : probability 'rV[RR]_(d * d) RR :=
  distribution (gauss (d * d)) (gaussian_feature_vec kappa d).
