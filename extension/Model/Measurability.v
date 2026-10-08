(* The measurability of the events of universality_statement, at Stdlib's R
   (item U11 of extension/README.md), for all n and d.

   Results:
   - paper_main_fit_event n d is measurable: pm_fit_event_measurable of
     theories/Measurability/Fit.v, which does not depend on the law.
   - measurable_unsat_value: Z |-> unsat_value n d Z (Unsat/LeastSquares)
     is a measurable function of the n features. It is the value of the
     least squares problem with the barrier 0 (unsat_value_barrier), so
     measurable_ls_barrier_value of convex/barrier_lindeberg.v applies:
     R_d^o is convex and relatively open (rel_open_convex_pd_slice) and
     contains the identity (unsat_domain_id).

   Main results to prove (phase 5, stages 2 and 3; names come with the
   proofs):
   - The events of the satisfiable phase are countable unions of closed
     sets of samples. If S > 0, then I / m <= S <= m I for some integer
     m > 0, so universality_pd_fit_event n d is the union over m of the
     samples x for which some S with I / m <= S <= m I satisfies
     x_i^T S x_i = 1 for every i; such a set of S is compact and the
     constraints are continuous in (x, S), so each set is closed. For
     universality_conditioned_fit_event n d c, dividing S by lm reduces
     the condition to I <= S <= c I with x_i^T S x_i equal to 1 / lm for
     every i, which is closed in the same way once the value 1 / lm ranges
     over a compact interval [1 / m, m].
   - The optimal squared fitting error universality_fitting_error n d is a
     measurable function of the sample: it is twice unsat_value of the
     features of the sample (as planned in Unsat/LeastSquares), and the
     features are measurable (measurable_unsat_features of Model/Rows).
   - Hence universality_error_event n d e eps is measurable for all e and
     eps. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability sesquilinear.
From GaussianAnalysis Require Import measurable_matrix euclidean least_squares.
From GaussianAnalysis Require Import real_spectral self_concordant logdet_barrier.
From GaussianAnalysis Require Import barrier_lindeberg.
From EllipsoidFitting Require Import PaperMainDefinitions Measurability.Fit.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
Import GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Stdlib's reals seen through their realType structure, which carries the
   measurable structure of MathComp-Analysis on matrices. *)
Local Notation RR := (R : realType).

(* The identity is in R_d^o = {R > 0, Tr R = d}. *)
Lemma unsat_domain_id d : unsat_domain d (mxvec (1%:M : 'M[RR]_d)).
Proof.
rewrite /unsat_domain /pd_slice /= mxvecK mxtrace1; split => //.
split; first by apply/symmetricmxP; rewrite trmx1.
by move=> x x0; rewrite mulmx1 mxdot_gt0.
Qed.

(* Phi_Z(R_d^o) is the value of the least squares problem with the
   barrier 0. *)
Lemma unsat_value_barrier n d (Z : n.-tuple 'rV[RR]_(d * d)) :
  unsat_value n d Z = ls_barrier_value Z 0 0 (unsat_domain d) 0 (fun=> 0).
Proof.
rewrite /unsat_value /ls_value /ls_barrier_value; congr inf.
apply/seteqP; split => _ [th Dth [b _ <-]]; exists th => //; exists b => //.
  by rewrite mul0r addr0.
by rewrite mul0r addr0.
Qed.

Lemma measurable_unsat_value n d :
  measurable_fun [set: n.-tuple 'rV[RR]_(d * d)]
    (fun Z => unsat_value n d Z : RR).
Proof.
apply: (eq_measurable_fun (fun Z : n.-tuple 'rV[RR]_(d * d) =>
    ls_barrier_value Z 0 0 (unsat_domain d) 0 (fun=> 0))).
  by move=> Z _; rewrite unsat_value_barrier.
apply: measurable_ls_barrier_value => //.
- exact: rel_open_convex_pd_slice.
- by exists (mxvec 1%:M); exact: unsat_domain_id.
- by move=> z _ e e0; exists 1 => // y _ _; rewrite subrr normr0.
Qed.
