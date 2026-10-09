(* The scope of the latent-sign law: the proof of latent_scope_statement of
   LatentSignScope, at Stdlib's R, from latent_covariance_at and
   latent_variance_at of Paired/Scope. Item S1 of phase 8.

   latent_marginal_theorem, beside it: for every coordinate j < d,
   dimension one included, x_j has the law mu and h(x_j) is centered
   (latent_marginal_at of Paired/Scope). The frozen
   latent_covariance_statement asserts these two facts only together with
   a second coordinate k distinct from j, so it says nothing about the
   single coordinate of dimension one. *)

From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import numfun probability.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import PairedDefinitions.
From EllipsoidUniversality Require Import LatentSignScope.
From EllipsoidUniversality.Paired Require Import Scope.

Local Open Scope ring_scope.

Theorem latent_scope_theorem : latent_scope_statement.
Proof.
split.
  move=> s mu d j k hs hmu jd kd jk.
  exact: (latent_covariance_at s mu d hs hmu j k jd kd jk).
move=> s mu d hs hmu d0.
exact: (latent_variance_at s mu d hs hmu d0).
Qed.

(* For every j < d, dimension one included: x_j has the law mu and
   E h(x_j) = 0. *)
Theorem latent_marginal_theorem (s : R)
    (mu : probability (measurableTypeR R) R) (d j : nat) :
  0 <= s <= 1 -> paired_uniform_spec mu -> (j < d)%nat ->
  (forall A : set (measurableTypeR R), measurable A ->
     latent_point_expectation s mu d
       (fun x => \1_A (List.nth j (tval x) 0)) = fine (mu A)) /\
  latent_point_expectation s mu d
    (fun x => paired_kernel (List.nth j (tval x) 0)) = 0.
Proof.
move=> hs hmu jd.
exact: (latent_marginal_at s mu d hs hmu j jd).
Qed.
