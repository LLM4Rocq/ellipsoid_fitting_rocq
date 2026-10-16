(* Gaussian quadric exclusion (S3 of the shifted-Gaussian plan).
   This file contains the statement only. The exceptional event is chosen
   before the sample and before all quadratic, linear and constant terms.
   quadric_eval Q v c x = <x,Qx> + <v,x> + c; thus v is the full linear
   coefficient, equal to twice the vector ell in the informal notation.
   The quadratic part must be positive semidefinite and nonzero. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis.matrix Require Import psd_part quadric_certificate.
From EllipsoidFitting Require Import PaperMainDefinitions GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition shifted_quadric_statement : Prop :=
  forall (alpha : R) (n : nat -> nat),
    4%:R^-1 < alpha -> universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps ->
  exists D : nat, forall d : nat, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (gaussian_product_law (n d*d) E <= eps%:E)%E &
    forall x : paper_main_sample (n d) d, ~ E x ->
    forall (Q : 'M[RR]_d) (v : 'cV[RR]_d) (c : R),
      psdmx Q -> Q != 0 ->
      ~ (forall i : 'I_(n d),
        quadric_eval Q v c (paper_main_point x i) = 0)].
