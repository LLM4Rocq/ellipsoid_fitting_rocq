(* Theorem 1.2 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372), for i.i.d. points whose law is,
   at each dimension, a finite mixture of product laws, at Stdlib's R:
   mixture_theorem proves mixture_theorem_statement (MixtureStatement.v).

   mixture_statement_holds (Mixture/Theorem) proves mixture_statement: a
   well-conditioned positive definite fit below the threshold, no
   positive semidefinite fit above it, and the limit of the optimal
   fitting error. mixture_interpolation_holds (Mixture/Interpolation)
   proves mixture_interpolation_statement, the small-residual
   interpolation (Theorem 1.9) for mixture samples. *)

From EllipsoidUniversality Require Import MixtureStatement.
From EllipsoidUniversality.Mixture Require Import Interpolation.
Require Import EllipsoidUniversality.Mixture.Theorem.

Theorem mixture_theorem : mixture_theorem_statement.
Proof.
exact (conj mixture_statement_holds mixture_interpolation_holds).
Qed.
