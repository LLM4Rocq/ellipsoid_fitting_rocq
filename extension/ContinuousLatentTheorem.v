(* The continuous latent mixture (18), at Stdlib's R:
   continuous_latent_theorem proves continuous_latent_statement
   (ContinuousLatent.v). Item R3 of phase 9.

   continuous_latent_holds (Countable/Continuous) checks the components and
   the average fourth moment 11/6, and shows that for d >= 2 the point law
   of (18) and that of any countable mixture of product laws are singular:
   a measurable set of points, defined from the relation y = x or x y = -1
   between the first two coordinates and from a countable set of first
   coordinates (library/probability/atoms.v), has mass 1 for the first law
   and 0 for the second. *)

From EllipsoidUniversality Require Import ContinuousLatent.
From EllipsoidUniversality.Countable Require Import Continuous.

Theorem continuous_latent_theorem : continuous_latent_statement.
Proof. exact continuous_latent_holds. Qed.
