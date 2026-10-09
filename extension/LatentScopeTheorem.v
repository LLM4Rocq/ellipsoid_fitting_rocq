(* The scope of the latent-sign law: the proof of latent_scope_statement of
   LatentSignScope, at Stdlib's R, from latent_covariance_at and
   latent_variance_at of Paired/Scope. Item S1 of phase 8. *)

From mathcomp Require Import all_ssreflect_compat.
From EllipsoidUniversality Require Import LatentSignScope.
From EllipsoidUniversality.Paired Require Import Scope.

Theorem latent_scope_theorem : latent_scope_statement.
Proof.
split.
  move=> s mu d j k hs hmu jd kd jk.
  exact: (latent_covariance_at s mu d hs hmu j k jd kd jk).
move=> s mu d hs hmu d0.
exact: (latent_variance_at s mu d hs hmu d0).
Qed.
