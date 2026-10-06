(* Finite Gaussian soft min-max comparison with all analytic premises proved. *)
From Stdlib Require Import Reals List Lra.
From EllipsoidFitting Require Import Gaussian.Iterated.Definitions
  Gaussian.Covariance.Definitions Gaussian.Covariance.PathDomains
  Gordon.Covariance Gordon.Coordinates Gordon.Growth.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_image_domain K p P beta gamma J Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  gaussian_covariance_domain p (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K p P xs)).
Proof.
intros Hb Hg HY HS HJ.
apply (gaussian_covariance_image_domain K p P _ (paper_main_gordon_growth_constant beta gamma Y S) 1).
- apply paper_main_gordon_value_continuous; assumption.
- exact (proj1 (paper_main_gordon_polynomial_growth K beta gamma J Y S Hb Hg HY HS HJ)).
Qed.
