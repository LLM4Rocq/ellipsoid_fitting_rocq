(* Finite Gaussian soft min-max comparison with all analytic premises proved. *)
From Stdlib Require Import Reals List Lra.
From EllipsoidFitting Require Import GaussianProductDefinitions GaussianCovarianceDefinitions
  GaussianCovarianceDomains GaussianCovarianceComparison PaperMainGordonCovariance
  PaperMainGordonCoordinates PaperMainGordonGrowth PaperMainGordonPairing.
Import ListNotations.
Open Scope R_scope.

Lemma paper_main_gordon_pairing_nonnegative K p q P Q beta gamma J Y S xs :
  0 <= beta -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  (forall y s t, In y Y -> In s S -> In t S ->
    gaussian_covariance_entry p P (J y s) (J y t) =
    gaussian_covariance_entry q Q (J y s) (J y t)) ->
  (forall y z s t, In y Y -> In z Y -> In s S -> In t S -> y <> z ->
    gaussian_covariance_entry q Q (J y s) (J z t) <=
    gaussian_covariance_entry p P (J y s) (J z t)) ->
  0 <= gaussian_covariance_pairing K p q P Q
    (fun a b => paper_main_gordon_second beta gamma J Y S a b xs).
Proof.
intros Hb HY HS HJ Hsame Hcross.
rewrite (paper_main_gordon_pairing_identity K p q P Q beta gamma J Y S xs HJ).
pose proof (paper_main_gordon_contraction_mono beta gamma
  (paper_main_gordon_scores J xs) Y S
  (paper_main_gordon_gram (fun y s k => P (J y s) k) (List.seq 0 p))
  (paper_main_gordon_gram (fun y s k => Q (J y s) k) (List.seq 0 q))
  Hb HY HS Hsame Hcross) as H.
lra.
Qed.

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

Theorem paper_main_gordon_soft_comparison K p q P Q beta gamma J Y S :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%nat) ->
  (forall y s t, In y Y -> In s S -> In t S ->
    gaussian_covariance_entry p P (J y s) (J y t) =
    gaussian_covariance_entry q Q (J y s) (J y t)) ->
  (forall y z s t, In y Y -> In z Y -> In s S -> In t S -> y <> z ->
    gaussian_covariance_entry q Q (J y s) (J z t) <=
    gaussian_covariance_entry p P (J y s) (J z t)) ->
  gaussian_covariance_domain p (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K p P xs)) /\
  gaussian_covariance_domain q (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K q Q xs)) /\
  gaussian_iterated_expectation q (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K q Q xs)) <=
  gaussian_iterated_expectation p (fun xs =>
    paper_main_gordon_value beta gamma J Y S (gaussian_covariance_image K p P xs)).
Proof.
intros Hb Hg HY HS HJ Hsame Hcross.
split; [apply paper_main_gordon_image_domain; assumption|].
split; [apply paper_main_gordon_image_domain; assumption|].
destruct (paper_main_gordon_polynomial_growth K beta gamma J Y S Hb Hg HY HS HJ)
  as [Hv [HD HD2]].
apply (gaussian_covariance_comparison K p q P Q
  (paper_main_gordon_value beta gamma J Y S)
  (paper_main_gordon_first beta gamma J Y S)
  (paper_main_gordon_second beta gamma J Y S)
  (paper_main_gordon_growth_constant beta gamma Y S) 1).
- apply paper_main_gordon_value_continuous; assumption.
- intros a Ha; apply paper_main_gordon_first_derivative; assumption.
- intros a Ha; apply paper_main_gordon_first_continuous; assumption.
- intros a b Ha Hbb; apply paper_main_gordon_second_derivative; assumption.
- intros a b Ha Hbb; apply paper_main_gordon_second_continuous; assumption.
- exact Hv.
- intros a Ha; apply HD.
- intros a b Ha Hbb; apply HD2.
- intros u Hu; apply paper_main_gordon_pairing_nonnegative; try assumption; lra.
Qed.
