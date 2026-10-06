(* Coordinate derivatives of the actual soft min-max of a finite score array.
   J assigns each score a coordinate; injectivity is not needed here. *)
From Stdlib Require Import Reals List Lia Lra.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GibbsDefinitions GibbsWeights
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinateDerivativeDefinitions PaperMainGordonCovariance
  PaperMainGordonCalculus PaperMainGordonContinuity.
Import ListNotations.
Open Scope R_scope.

Definition paper_main_gordon_scores (J : nat -> nat -> nat) (xs : list R)
    (y s : nat) : R := List.nth (J y s) xs 0.

Definition paper_main_gordon_delta (J : nat -> nat -> nat) (a y s : nat) : R :=
  if Nat.eq_dec (J y s) a then 1 else 0.

Definition paper_main_gordon_value beta gamma J Y S (xs : list R) : R :=
  soft_minimax beta gamma (paper_main_gordon_scores J xs) Y S.

Definition paper_main_gordon_first beta gamma J Y S a (xs : list R) : R :=
  paper_main_gordon_mean beta gamma (paper_main_gordon_scores J xs)
    (paper_main_gordon_delta J a) Y S.

Definition paper_main_gordon_second beta gamma J Y S a b (xs : list R) : R :=
  paper_main_gordon_hessian beta gamma (paper_main_gordon_scores J xs)
    (paper_main_gordon_delta J a) (paper_main_gordon_delta J b) Y S.

Lemma paper_main_gordon_value_continuous K beta gamma J Y S :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%coq_nat) ->
  finite_joint_continuous K (paper_main_gordon_value beta gamma J Y S).
Proof.
intros HY HS HJ.
unfold paper_main_gordon_value; apply paper_main_gordon_soft_minimax_continuous; try assumption.
intros y s Hy Hs; unfold paper_main_gordon_scores.
apply finite_joint_continuous_nth; apply HJ; assumption.
Qed.

Lemma paper_main_gordon_delta_bound J a y s :
  Rabs (paper_main_gordon_delta J a y s) <= 1.
Proof.
unfold paper_main_gordon_delta.
destruct (Nat.eq_dec (J y s) a); simpl; rewrite ?Rabs_R1 ?Rabs_R0; lra.
Qed.

Lemma paper_main_gordon_first_bound beta gamma J Y S a xs :
  Y <> [] -> S <> [] ->
  Rabs (paper_main_gordon_first beta gamma J Y S a xs) <= 1.
Proof.
intros HY HS.
unfold paper_main_gordon_first; apply paper_main_gordon_mean_bound; try assumption.
intros y s Hy Hs; apply paper_main_gordon_delta_bound.
Qed.

Lemma paper_main_gordon_second_bound beta gamma J Y S a b xs :
  0 <= beta -> 0 <= gamma -> Y <> [] -> S <> [] ->
  Rabs (paper_main_gordon_second beta gamma J Y S a b xs) <= 2 * (beta + gamma).
Proof.
intros Hb Hg HY HS.
unfold paper_main_gordon_second.
replace (2 * (beta + gamma)) with (2 * (beta + gamma) * 1 * 1) by ring.
apply paper_main_gordon_hessian_bound; try assumption; try lra.
- intros y s Hy Hs; apply paper_main_gordon_delta_bound.
- intros y s Hy Hs; apply paper_main_gordon_delta_bound.
Qed.
