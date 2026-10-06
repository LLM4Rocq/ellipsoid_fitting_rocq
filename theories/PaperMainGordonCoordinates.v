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

Lemma paper_main_gordon_score_derivative J xs a y s :
  (J y s < List.length xs)%coq_nat ->
  derivable_pt_lim
    (fun t => paper_main_gordon_scores J (replace_coordinate a t xs) y s)
    (List.nth a xs 0) (paper_main_gordon_delta J a y s).
Proof.
intros HJ.
unfold paper_main_gordon_scores, paper_main_gordon_delta.
destruct (Nat.eq_dec (J y s) a) as [Heq|Hne].
- subst a; simpl; apply (derivable_pt_lim_ext (fun t : R => t)).
  + intros t; symmetry; apply replace_coordinate_nth_same; exact HJ.
  + apply derivable_pt_lim_id.
- simpl; apply (derivable_pt_lim_ext (fun _ : R => List.nth (J y s) xs 0)).
  + intros t; symmetry; apply replace_coordinate_nth_other; congruence.
  + apply derivable_pt_lim_const.
Qed.

Lemma paper_main_gordon_mean_zero beta gamma H Y S :
  Y <> [] -> S <> [] ->
  paper_main_gordon_mean beta gamma H (fun _ _ => 0) Y S = 0.
Proof.
intros HY HS.
unfold paper_main_gordon_mean, paper_main_gordon_outer, paper_main_gordon_inner.
transitivity (gibbs_average (-beta) (fun y => soft_max gamma (H y) S) Y (fun _ => 0)).
- apply gibbs_average_ext; intros y Hy; apply gibbs_average_const; exact HS.
- apply gibbs_average_const; exact HY.
Qed.

Lemma paper_main_gordon_first_derivative K beta gamma J Y S a :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%coq_nat) ->
  finite_coordinate_derivative K a (paper_main_gordon_value beta gamma J Y S)
    (paper_main_gordon_first beta gamma J Y S a).
Proof.
intros Hb Hg HY HS HJ xs Hxs.
pose proof (paper_main_gordon_curve_derivative beta gamma
  (fun t => paper_main_gordon_scores J (replace_coordinate a t xs))
  (paper_main_gordon_delta J a) Y S (List.nth a xs 0) Hb Hg HY HS) as HD.
assert (HC : forall y s, In y Y -> In s S -> derivable_pt_lim
  (fun t => paper_main_gordon_scores J (replace_coordinate a t xs) y s)
  (List.nth a xs 0) (paper_main_gordon_delta J a y s)).
{ intros y s Hy Hs; apply paper_main_gordon_score_derivative.
  rewrite Hxs; apply HJ; assumption. }
specialize (HD HC); rewrite replace_coordinate_self in HD.
apply is_derive_of_Reals; exact HD.
Qed.

Lemma paper_main_gordon_second_derivative K beta gamma J Y S a b :
  0 < beta -> 0 < gamma -> Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%coq_nat) ->
  finite_coordinate_derivative K b (paper_main_gordon_first beta gamma J Y S a)
    (paper_main_gordon_second beta gamma J Y S a b).
Proof.
intros Hb Hg HY HS HJ xs Hxs.
pose proof (paper_main_gordon_mean_curve_derivative beta gamma
  (fun t => paper_main_gordon_scores J (replace_coordinate b t xs))
  (fun _ => paper_main_gordon_delta J a) (paper_main_gordon_delta J b)
  (fun _ _ => 0) Y S (List.nth b xs 0) Hb Hg HY HS) as HD.
assert (HC : forall y s, In y Y -> In s S -> derivable_pt_lim
  (fun t => paper_main_gordon_scores J (replace_coordinate b t xs) y s)
  (List.nth b xs 0) (paper_main_gordon_delta J b y s)).
{ intros y s Hy Hs; apply paper_main_gordon_score_derivative.
  rewrite Hxs; apply HJ; assumption. }
assert (HU : forall y s, In y Y -> In s S -> derivable_pt_lim
  (fun _ : R => paper_main_gordon_delta J a y s) (List.nth b xs 0) 0).
{ intros; apply derivable_pt_lim_const. }
specialize (HD HC HU); rewrite replace_coordinate_self in HD.
rewrite (paper_main_gordon_mean_zero beta gamma (paper_main_gordon_scores J xs) Y S HY HS) Rplus_0_l in HD.
apply is_derive_of_Reals; exact HD.
Qed.

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

Lemma paper_main_gordon_first_continuous K beta gamma J Y S a :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%coq_nat) ->
  finite_joint_continuous K (paper_main_gordon_first beta gamma J Y S a).
Proof.
intros HY HS HJ.
unfold paper_main_gordon_first; apply paper_main_gordon_mean_continuous; try assumption.
- intros y s Hy Hs; unfold paper_main_gordon_scores.
  apply finite_joint_continuous_nth; apply HJ; assumption.
- intros y s Hy Hs; apply finite_joint_continuous_constant.
Qed.

Lemma paper_main_gordon_second_continuous K beta gamma J Y S a b :
  Y <> [] -> S <> [] ->
  (forall y s, In y Y -> In s S -> (J y s < K)%coq_nat) ->
  finite_joint_continuous K (paper_main_gordon_second beta gamma J Y S a b).
Proof.
intros HY HS HJ.
unfold paper_main_gordon_second; apply paper_main_gordon_hessian_continuous; try assumption.
- intros y s Hy Hs; unfold paper_main_gordon_scores.
  apply finite_joint_continuous_nth; apply HJ; assumption.
- intros y s Hy Hs; apply finite_joint_continuous_constant.
- intros y s Hy Hs; apply finite_joint_continuous_constant.
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
