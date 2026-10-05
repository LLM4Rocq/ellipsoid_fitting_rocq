(* Gaussian coordinate moments of degree two and four, with their
   integrability domains: the coordinate part of the moments of
   PaperMainDataFeatureMoments.

   E is the iterated Gaussian expectation gaussian_iterated_expectation of
   GaussianProductDefinitions in dimension S n. Its coordinates are
   x_a = List.nth a xs 0, and delta_ab = pmdf_kron a b. For a, b, c, e <= n:
   - E[x_a x_b] = delta_ab (pmdf_second_moment);
   - E[x_a x_b x_c x_e] = delta_ab delta_ce + delta_ac delta_be +
     delta_ae delta_bc (pmdf_fourth_moment);
   - with x_ab = x_a x_b - delta_ab (pmdf_centered),
     E[x_ab x_ce] = delta_ac delta_be + delta_ae delta_bc
     (pmdf_centered_moment).
   Each function is continuous with a polynomial bound (pmdf_regular), so it
   has the integrability domains gaussian_covariance_domain
   (pmdf_regular_domain, from gaussian_coordinate_polynomial_domain). The
   identities come from the first-order Stein identity
   gaussian_iterated_coordinate_first_stein of GaussianCoordinateStein, for
   F = x_b (degree two) and F = x_b x_c x_e (degree four). The derivatives
   come from the product rule (pmdf_derivative_nth, pmdf_derivative_mult). *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import Rstruct.
From mathcomp Require Import topology normedtype derive.
From mathcomp Require Import Rstruct_topology.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianProductDefinitions
  GaussianProduct GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateWeights GaussianCoordinateDerivativeDefinitions
  GaussianCoordinatePermutationDefinitions GaussianCoordinatePermutations
  GaussianCoordinatePolynomialContinuity GaussianCoordinateStein
  GaussianCoordinateSteinDomains GaussianCovarianceDefinitions.
Import ListNotations.
Open Scope R_scope.

(* The Kronecker delta on indices. *)
Definition pmdf_kron (i j : nat) : R := if Nat.eqb i j then 1 else 0.

Lemma pmdf_kron_sym i j : pmdf_kron i j = pmdf_kron j i.
Proof. by rewrite /pmdf_kron Nat.eqb_sym. Qed.

Lemma pmdf_kron_refl i : pmdf_kron i i = 1.
Proof. by rewrite /pmdf_kron Nat.eqb_refl. Qed.

(* Continuous with a polynomial bound. *)
Definition pmdf_regular d (F : list R -> R) : Prop :=
  finite_joint_continuous d F /\ exists C p, finite_polynomial_bound d C p F.

Lemma pmdf_regular_ext d F G :
  (forall xs, F xs = G xs) -> pmdf_regular d F -> pmdf_regular d G.
Proof. by move=> E; rewrite (functional_extensionality F G E). Qed.

Lemma pmdf_continuous_const d c : finite_joint_continuous d (fun _ => c).
Proof.
move=> z eps; exists eps => w _.
have -> : c - c = 0 by ring.
rewrite Rabs_R0; exact: cond_pos.
Qed.

Lemma pmdf_regular_const d c : pmdf_regular d (fun _ => c).
Proof.
split; first exact: pmdf_continuous_const.
by exists (Rabs c), 0%nat; exact: finite_polynomial_bound_constant.
Qed.

Lemma pmdf_regular_nth d i : (i < d)%coq_nat -> pmdf_regular d (fun xs => List.nth i xs 0).
Proof.
move=> Hi; split; first exact: finite_joint_continuous_nth.
exists (Rabs 1), 1%nat.
have [HC HB] := finite_polynomial_bound_times_coordinate d (Rabs 1) 0 (fun _ => 1) i
  (finite_polynomial_bound_constant d 1) Hi.
split => // xs Hxs.
by have := HB xs Hxs; rewrite Rmult_1_r.
Qed.

Lemma pmdf_regular_add d F G :
  pmdf_regular d F -> pmdf_regular d G -> pmdf_regular d (fun xs => F xs + G xs).
Proof.
move=> [HF [C [p BF]]] [HG [D [q BG]]]; split; first exact: finite_joint_continuous_add.
exists (C + D), (Nat.max p q).
apply: finite_polynomial_bound_add.
- exact: (finite_polynomial_bound_degree_monotone d C p _ F BF (Nat.le_max_l p q)).
- exact: (finite_polynomial_bound_degree_monotone d D q _ G BG (Nat.le_max_r p q)).
Qed.

Lemma pmdf_regular_mult d F G :
  pmdf_regular d F -> pmdf_regular d G -> pmdf_regular d (fun xs => F xs * G xs).
Proof.
move=> [HF [C [p BF]]] [HG [D [q BG]]]; split; first exact: finite_joint_continuous_mult.
by exists (C * D), (p + q)%coq_nat; exact: finite_polynomial_bound_mult.
Qed.

Lemma pmdf_regular_scale d F a : pmdf_regular d F -> pmdf_regular d (fun xs => a * F xs).
Proof.
move=> [HF [C [p BF]]]; split; first exact: finite_joint_continuous_scale.
by exists (Rabs a * C), p; exact: finite_polynomial_bound_scale.
Qed.

Arguments pmdf_regular_add {d F G}.
Arguments pmdf_regular_mult {d F G}.
Arguments pmdf_regular_scale {d F a}.

Lemma pmdf_regular_domain d F : pmdf_regular d F -> gaussian_covariance_domain d F.
Proof. by move=> [HC [C [p HB]]]; exact: (gaussian_coordinate_polynomial_domain d F C p). Qed.

Lemma pmdf_regular_integrable d F : pmdf_regular d F -> gaussian_iterated_integrable d F.
Proof. by move=> H; case: (pmdf_regular_domain d F H). Qed.

Arguments pmdf_regular_domain {d F}.
Arguments pmdf_regular_integrable {d F}.

(* Derivatives in one coordinate. *)
Lemma pmdf_derivative_nth d i j : (i < d)%coq_nat ->
  finite_coordinate_derivative d i (fun xs => List.nth j xs 0) (fun _ => pmdf_kron i j).
Proof.
move=> Hi xs Hxs; rewrite /pmdf_kron.
case: (Nat.eqb_spec i j) => [<-|Hij].
- have E : forall t, t = List.nth i (replace_coordinate i t xs) 0.
    by move=> t; rewrite (replace_coordinate_nth_same i t xs ltac:(lia)).
  exact: (is_derive_ext _ _ _ _ E (is_derive_id_R _)).
- have E : forall t, List.nth j xs 0 = List.nth j (replace_coordinate i t xs) 0.
    by move=> t; rewrite (replace_coordinate_nth_other i j t xs Hij).
  exact: (is_derive_ext _ _ _ _ E (is_derive_const _ _)).
Qed.

Lemma pmdf_derivative_mult d i F DF G DG :
  finite_coordinate_derivative d i F DF -> finite_coordinate_derivative d i G DG ->
  finite_coordinate_derivative d i (fun xs => F xs * G xs)
    (fun xs => DF xs * G xs + F xs * DG xs).
Proof.
move=> HF HG xs Hxs.
have H := is_derive_mult _ _ _ _ _ (HF xs Hxs) (HG xs Hxs).
cbv beta in H; rewrite replace_coordinate_self in H; exact: H.
Qed.

Arguments pmdf_derivative_mult {d i F DF G DG}.

(* E[x_a x_b] = delta_ab. *)
Theorem pmdf_second_moment n a b :
  (a <= n)%coq_nat -> (b <= n)%coq_nat ->
  gaussian_covariance_domain (S n) (fun xs => List.nth a xs 0 * List.nth b xs 0) /\
  gaussian_iterated_expectation (S n) (fun xs => List.nth a xs 0 * List.nth b xs 0) =
    pmdf_kron a b.
Proof.
move=> Ha Hb.
have Rb := pmdf_regular_nth (S n) b ltac:(lia).
have Rab := pmdf_regular_mult (pmdf_regular_nth (S n) a ltac:(lia)) Rb.
split; first exact: pmdf_regular_domain.
case: Rb => Cb [C [p Bb]].
have Bk := finite_polynomial_bound_constant (S n) (pmdf_kron a b).
have HS := gaussian_iterated_coordinate_first_stein n a (fun xs => List.nth b xs 0)
  (fun _ => pmdf_kron a b) C p (Rabs (pmdf_kron a b)) 0 Ha Cb (pmdf_continuous_const _ _)
  Bb Bk (pmdf_derivative_nth (S n) a b ltac:(lia)).
cbv beta in HS; rewrite -HS.
by case: (gaussian_iterated_constant (S n) (pmdf_kron a b)).
Qed.

(* E[x_a x_b x_c x_e] = delta_ab delta_ce + delta_ac delta_be
                       + delta_ae delta_bc. *)
Theorem pmdf_fourth_moment n a b c e :
  (a <= n)%coq_nat -> (b <= n)%coq_nat -> (c <= n)%coq_nat -> (e <= n)%coq_nat ->
  gaussian_covariance_domain (S n)
    (fun xs => List.nth a xs 0 * List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0) /\
  gaussian_iterated_expectation (S n)
    (fun xs => List.nth a xs 0 * List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0) =
  pmdf_kron a b * pmdf_kron c e + pmdf_kron a c * pmdf_kron b e +
  pmdf_kron a e * pmdf_kron b c.
Proof.
move=> Ha Hb Hc He.
have Ra := pmdf_regular_nth (S n) a ltac:(lia).
have Rb := pmdf_regular_nth (S n) b ltac:(lia).
have Rc := pmdf_regular_nth (S n) c ltac:(lia).
have Re := pmdf_regular_nth (S n) e ltac:(lia).
split.
  exact: pmdf_regular_domain (pmdf_regular_mult (pmdf_regular_mult
    (pmdf_regular_mult Ra Rb) Rc) Re).
pose F := fun xs : list R => List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0.
pose DF := fun xs : list R =>
  (pmdf_kron a b * List.nth c xs 0 + List.nth b xs 0 * pmdf_kron a c) * List.nth e xs 0 +
  List.nth b xs 0 * List.nth c xs 0 * pmdf_kron a e.
have HD : finite_coordinate_derivative (S n) a F DF :=
  pmdf_derivative_mult (pmdf_derivative_mult (pmdf_derivative_nth (S n) a b ltac:(lia))
    (pmdf_derivative_nth (S n) a c ltac:(lia))) (pmdf_derivative_nth (S n) a e ltac:(lia)).
have [CF [CF' [pF BF]]] : pmdf_regular (S n) F := pmdf_regular_mult (pmdf_regular_mult Rb Rc) Re.
have [CD [CD' [pD BD]]] : pmdf_regular (S n) DF.
  apply: pmdf_regular_add; last exact: pmdf_regular_mult (pmdf_regular_mult Rb Rc)
    (pmdf_regular_const _ _).
  apply: pmdf_regular_mult Re; apply: pmdf_regular_add.
  - exact: pmdf_regular_mult (pmdf_regular_const _ _) Rc.
  - exact: pmdf_regular_mult Rb (pmdf_regular_const _ _).
have HS := gaussian_iterated_coordinate_first_stein n a F DF CF' pF CD' pD Ha CF CD BF BD HD.
rewrite /F in HS; cbv beta in HS.
have -> : gaussian_iterated_expectation (S n)
    (fun xs => List.nth a xs 0 * List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0) =
  gaussian_iterated_expectation (S n)
    (fun xs => List.nth a xs 0 * (List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0)).
  by apply: gaussian_iterated_expectation_ext => xs _; ring.
rewrite -HS.
have [Dce Ece] := pmdf_second_moment n c e Hc He.
have [Dbe Ebe] := pmdf_second_moment n b e Hb He.
have [Dbc Ebc] := pmdf_second_moment n b c Hb Hc.
have [I1 E1] := gaussian_iterated_scale (S n) _ (pmdf_kron a b) (proj1 Dce).
have [I2 E2] := gaussian_iterated_scale (S n) _ (pmdf_kron a c) (proj1 Dbe).
have [I3 E3] := gaussian_iterated_scale (S n) _ (pmdf_kron a e) (proj1 Dbc).
have [I12 E12] := gaussian_iterated_add (S n) _ _ I1 I2.
have [_ E123] := gaussian_iterated_add (S n) _ _ I12 I3.
have -> : gaussian_iterated_expectation (S n) DF =
  gaussian_iterated_expectation (S n) (fun xs =>
    (pmdf_kron a b * (List.nth c xs 0 * List.nth e xs 0) +
     pmdf_kron a c * (List.nth b xs 0 * List.nth e xs 0)) +
    pmdf_kron a e * (List.nth b xs 0 * List.nth c xs 0)).
  by apply: gaussian_iterated_expectation_ext => xs _; rewrite /DF; ring.
rewrite E123 E12 E1 E2 E3 Ece Ebe Ebc; ring.
Qed.

(* The centered quadratic monomial x_a x_b - delta_ab. *)
Definition pmdf_centered a b (xs : list R) : R :=
  List.nth a xs 0 * List.nth b xs 0 - pmdf_kron a b.

Lemma pmdf_regular_centered d a b :
  (a < d)%coq_nat -> (b < d)%coq_nat -> pmdf_regular d (pmdf_centered a b).
Proof.
move=> Ha Hb; apply: (pmdf_regular_ext d (fun xs =>
  List.nth a xs 0 * List.nth b xs 0 + (-1) * pmdf_kron a b)).
  by move=> xs; rewrite /pmdf_centered; ring.
apply: pmdf_regular_add; last exact: pmdf_regular_scale (pmdf_regular_const _ _).
exact: pmdf_regular_mult (pmdf_regular_nth _ _ Ha) (pmdf_regular_nth _ _ Hb).
Qed.

(* E[(x_a x_b - delta_ab)(x_c x_e - delta_ce)]
     = delta_ac delta_be + delta_ae delta_bc. *)
Theorem pmdf_centered_moment n a b c e :
  (a <= n)%coq_nat -> (b <= n)%coq_nat -> (c <= n)%coq_nat -> (e <= n)%coq_nat ->
  gaussian_covariance_domain (S n) (fun xs => pmdf_centered a b xs * pmdf_centered c e xs) /\
  gaussian_iterated_expectation (S n) (fun xs => pmdf_centered a b xs * pmdf_centered c e xs) =
    pmdf_kron a c * pmdf_kron b e + pmdf_kron a e * pmdf_kron b c.
Proof.
move=> Ha Hb Hc He.
split.
  exact: pmdf_regular_domain (pmdf_regular_mult
    (pmdf_regular_centered (S n) a b ltac:(lia) ltac:(lia))
    (pmdf_regular_centered (S n) c e ltac:(lia) ltac:(lia))).
have [D4 E4] := pmdf_fourth_moment n a b c e Ha Hb Hc He.
have [Dab Eab] := pmdf_second_moment n a b Ha Hb.
have [Dce Ece] := pmdf_second_moment n c e Hc He.
have [I1 E1] := gaussian_iterated_scale (S n) _ (- pmdf_kron c e) (proj1 Dab).
have [I2 E2] := gaussian_iterated_scale (S n) _ (- pmdf_kron a b) (proj1 Dce).
have [I3 E3] := gaussian_iterated_constant (S n) (pmdf_kron a b * pmdf_kron c e).
have [I41 E41] := gaussian_iterated_add (S n) _ _ (proj1 D4) I1.
have [I412 E412] := gaussian_iterated_add (S n) _ _ I41 I2.
have [_ E4123] := gaussian_iterated_add (S n) _ _ I412 I3.
have -> : gaussian_iterated_expectation (S n)
    (fun xs => pmdf_centered a b xs * pmdf_centered c e xs) =
  gaussian_iterated_expectation (S n) (fun xs =>
    List.nth a xs 0 * List.nth b xs 0 * List.nth c xs 0 * List.nth e xs 0 +
    - pmdf_kron c e * (List.nth a xs 0 * List.nth b xs 0) +
    - pmdf_kron a b * (List.nth c xs 0 * List.nth e xs 0) +
    pmdf_kron a b * pmdf_kron c e).
  by apply: gaussian_iterated_expectation_ext => xs _; rewrite /pmdf_centered; ring.
rewrite E4123 E412 E41 E4 E1 E2 E3 Eab Ece; ring.
Qed.
