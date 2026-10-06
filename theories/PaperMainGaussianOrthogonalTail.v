(* Tails of a weighted centered Gaussian square after a loading with
   orthonormal rows, under the original law gaussian_product_law d.
   Write O x = gaussian_covariance_image d d O x and
   Q d a xs = sum_(i < d) a_i (x_i^2 - 1), with coefficients of either sign.
   The map x |-> Q d a (O x) is continuous, so its level sets are
   measurable. The exponential exp (t Q) is not polynomially bounded, so
   the covariance identity is never applied to it. Instead, for e > 0 the
   bounded C2 test psi(Q) of PaperMainGaussianOrthogonalCutoff majorizes the
   indicator of [u <= Q] and is at most (1 + e) exp (t (Q - u)). Markov's
   inequality, the orthogonal invariance of E psi(Q), and e -> 0 in a real
   inequality give the Chernoff bound
     P[u <= Q(O x)] <= exp (- t u) E_d exp (t Q)
   for 0 < t and 2 t L < 1, where |a_i| <= L. With the exact moment
   generating function of PaperMainGaussianWeightedSquare this gives the
   same tails as for Q itself: for v = sum_(i < d) a_i^2, 0 < u and
   0 < v + L u,
     P[u <= Q(O x)] <= exp (- u^2 / (4 v + 4 L u)),
     P[Q(O x) <= - u] <= exp (- u^2 / (4 v + 4 L u)),
     P[u <= |Q(O x)|] <= 2 exp (- u^2 / (4 v + 4 L u)),
   and for 0 < s, 0 < v the threshold forms with 2 sqrt (v s) + 2 L s and
   failure exp (- s), 2 exp (- s). When every coefficient vanishes (in
   particular d = 0) the events are empty for u > 0. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianFiniteSums
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions
  GaussianCoordinateTopology GaussianCoordinateSteinDomains
  GaussianCoordinatePolynomialContinuity
  GaussianProductDefinitions GaussianProduct GaussianProbabilityProductDefinitions
  GaussianProbabilityProductIntegrals GaussianProbabilityProductContinuity
  GaussianCovarianceDefinitions
  PaperMainGaussianSmoothCovariance PaperMainGaussianSmoothLaw PaperMainGaussianSmoothTail
  PaperMainGaussianGordonTail PaperMainGaussianWeightedSquare
  PaperMainGaussianWeightedSquareLaw PaperMainGaussianOrthogonal
  PaperMainGaussianOrthogonalLaw PaperMainGaussianOrthogonalCutoff.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Continuity and measurability. *)

Lemma paper_main_gaussian_orthogonal_square_continuous d O (a : nat -> R) :
  finite_joint_continuous d
    (fun xs => paper_main_weighted_square d a (gaussian_covariance_image d d O xs)).
Proof.
exact: (paper_main_gaussian_orthogonal_continuous d O _
  (paper_main_weighted_square_continuous d a)).
Qed.

Theorem paper_main_gaussian_orthogonal_square_ge_measurable d O (a : nat -> R) c :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle c (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))].
Proof.
exact: (paper_main_gaussian_orthogonal_ge_measurable d O _ c
  (paper_main_weighted_square_continuous d a)).
Qed.

Theorem paper_main_gaussian_orthogonal_square_le_measurable d O (a : nat -> R) c :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x))) c].
Proof.
exact: (paper_main_gaussian_orthogonal_le_measurable d O _ c
  (paper_main_weighted_square_continuous d a)).
Qed.

(* Markov's inequality for a continuous, polynomially bounded majorant. *)

Lemma paper_main_gaussian_orthogonal_markov d (A : set (d.-tuple (measurableTypeR R)))
    (G : list R -> R) C r :
  measurable A -> finite_joint_continuous d G -> finite_polynomial_bound d C r G ->
  (forall x : d.-tuple (measurableTypeR R), A x -> 1 <= G (tval x)) ->
  (forall x : d.-tuple (measurableTypeR R), 0 <= G (tval x)) ->
  (gaussian_product_law d A <= (gaussian_iterated_expectation d G)%:E)%E.
Proof.
move=> mA Hc Hb H1 H0.
have [HI HE] := paper_main_gaussian_law_transport d G C r Hc Hb.
have HIA := integrable_indic (gaussian_product_law d) mA.
have eA := integral_indic (gaussian_product_law d) measurableT mA.
rewrite setIT in eA.
rewrite -eA -HE.
apply: (le_integral measurableT HIA HI) => x _.
rewrite /numfun.indic lee_fin; case: (boolP (x \in A)) => Hx; apply/RleP.
- by move: Hx; rewrite inE => Hx; exact: (H1 x Hx).
- exact: (H0 x).
Qed.

(* The smoothed Chernoff bound, then e -> 0. *)

Lemma paper_main_gaussian_orthogonal_square_smooth_bound d O (a : nat -> R) L t u e :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < t ->
  2 * t * L < 1 -> 0 < e ->
  (gaussian_product_law d
    [set x | Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))]
    <= ((1 + e) * exp (- (t * u)) *
      gaussian_iterated_expectation d (fun xs => exp (t * paper_main_weighted_square d a xs)))%:E)%E.
Proof.
move=> HO Ha HL Ht HtL He.
have Hs := paper_main_gaussian_orthogonal_test_smooth d a L t u e He (Rlt_le _ _ Ht) HL Ha.
have Hs' := Hs; case: Hs' => Hc _ _ _ _ Hb _ _.
have [C' [HcO HbO]] := paper_main_gaussian_orthogonal_regular d O
  (paper_main_gaussian_orthogonal_test d a t u e) _ 2 Hc Hb.
have Hpos : forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i.
  move=> i Hi; have HaL := Ha i Hi.
  have Hu : Rabs (2 * t * a i) <= 2 * t * L.
    rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)) (Rabs_pos_eq t ltac:(lra)).
    by apply: Rmult_le_compat_l; [lra | exact HaL].
  by have := Rle_abs (2 * t * a i); lra.
have [HIexp _] := paper_main_weighted_square_mgf d t a Hpos.
have [HIc HEc] := gaussian_iterated_scale d
  (fun xs => exp (t * paper_main_weighted_square d a xs)) ((1 + e) * exp (- (t * u))) HIexp.
have [HIf _] := gaussian_coordinate_polynomial_domain d _ _ _ Hc Hb.
have H1 : forall x : d.-tuple (measurableTypeR R),
    [set x | Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))]
      x ->
    1 <= paper_main_gaussian_orthogonal_test d a t u e (gaussian_covariance_image d d O (tval x)).
  move=> x Hx.
  exact: (paper_main_gaussian_orthogonal_test_ge1 d a t u e _ He (Rlt_le _ _ Ht) Hx).
have H0 : forall x : d.-tuple (measurableTypeR R),
    0 <= paper_main_gaussian_orthogonal_test d a t u e (gaussian_covariance_image d d O (tval x)).
  move=> x; exact: (paper_main_gaussian_orthogonal_test_nonneg d a t u e _ He).
apply: (le_trans (paper_main_gaussian_orthogonal_markov d _ _ C' (2 * d)%coq_nat
  (paper_main_gaussian_orthogonal_square_ge_measurable d O a u) HcO HbO H1 H0)).
rewrite (paper_main_gaussian_orthogonal_smooth_expectation d O _ _ _ _ _ HO Hs).
have Hle := gaussian_iterated_monotone d _ _ HIf HIc
  (fun xs _ => paper_main_gaussian_orthogonal_test_exp_bound d a t u e xs He).
rewrite HEc in Hle.
by rewrite lee_fin; apply/RleP; exact: Hle.
Qed.

Lemma paper_main_gaussian_orthogonal_epsilon_limit (p : \bar R) K :
  0 <= K -> (forall e, 0 < e -> (p <= ((1 + e) * K)%:E)%E) -> (p <= K%:E)%E.
Proof.
move=> HK Hp.
apply/lee_addgt0Pr => eps Heps.
have Heps' : 0 < eps by apply/RltP.
have He : 0 < eps / (K + 1) by apply: Rdiv_lt_0_compat; lra.
apply: (le_trans (Hp _ He)).
rewrite -EFinD lee_fin; apply/RleP.
have Hfrac : eps / (K + 1) * K <= eps.
  apply: (Rmult_le_reg_r (K + 1)); first lra.
  have -> : eps / (K + 1) * K * (K + 1) = eps * K by field; lra.
  nra.
change ((1 + eps / (K + 1)) * K <= K + eps); nra.
Qed.

Theorem paper_main_gaussian_orthogonal_square_chernoff d O (a : nat -> R) L t u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < t -> 2 * t * L < 1 ->
  (gaussian_product_law d
    [set x | Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))]
    <= (exp (- (t * u)) *
      gaussian_iterated_expectation d (fun xs => exp (t * paper_main_weighted_square d a xs)))%:E)%E.
Proof.
move=> HO Ha HL Ht HtL.
have Hpos : forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i.
  move=> i Hi; have HaL := Ha i Hi.
  have Hu : Rabs (2 * t * a i) <= 2 * t * L.
    rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)) (Rabs_pos_eq t ltac:(lra)).
    by apply: Rmult_le_compat_l; [lra | exact HaL].
  by have := Rle_abs (2 * t * a i); lra.
have [HIexp _] := paper_main_weighted_square_mgf d t a Hpos.
have HE0 : 0 <= gaussian_iterated_expectation d
    (fun xs => exp (t * paper_main_weighted_square d a xs)).
  apply: (gaussian_iterated_nonnegative d _ HIexp) => xs _.
  apply: Rlt_le; exact: exp_pos.
apply: paper_main_gaussian_orthogonal_epsilon_limit.
  by apply: Rmult_le_pos; [apply: Rlt_le; exact: exp_pos | exact: HE0].
move=> e He.
apply: (le_trans (paper_main_gaussian_orthogonal_square_smooth_bound d O a L t u e
  HO Ha HL Ht HtL He)).
set E := gaussian_iterated_expectation d (fun xs => exp (t * paper_main_weighted_square d a xs)).
rewrite lee_fin; apply/RleP.
change ((1 + e) * exp (- (t * u)) * E <= (1 + e) * (exp (- (t * u)) * E)).
rewrite Rmult_assoc; exact: Rle_refl.
Qed.

Theorem paper_main_gaussian_orthogonal_square_upper_tail d O (a : nat -> R) L t u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < t -> 2 * t * L < 1 ->
  (gaussian_product_law d
    [set x | Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))]
    <= (exp (t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) -
      t * u))%:E)%E.
Proof.
move=> HO Ha HL Ht HtL.
apply: (le_trans (paper_main_gaussian_orthogonal_square_chernoff d O a L t u HO Ha HL Ht HtL)).
have HtL' : 2 * Rabs t * L < 1 by rewrite Rabs_pos_eq; lra.
have HB := paper_main_weighted_square_mgf_bound d a L t Ha HtL'.
rewrite (Rabs_pos_eq t ltac:(lra)) in HB.
rewrite lee_fin; apply/RleP.
have -> : t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) - t * u =
    - (t * u) + t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L)
  by ring.
rewrite exp_plus; apply: Rmult_le_compat_l; [apply: Rlt_le; exact: exp_pos | exact: HB].
Qed.

(* Optimization in t, for any bound of the Chernoff form. *)

Lemma paper_main_gaussian_orthogonal_chernoff_quadratic (p : \bar R) v L u :
  0 <= L -> 0 < u -> 0 < v ->
  (forall t, 0 < t -> 2 * t * L < 1 ->
    (p <= (exp (t * t * v / (1 - 2 * t * L) - t * u))%:E)%E) ->
  (p <= (exp (- u ^ 2 / (4 * v + 4 * L * u)))%:E)%E.
Proof.
move=> HL Hu Hv H.
have Hden : 0 < v + L * u by nra.
pose t := u / (2 * (v + L * u)).
have Ht : 0 < t by rewrite /t; apply: Rdiv_lt_0_compat; lra.
have HtL : 2 * t * L < 1.
  rewrite /t; apply: (Rmult_lt_reg_r (v + L * u)); first lra.
  have -> : 2 * (u / (2 * (v + L * u))) * L * (v + L * u) = L * u by field; lra.
  lra.
have Hexp : t * t * v / (1 - 2 * t * L) - t * u = - u ^ 2 / (4 * v + 4 * L * u).
  rewrite /t; field.
  split; [lra | split; [lra | nra]].
rewrite -Hexp.
exact: (H t Ht HtL).
Qed.

(* The transported one-sided, two-sided and threshold tails. *)

Theorem paper_main_gaussian_orthogonal_square_upper_tail_quadratic d O (a : nat -> R) L u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d
    [set x | Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))]
    <= (exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> HO Ha HL Hu Hden.
set v := finite_sum (fun i => a i ^ 2) (List.seq 0 d).
have Hv0 : 0 <= v by apply: finite_sum_nonneg => i _; apply: pow2_ge_0.
case: (Req_dec v 0) => Hv.
  have Hz := paper_main_weighted_square_variance_zero d a Hv.
  have -> : [set x : d.-tuple (measurableTypeR R) |
      Rle u (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)))] = set0.
    apply/seteqP; split=> x //=.
    by rewrite (paper_main_weighted_square_zero d a _ Hz); lra.
  by rewrite measure0 lee_fin; apply/RleP; apply: Rlt_le; exact: exp_pos.
apply: (paper_main_gaussian_orthogonal_chernoff_quadratic _ v L u HL Hu ltac:(lra)).
move=> t Ht HtL.
exact: (paper_main_gaussian_orthogonal_square_upper_tail d O a L t u HO Ha HL Ht HtL).
Qed.

Theorem paper_main_gaussian_orthogonal_square_lower_tail_quadratic d O (a : nat -> R) L u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d
    [set x | Rle (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x))) (- u)]
    <= (exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> HO Ha HL Hu Hden.
have Ha' : forall i, (i < d)%coq_nat -> Rabs (- a i) <= L.
  by move=> i Hi; rewrite Rabs_Ropp; exact: Ha.
have Hv : finite_sum (fun i => (- a i) ^ 2) (List.seq 0 d) =
    finite_sum (fun i => a i ^ 2) (List.seq 0 d).
  by apply: finite_sum_ext => i _; ring.
have H := paper_main_gaussian_orthogonal_square_upper_tail_quadratic d O (fun i => - a i)
  L u HO Ha' HL Hu (ltac:(rewrite Hv; exact Hden)).
rewrite Hv in H.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle (paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x))) (- u)] =
  [set x | Rle u (paper_main_weighted_square d (fun i => - a i)
    (gaussian_covariance_image d d O (tval x)))].
  apply/seteqP; split=> x /=; rewrite paper_main_weighted_square_neg; lra.
by rewrite HS.
Qed.

Theorem paper_main_gaussian_orthogonal_square_two_sided_tail d O (a : nat -> R) L u :
  paper_main_gaussian_orthonormal_rows d O ->
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d
    [set x | Rle u (Rabs (paper_main_weighted_square d a
      (gaussian_covariance_image d d O (tval x))))]
    <= (2 * exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) +
      4 * L * u)))%:E)%E.
Proof.
move=> HO Ha HL Hu Hden.
set q := fun x : d.-tuple (measurableTypeR R) =>
  paper_main_weighted_square d a (gaussian_covariance_image d d O (tval x)).
have HS : [set x : d.-tuple (measurableTypeR R) | Rle u (Rabs (q x))] =
  [set x | Rle u (q x)] `|` [set x | Rle (q x) (- u)].
  apply/seteqP; split=> x /=.
  - move=> Hx.
    case: (Rle_lt_dec 0 (q x)) => Hs.
      by left; rewrite (Rabs_pos_eq _ Hs) in Hx.
    right; rewrite (Rabs_left _ Hs) in Hx.
    have H := Ropp_le_contravar _ _ Hx.
    by rewrite Ropp_involutive in H.
  - case=> Hx'.
      by apply: (Rle_trans _ _ _ Hx'); exact: Rle_abs.
    have Hnu : - u < 0 by lra.
    have Hneg := Rle_lt_trans _ _ _ Hx' Hnu.
    rewrite (Rabs_left _ Hneg).
    have H := Ropp_le_contravar _ _ Hx'.
    by rewrite Ropp_involutive in H.
rewrite HS.
apply: (le_trans (measureU2 _ (paper_main_gaussian_orthogonal_square_ge_measurable d O a u)
  (paper_main_gaussian_orthogonal_square_le_measurable d O a (- u)))).
have H1 := paper_main_gaussian_orthogonal_square_upper_tail_quadratic d O a L u HO Ha HL Hu Hden.
have H2 := paper_main_gaussian_orthogonal_square_lower_tail_quadratic d O a L u HO Ha HL Hu Hden.
have E2 : forall z : R, ((2 * z)%:E = z%:E + z%:E)%E.
  move=> z; rewrite -EFinD; congr (_%:E).
  by change (2 * z = z + z); ring.
rewrite E2.
exact: (leeD H1 H2).
Qed.
