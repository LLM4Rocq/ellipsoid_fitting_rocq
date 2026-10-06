(* Bounded-row concentration under the iterated Gaussian expectation.

   Coordinates come in N rows (blocks) of p consecutive standard Gaussian
   coordinates. F : list R -> R is continuous and bounded on R^(N p), and
   replacing one whole row changes F by at most c.
   1. Scalar steps: exp (a s) <= cosh a + s sinh a for |s| <= 1 (tangent
      lines of exp), and cosh a <= exp (a^2 / 2).
   2. One row: a continuous X on R^p with |X| <= c and zero Gaussian mean
      has E exp (lambda X) <= exp (lambda^2 c^2 / 2).
   3. Rows: E exp (lambda (F - E F)) <= exp (lambda^2 N c^2 / 2), by
      induction on N, integrating the last row first. The last-row marginal
      is again continuous and bounded, has the same row oscillation, and has
      the same expectation; the conditional increment lies in [-c, c] and
      has zero mean. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From EllipsoidFitting Require Import Analysis.CalculusBridge
  GaussianDefinitions Gaussian.IteratedExpectationDefinitions
  Gaussian.IteratedExpectation Gaussian.SuffixMarginalDefinitions
  Gaussian.LastIntegration Analysis.CoordinateContinuityDefinitions
  Analysis.CoordinateTopology Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinateWeights Gaussian.CoordinateMarginals
  Gaussian.CoordinateSuffixAlgebra Gaussian.CoordinateSuffixRegularity
  Gaussian.LipschitzVariance.
Import ListNotations.
Open Scope R_scope.

(* 1. Scalar steps. *)

Lemma paper_main_concentration_exp_chord (a s : R) :
  -1 <= s <= 1 ->
  exp (a * s) <= (1 + s) / 2 * exp a + (1 - s) / 2 * exp (- a).
Proof.
intros [Hs1 Hs2].
set m := a * s.
have H1 := exp_ineq1_le (a - m).
have H2 := exp_ineq1_le (- a - m).
have E1 : exp a = exp m * exp (a - m) by rewrite -exp_plus; f_equal; ring.
have E2 : exp (- a) = exp m * exp (- a - m) by rewrite -exp_plus; f_equal; ring.
have Hm := exp_pos m.
rewrite E1 E2.
have Hw1 : 0 <= (1 + s) / 2 by lra.
have Hw2 : 0 <= (1 - s) / 2 by lra.
have K1 := Rmult_le_compat_l (exp m) _ _ (Rlt_le _ _ Hm) H1.
have K2 := Rmult_le_compat_l (exp m) _ _ (Rlt_le _ _ Hm) H2.
have K3 := Rmult_le_compat_l ((1 + s) / 2) _ _ Hw1 K1.
have K4 := Rmult_le_compat_l ((1 - s) / 2) _ _ Hw2 K2.
have Hsum : (1 + s) / 2 * (exp m * (1 + (a - m))) +
    (1 - s) / 2 * (exp m * (1 + (- a - m))) = exp m.
  rewrite /m; field.
lra.
Qed.

Lemma paper_main_concentration_tanh_step (u : R) :
  0 <= u -> exp u - exp (- u) <= u * (exp u + exp (- u)).
Proof.
intros Hu.
have H := paper_main_variance_derivative_nonnegative
  (fun t => t * (exp t + exp (- t)) - (exp t - exp (- t)))
  (fun t => t * (exp t - exp (- t))) u Hu.
have HD : forall t, @is_derive R R^o R^o t 1
    (fun t => t * (exp t + exp (- t)) - (exp t - exp (- t))) (t * (exp t - exp (- t))).
  by intros t; auto_derive; try lra; simpl; ring.
have Hsg : forall t, 0 <= t -> 0 <= t * (exp t - exp (- t)).
  intros t Ht; apply: Rmult_le_pos => //.
  case: Ht => Ht; last by rewrite -Ht Ropp_0; lra.
  by apply: Rlt_le; have := exp_increasing (- t) t ltac:(lra); lra.
specialize (H HD Hsg); simpl in H.
rewrite Ropp_0 exp_0 in H; lra.
Qed.

Lemma paper_main_concentration_cosh_bound (a : R) :
  (exp a + exp (- a)) / 2 <= exp (a ^ 2 / 2).
Proof.
have Hpos : forall u, 0 <= u -> (exp u + exp (- u)) / 2 <= exp (u ^ 2 / 2).
  intros u Hu.
  have H := paper_main_variance_derivative_nonnegative
    (fun t => - (exp (- (t ^ 2 / 2)) * (exp t + exp (- t))))
    (fun t => exp (- (t ^ 2 / 2)) * (t * (exp t + exp (- t)) - (exp t - exp (- t)))) u Hu.
  have HD : forall t, @is_derive R R^o R^o t 1
      (fun t => - (exp (- (t ^ 2 / 2)) * (exp t + exp (- t))))
      (exp (- (t ^ 2 / 2)) * (t * (exp t + exp (- t)) - (exp t - exp (- t)))).
    by intros t; auto_derive; try lra; simpl; field.
  have Hsg : forall t, 0 <= t ->
      0 <= exp (- (t ^ 2 / 2)) * (t * (exp t + exp (- t)) - (exp t - exp (- t))).
    intros t Ht; apply: Rmult_le_pos; first exact: Rlt_le (exp_pos _).
    have := paper_main_concentration_tanh_step t Ht; lra.
  specialize (H HD Hsg).
  have E0 : - (exp (- (0 ^ 2 / 2)) * (exp 0 + exp (- 0))) = -2.
    by rewrite Ropp_0 /= Rmult_0_l Rdiv_0_l Ropp_0 exp_0; ring.
  rewrite E0 in H.
  have Hq : exp (- (u ^ 2 / 2)) * exp (u ^ 2 / 2) = 1.
    by rewrite -exp_plus; replace (- (u ^ 2 / 2) + u ^ 2 / 2) with 0 by ring; rewrite exp_0.
  have He := exp_pos (u ^ 2 / 2).
  have He' := exp_pos (- (u ^ 2 / 2)).
  set E := exp (u ^ 2 / 2) in Hq He *.
  set E' := exp (- (u ^ 2 / 2)) in Hq He' H *.
  have Hc : 0 < exp u + exp (- u) by have := exp_pos u; have := exp_pos (- u); lra.
  nra.
case: (Rle_dec 0 a) => Ha; first exact: Hpos.
have := Hpos (- a) ltac:(lra).
rewrite Ropp_involutive.
have -> : (- a) ^ 2 = a ^ 2 by ring.
lra.
Qed.

(* Integrability and continuity helpers. *)

Lemma paper_main_concentration_weight0 (xs : list R) :
  gaussian_coordinate_product_weight 0 xs = 1.
Proof.
induction xs as [|x xs IH]; simpl; first reflexivity.
by rewrite IH /gaussian_coordinate_weight /=; ring.
Qed.

Lemma paper_main_concentration_integrable d (F : list R -> R) (C : R) :
  finite_joint_continuous d F -> (forall xs, length xs = d -> Rabs (F xs) <= C) ->
  gaussian_iterated_integrable d F.
Proof.
intros HF HB.
apply: (gaussian_iterated_polynomial_integrable d F C 0 HF).
split.
  have := HB (repeat 0 d) (repeat_length 0 d).
  have := Rabs_pos (F (repeat 0 d)); lra.
intros xs Hxs; rewrite paper_main_concentration_weight0 Rmult_1_r; exact: HB.
Qed.

Lemma paper_main_concentration_comp d (F : list R -> R) (g : R -> R) :
  (forall y, continuity_pt g y) -> finite_joint_continuous d F ->
  finite_joint_continuous d (fun xs => g (F xs)).
Proof.
intros Hg HF z eps.
have Hgz := Hg (F (coordinates_to_list d z)).
rewrite /continuity_pt /continue_in /limit1_in /limit_in in Hgz.
destruct (Hgz eps (cond_pos eps)) as [alp [Halp H]].
destruct (HF z (mkposreal alp Halp)) as [delta Hd].
exists delta; intros w Hw.
destruct (Req_dec (F (coordinates_to_list d w)) (F (coordinates_to_list d z))) as [He|Hne].
  by rewrite He Rminus_diag Rabs_R0; apply: cond_pos.
apply: (H (F (coordinates_to_list d w))); split.
  by split; [exact I | congruence].
exact: (Hd w Hw).
Qed.

Lemma paper_main_concentration_exp_continuous (lam m y : R) :
  continuity_pt (fun t => exp (lam * (t - m))) y.
Proof. reg. Qed.

Lemma paper_main_concentration_exp_le (x y : R) : x <= y -> exp x <= exp y.
Proof.
move=> H; case: H => [Hxy|->]; last exact: Rle_refl.
by apply: Rlt_le; apply: exp_increasing.
Qed.

(* 2. One row. *)

Lemma paper_main_concentration_one_row p (X : list R -> R) (c lam : R) :
  0 <= c -> finite_joint_continuous p X ->
  (forall ys, length ys = p -> Rabs (X ys) <= c) ->
  gaussian_iterated_expectation p X = 0 ->
  gaussian_iterated_expectation p (fun ys => exp (lam * X ys)) <=
    exp (lam ^ 2 * c ^ 2 / 2).
Proof.
move=> Hc HX HXb HX0.
have HXi := paper_main_concentration_integrable p X c HX HXb.
have HEc : finite_joint_continuous p (fun ys => exp (lam * X ys)).
  apply: (finite_joint_continuous_ext p (fun ys => exp (lam * (X ys - 0)))).
    by move=> xs _; rewrite Rminus_0_r.
  exact: (paper_main_concentration_comp p X _ (paper_main_concentration_exp_continuous lam 0) HX).
have HEb : forall ys, length ys = p -> Rabs (exp (lam * X ys)) <= exp (Rabs lam * c).
  move=> ys Hys; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := Rle_abs (lam * X ys).
  rewrite Rabs_mult in H1.
  have H2 := HXb ys Hys.
  have H3 := Rabs_pos lam.
  apply: Rle_trans H1 _.
  by apply: Rmult_le_compat_l.
have HEi := paper_main_concentration_integrable p _ _ HEc HEb.
case: (Rle_lt_or_eq_dec _ _ Hc) => Hc0; last first.
  have HX0' : forall ys, length ys = p -> exp (lam * X ys) = 1.
    move=> ys Hys; have := HXb ys Hys; rewrite -Hc0 => H.
    have -> : X ys = 0.
      have H1 := Rle_abs (X ys); have H2 := Rle_abs (- X ys); rewrite Rabs_Ropp in H2; lra.
    by rewrite Rmult_0_r exp_0.
  rewrite (gaussian_iterated_expectation_ext p _ (fun _ => 1) HX0').
  rewrite (proj2 (gaussian_iterated_constant p 1)) -Hc0.
  have -> : lam ^ 2 * 0 ^ 2 / 2 = 0 by field.
  by rewrite exp_0; lra.
set a := lam * c.
set ch := (exp a + exp (- a)) / 2.
set k := (exp a - exp (- a)) / (2 * c).
have Hpt : forall ys, length ys = p -> exp (lam * X ys) <= ch + k * X ys.
  move=> ys Hys.
  have H1 := Rle_abs (X ys); have H2 := Rle_abs (- X ys); rewrite Rabs_Ropp in H2.
  have H3 := HXb ys Hys.
  have Hs : -1 <= X ys / c <= 1.
    split.
      apply: (Rmult_le_reg_r c) => //; rewrite /Rdiv Rmult_assoc Rinv_l; lra.
    apply: (Rmult_le_reg_r c) => //; rewrite /Rdiv Rmult_assoc Rinv_l; lra.
  have := paper_main_concentration_exp_chord a (X ys / c) Hs.
  have -> : a * (X ys / c) = lam * X ys by rewrite /a; field; lra.
  have -> : (1 + X ys / c) / 2 * exp a + (1 - X ys / c) / 2 * exp (- a) = ch + k * X ys.
    by rewrite /ch /k; field; lra.
  done.
have Hci := proj1 (gaussian_iterated_constant p ch).
have Hsi := gaussian_iterated_scale p X k HXi.
have Hai := gaussian_iterated_add p (fun _ => ch) (fun ys => k * X ys) Hci (proj1 Hsi).
apply: Rle_trans (gaussian_iterated_monotone p _ _ HEi (proj1 Hai) Hpt) _.
rewrite (proj2 Hai) (proj2 Hsi) (proj2 (gaussian_iterated_constant p ch)) HX0 Rmult_0_r.
rewrite Rplus_0_r.
have := paper_main_concentration_cosh_bound a.
by have -> : a ^ 2 / 2 = lam ^ 2 * c ^ 2 / 2 by rewrite /a; field.
Qed.

(* 3. Rows. *)

Definition paper_main_row_oscillation (N p : nat) (c : R) (F : list R -> R) : Prop :=
  forall (k : nat) (a z z' b : list R), (k < N)%nat ->
    length a = (k * p)%nat -> length z = p -> length z' = p ->
    length b = ((N - S k) * p)%nat ->
    Rabs (F (a ++ z ++ b) - F (a ++ z' ++ b)) <= c.

Lemma paper_main_concentration_poly0 d (F : list R -> R) (C : R) :
  (forall xs, length xs = d -> Rabs (F xs) <= C) -> finite_polynomial_bound d C 0 F.
Proof.
intros HB; split.
  have := HB (repeat 0 d) (repeat_length 0 d); have := Rabs_pos (F (repeat 0 d)); lra.
by intros xs Hxs; rewrite paper_main_concentration_weight0 Rmult_1_r; exact: HB.
Qed.

Lemma paper_main_concentration_suffix_bound d n (F : list R -> R) (C : R) :
  finite_joint_continuous (d + n) F ->
  (forall xs, length xs = (d + n)%nat -> Rabs (F xs) <= C) ->
  forall xs, length xs = d -> Rabs (gaussian_suffix_marginal n F xs) <= C.
Proof.
intros HF HB xs Hxs.
rewrite /gaussian_suffix_marginal.
have Hc : finite_joint_continuous n (fun ys => F (xs ++ ys)).
  by apply: finite_joint_continuous_prefix; rewrite Hxs.
have Hb : forall ys, length ys = n -> Rabs (F (xs ++ ys)) <= C.
  by move=> ys Hys; apply: HB; rewrite length_app Hxs Hys.
have Hi := paper_main_concentration_integrable n _ C Hc Hb.
have HCi := proj1 (gaussian_iterated_constant n C).
have := gaussian_iterated_majorant_bound n _ _ Hi HCi Hb.
by rewrite (proj2 (gaussian_iterated_constant n C)).
Qed.

Lemma paper_main_concentration_suffix_oscillation N p (F : list R -> R) (C c : R) :
  finite_joint_continuous (N * p + p) F ->
  (forall xs, length xs = (N * p + p)%nat -> Rabs (F xs) <= C) ->
  paper_main_row_oscillation (S N) p c F ->
  paper_main_row_oscillation N p c (gaussian_suffix_marginal p F).
Proof.
intros HF HB Hosc k a z z' b Hk Ha Hz Hz' Hb.
move/ssrnat.ltP: Hk => Hk.
have Hlen : forall w, length w = p -> length (a ++ w ++ b) = (N * p)%nat.
  intros w Hw; rewrite !length_app Ha Hw Hb.
  rewrite -?multE -?minusE -?plusE; nia.
have Hcont : forall w, length w = p ->
    finite_joint_continuous p (fun ys => F ((a ++ w ++ b) ++ ys)).
  by intros w Hw; apply: finite_joint_continuous_prefix; rewrite Hlen.
have Hbnd : forall w, length w = p -> forall ys, length ys = p ->
    Rabs (F ((a ++ w ++ b) ++ ys)) <= C.
  by intros w Hw ys Hys; apply: HB; rewrite length_app Hlen // Hys.
have Hdiff : forall ys, length ys = p ->
    Rabs (F ((a ++ z ++ b) ++ ys) - F ((a ++ z' ++ b) ++ ys)) <= c.
  intros ys Hys; rewrite -!catA.
  apply: (Hosc k a z z' (b ++ ys)) => //.
    by apply/ssrnat.ltP; lia.
  rewrite length_app Hb Hys.
  rewrite -?multE -?minusE -?plusE; nia.
have HAi := paper_main_concentration_integrable p _ C (Hcont z Hz) (Hbnd z Hz).
have HBi := paper_main_concentration_integrable p _ C (Hcont z' Hz') (Hbnd z' Hz').
have Hneg := gaussian_iterated_scale p _ (-1) HBi.
have Hsub := gaussian_iterated_add p _ _ HAi (proj1 Hneg).
have HCi := proj1 (gaussian_iterated_constant p c).
have Hm := gaussian_iterated_majorant_bound p _ (fun _ => c) (proj1 Hsub) HCi.
rewrite (proj2 Hsub) (proj2 Hneg) (proj2 (gaussian_iterated_constant p c)) in Hm.
rewrite /gaussian_suffix_marginal.
have Hpt : forall xs, length xs = p ->
    Rabs (F ((a ++ z ++ b) ++ xs) + -1 * F ((a ++ z' ++ b) ++ xs)) <= c.
  move=> xs Hxs.
  have -> : F ((a ++ z ++ b) ++ xs) + -1 * F ((a ++ z' ++ b) ++ xs) =
      F ((a ++ z ++ b) ++ xs) - F ((a ++ z' ++ b) ++ xs) by ring.
  exact: Hdiff.
change (Rabs (gaussian_iterated_expectation p (fun ys => F ((a ++ z ++ b) ++ ys)) -
  gaussian_iterated_expectation p (fun ys => F ((a ++ z' ++ b) ++ ys))) <= c).
have -> : forall u v : R, u - v = u + -1 * v by move=> u v; ring.
exact: Hm Hpt.
Qed.

Theorem paper_main_concentration_rows N p (F : list R -> R) (C c lam : R) :
  0 <= c -> finite_joint_continuous (N * p) F ->
  (forall xs, length xs = (N * p)%nat -> Rabs (F xs) <= C) ->
  paper_main_row_oscillation N p c F ->
  gaussian_iterated_expectation (N * p)
    (fun xs => exp (lam * (F xs - gaussian_iterated_expectation (N * p) F))) <=
  exp (lam ^ 2 * INR N * c ^ 2 / 2).
Proof.
elim: N F C => [|N IH] F C Hc HF HB Hosc.
  rewrite /= Rmult_0_r Rmult_0_l.
  have -> : (0 / 2) = 0 by field.
  by rewrite Rminus_diag Rmult_0_r exp_0; lra.
have Hd : (N.+1 * p)%N = (N * p + p)%coq_nat by rewrite mulSnr.
rewrite Hd in HF HB *.
set F1 := gaussian_suffix_marginal p F.
have HB0 := paper_main_concentration_poly0 _ F C HB.
have HF1c : finite_joint_continuous (N * p) F1.
  exact: (gaussian_suffix_marginal_continuous (N * p) p F C 0 HF HB0).
have HF1b : forall xs, length xs = (N * p)%N -> Rabs (F1 xs) <= C.
  exact: (paper_main_concentration_suffix_bound (N * p) p F C HF HB).
have HF1o : paper_main_row_oscillation N p c F1.
  by apply: (paper_main_concentration_suffix_oscillation N p F C c).
have IH' := IH F1 C Hc HF1c HF1b HF1o.
have HM : gaussian_iterated_expectation (N * p + p)%coq_nat F =
    gaussian_iterated_expectation (N * p) F1.
  exact: gaussian_iterated_suffix_expectation.
rewrite HM.
set M := gaussian_iterated_expectation (N * p) F1 in IH' *.
rewrite gaussian_iterated_suffix_expectation.
have Hpt : forall xs, length xs = (N * p)%N ->
    gaussian_suffix_marginal p (fun xs => exp (lam * (F xs - M))) xs <=
    exp (lam ^ 2 * c ^ 2 / 2) * exp (lam * (F1 xs - M)).
  move=> xs Hxs.
  rewrite /gaussian_suffix_marginal.
  have HFc : finite_joint_continuous p (fun ys => F (xs ++ ys)).
    by apply: finite_joint_continuous_prefix; rewrite Hxs.
  have HFb : forall ys, length ys = p -> Rabs (F (xs ++ ys)) <= C.
    by move=> ys Hys; apply: HB; rewrite length_app Hxs Hys.
  have HFi := paper_main_concentration_integrable p _ C HFc HFb.
  set K := F1 xs.
  have HKdef : K = gaussian_iterated_expectation p (fun ys => F (xs ++ ys)) by [].
  set X := fun ys => F (xs ++ ys) - K.
  have HXc : finite_joint_continuous p X.
    apply: (paper_main_concentration_comp p (fun ys => F (xs ++ ys)) (fun t => t - K)) => //.
    by move=> y; reg.
  have HXb : forall ys, length ys = p -> Rabs (X ys) <= c.
    move=> ys Hys.
    have Hc' : forall ys', length ys' = p -> Rabs (F (xs ++ ys) - F (xs ++ ys')) <= c.
      move=> ys' Hys'.
      have := Hosc N xs ys ys' [::].
      rewrite !cats0; apply => //.
      by rewrite subnn.
    have HCi := proj1 (gaussian_iterated_constant p (F (xs ++ ys))).
    have Hneg := gaussian_iterated_scale p _ (-1) HFi.
    have Hsub := gaussian_iterated_add p _ _ HCi (proj1 Hneg).
    have HCc := proj1 (gaussian_iterated_constant p c).
    have Hm := gaussian_iterated_majorant_bound p _ (fun _ => c) (proj1 Hsub) HCc.
    rewrite (proj2 Hsub) (proj2 Hneg) !(proj2 (gaussian_iterated_constant p _)) in Hm.
    rewrite /X HKdef.
    have -> : forall u v : R, u - v = u + -1 * v by move=> u v; ring.
    apply: Hm => ys' Hys'.
    have -> : F (xs ++ ys) + -1 * F (xs ++ ys') = F (xs ++ ys) - F (xs ++ ys') by ring.
    exact: Hc'.
  have HX0 : gaussian_iterated_expectation p X = 0.
    have HCi := proj1 (gaussian_iterated_constant p (- K)).
    have Hadd := gaussian_iterated_add p _ _ HFi HCi.
    rewrite (gaussian_iterated_expectation_ext p X (fun ys => F (xs ++ ys) + - K)).
      by move=> ys _; rewrite /X; ring.
    by rewrite (proj2 Hadd) (proj2 (gaussian_iterated_constant p (- K))) -HKdef; ring.
  have Hrow := paper_main_concentration_one_row p X c lam Hc HXc HXb HX0.
  have HEc : finite_joint_continuous p (fun ys => exp (lam * X ys)).
    apply: (finite_joint_continuous_ext p (fun ys => exp (lam * (X ys - 0)))).
      by move=> ys _; rewrite Rminus_0_r.
    exact: (paper_main_concentration_comp p X _ (paper_main_concentration_exp_continuous lam 0) HXc).
  have HEb : forall ys, length ys = p -> Rabs (exp (lam * X ys)) <= exp (Rabs lam * c).
    move=> ys Hys; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
    apply: paper_main_concentration_exp_le.
    have H1 := Rle_abs (lam * X ys); rewrite Rabs_mult in H1.
    have H2 := HXb ys Hys; have H3 := Rabs_pos lam.
    apply: Rle_trans H1 _; by apply: Rmult_le_compat_l.
  have HEi := paper_main_concentration_integrable p _ _ HEc HEb.
  change (gaussian_iterated_expectation p (fun ys => exp (lam * (F (xs ++ ys) - M))) <=
    exp (lam ^ 2 * c ^ 2 / 2) * exp (lam * (K - M))).
  rewrite (gaussian_iterated_expectation_ext p _
    (fun ys => exp (lam * (K - M)) * exp (lam * X ys))).
    by move=> ys _; rewrite /X -exp_plus; congr exp; ring.
  rewrite (proj2 (gaussian_iterated_scale p _ _ HEi)) Rmult_comm.
  apply: Rmult_le_compat_r; first exact: Rlt_le (exp_pos _).
  exact: Hrow.
have HGc : finite_joint_continuous (N * p + p)%coq_nat (fun xs => exp (lam * (F xs - M))).
  exact: (paper_main_concentration_comp _ F _ (paper_main_concentration_exp_continuous lam M) HF).
have HGb : forall xs, length xs = (N * p + p)%coq_nat ->
    Rabs (exp (lam * (F xs - M))) <= exp (Rabs lam * (C + Rabs M)).
  move=> xs Hxs; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := Rle_abs (lam * (F xs - M)); rewrite Rabs_mult in H1.
  have H2 := HB xs Hxs; have H3 := Rabs_pos lam.
  have H4 : Rabs (F xs - M) <= C + Rabs M.
    have := Rabs_triang (F xs) (- M); rewrite Rabs_Ropp /Rminus; lra.
  apply: Rle_trans H1 _; by apply: Rmult_le_compat_l.
have HSc := gaussian_suffix_marginal_continuous (N * p) p _ _ 0 HGc
  (paper_main_concentration_poly0 _ _ _ HGb).
have HSb := paper_main_concentration_suffix_bound (N * p) p _ _ HGc HGb.
have HSi := paper_main_concentration_integrable (N * p) _ _ HSc HSb.
have HHc : finite_joint_continuous (N * p) (fun xs => exp (lam * (F1 xs - M))).
  exact: (paper_main_concentration_comp _ F1 _ (paper_main_concentration_exp_continuous lam M) HF1c).
have HHb : forall xs, length xs = (N * p)%N ->
    Rabs (exp (lam * (F1 xs - M))) <= exp (Rabs lam * (C + Rabs M)).
  move=> xs Hxs; rewrite Rabs_right; first exact: Rle_ge (Rlt_le _ _ (exp_pos _)).
  apply: paper_main_concentration_exp_le.
  have H1 := Rle_abs (lam * (F1 xs - M)); rewrite Rabs_mult in H1.
  have H2 := HF1b xs Hxs; have H3 := Rabs_pos lam.
  have H4 : Rabs (F1 xs - M) <= C + Rabs M.
    have := Rabs_triang (F1 xs) (- M); rewrite Rabs_Ropp /Rminus; lra.
  apply: Rle_trans H1 _; by apply: Rmult_le_compat_l.
have HHi := paper_main_concentration_integrable (N * p) _ _ HHc HHb.
have Hsc := gaussian_iterated_scale (N * p) _ (exp (lam ^ 2 * c ^ 2 / 2)) HHi.
apply: Rle_trans (gaussian_iterated_monotone (N * p) _ _ HSi (proj1 Hsc) Hpt) _.
rewrite (proj2 Hsc).
have -> : exp (lam ^ 2 * INR N.+1 * c ^ 2 / 2) =
    exp (lam ^ 2 * c ^ 2 / 2) * exp (lam ^ 2 * INR N * c ^ 2 / 2).
  by rewrite -exp_plus S_INR; congr exp; field.
apply: Rmult_le_compat_l; first exact: Rlt_le (exp_pos _).
exact: IH'.
Qed.
