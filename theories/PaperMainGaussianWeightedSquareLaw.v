(* Weighted centered Gaussian squares under the product law
   gaussian_product_law d. Q d a xs = sum_(i < d) a_i (x_i^2 - 1) is
   continuous, so its level sets are measurable. exp(t Q) is not
   polynomially bounded, so its law integral comes from the product
   integrals of PaperMainGaussianWeightedSquare through gpp_all_sections:
   when every 1 - 2 t a_i > 0, exp(t Q) is integrable for the law and its
   integral is the exact product. With |a_i| <= L, v = sum_(i < d) a_i^2
   and u > 0, Chernoff's inequality (MathComp chernoff) and the MGF bound
   give
     P[u <= Q] <= exp(-u^2/(4v + 4Lu)),  P[Q <= -u] <= exp(-u^2/(4v + 4Lu)),
     P[u <= Q or Q <= -u] <= 2 exp(-u^2/(4v + 4Lu)),
   whenever v + L u > 0. When every coefficient vanishes, Q = 0 and these
   events are empty. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution exp measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums GaussianFiniteSums
  GaussianCoordinateDefinitions GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianProductDefinitions GaussianProduct GaussianProbabilityProductDefinitions
  GaussianProbabilityProductIntegrals GaussianProbabilityProductContinuity
  PaperMainGaussianSmoothExponential PaperMainGaussianSmoothLaw PaperMainGaussianSmoothTail
  PaperMainGaussianGordonTail PaperMainGaussianWeightedSquare.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Continuity and measurability. *)

Lemma paper_main_weighted_square_continuous d (a : nat -> R) :
  finite_joint_continuous d (paper_main_weighted_square d a).
Proof.
rewrite /paper_main_weighted_square.
apply: (finite_joint_continuous_sum d (List.seq 0 d)
  (fun i xs => a i * (List.nth i xs 0 ^ 2 - 1))) => i Hi.
have Hi' := proj1 (List.in_seq _ _ _) Hi.
apply: finite_joint_continuous_scale.
apply: (finite_joint_continuous_ext d (fun xs => List.nth i xs 0 * List.nth i xs 0 + -1)).
  by move=> xs _; ring.
apply: finite_joint_continuous_add; last exact: finite_joint_continuous_constant.
by apply: finite_joint_continuous_mult; apply: finite_joint_continuous_nth; lia.
Qed.

Lemma paper_main_weighted_square_exp_continuous d (a : nat -> R) t :
  finite_joint_continuous d (fun xs => exp (t * paper_main_weighted_square d a xs)).
Proof.
exact: (paper_main_gaussian_exp_continuous d t _ (paper_main_weighted_square_continuous d a)).
Qed.

Theorem paper_main_weighted_square_ge_measurable d (a : nat -> R) c :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle c (paper_main_weighted_square d a (tval x))].
Proof.
exact: (paper_main_gaussian_smooth_ge_measurable d _ c
  (paper_main_weighted_square_continuous d a)).
Qed.

Theorem paper_main_weighted_square_le_measurable d (a : nat -> R) c :
  measurable [set x : d.-tuple (measurableTypeR R) |
    Rle (paper_main_weighted_square d a (tval x)) c].
Proof.
exact: (paper_main_gaussian_continuous_le_measurable d _ c
  (paper_main_weighted_square_continuous d a)).
Qed.

(* The law-level moment generating function. *)

Theorem paper_main_weighted_square_law_mgf d t (a : nat -> R) :
  (forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i) ->
  (gaussian_product_law d).-integrable setT
    (fun x => (exp (t * paper_main_weighted_square d a (tval x)))%:E) /\
  (\int[gaussian_product_law d]_x (exp (t * paper_main_weighted_square d a (tval x)))%:E =
    (paper_main_weighted_square_product d t a)%:E)%E.
Proof.
move=> Ha.
have [HI [HA HE]] := paper_main_weighted_square_mgf d t a Ha.
have Hm := proj2 (measurable_EFinP _ _)
  (gpp_joint_measurable d _ (paper_main_weighted_square_exp_continuous d a t)).
have [Hint Heq] := gpp_all_sections d _ Hm HI HA.
by split; [exact: Hint | rewrite Heq HE].
Qed.

(* Chernoff's inequality for the upper tail. *)

Theorem paper_main_weighted_square_upper_tail d (a : nat -> R) L t u :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 < t -> 2 * t * L < 1 ->
  (gaussian_product_law d [set x | Rle u (paper_main_weighted_square d a (tval x))] <=
    (exp (t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) -
      t * u))%:E)%E.
Proof.
move=> Ha Ht HtL.
have HtL' : 2 * Rabs t * L < 1 by rewrite Rabs_pos_eq; lra.
have Hpos : forall i, (i < d)%coq_nat -> 0 < 1 - 2 * t * a i.
  move=> i Hi; have HaL := Ha i Hi.
  have Hu : Rabs (2 * t * a i) <= 2 * t * L.
    rewrite !Rabs_mult (Rabs_pos_eq 2 ltac:(lra)) (Rabs_pos_eq t ltac:(lra)).
    by apply: Rmult_le_compat_l; [lra | exact HaL].
  by have := Rle_abs (2 * t * a i); lra.
have Ht' : (0 < t)%R by apply/RltP.
pose X : {RV gaussian_product_law d >-> (R : realType)} :=
  @MeasurableFun.Pack _ _ _ (R : realType)
  (fun x : d.-tuple (measurableTypeR R) => paper_main_weighted_square d a (tval x))
  (MeasurableFun.Class (isMeasurableFun.Build _ _ _ (R : realType) _
  (gpp_joint_measurable d _ (paper_main_weighted_square_continuous d a)))).
have H := chernoff X (r := t) u Ht'.
have [_ HT] := paper_main_weighted_square_law_mgf d t a Hpos.
have HM : (@mmt_gen_fun _ _ _ (gaussian_product_law d) X t =
    (paper_main_weighted_square_product d t a)%:E)%E.
  rewrite -HT /mmt_gen_fun unlock; apply: eq_integral => x _ /=.
  by rewrite RexpE mulrC.
have HB := paper_main_weighted_square_mgf_bound d a L t Ha HtL'.
have [_ [_ HE]] := paper_main_weighted_square_mgf d t a Hpos.
rewrite HE (Rabs_pos_eq t ltac:(lra)) in HB.
have Hreal : Rle (paper_main_weighted_square_product d t a * exp (- (t * u)))
    (exp (t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) - t * u)).
  have -> : t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) - t * u =
      t * t * finite_sum (fun i => a i ^ 2) (List.seq 0 d) / (1 - 2 * t * L) + - (t * u)
    by ring.
  rewrite exp_plus; apply: Rmult_le_compat_r; [apply: Rlt_le; exact: exp_pos | exact: HB].
have HS : [set x | (u <= X x)%R] =
    [set x : d.-tuple (measurableTypeR R) | Rle u (paper_main_weighted_square d a (tval x))].
  by apply/seteqP; split=> x /=; [move/RleP | move=> Hx; apply/RleP].
rewrite -HS; apply: (le_trans H).
by rewrite HM -EFinM lee_fin -RexpE; apply/RleP; exact: Hreal.
Qed.

(* The optimized one-sided tails. *)

Lemma paper_main_weighted_square_zero d (a : nat -> R) xs :
  (forall i, (i < d)%coq_nat -> a i = 0) -> paper_main_weighted_square d a xs = 0.
Proof.
move=> Hz; rewrite /paper_main_weighted_square.
transitivity (finite_sum (fun _ => 0) (List.seq 0 d)); last exact: finite_sum_zero.
apply: finite_sum_ext => i Hi; have Hi' := proj1 (List.in_seq _ _ _) Hi.
by rewrite (Hz i ltac:(lia)); ring.
Qed.

Lemma paper_main_weighted_square_variance_zero d (a : nat -> R) :
  finite_sum (fun i => a i ^ 2) (List.seq 0 d) = 0 -> forall i, (i < d)%coq_nat -> a i = 0.
Proof.
move=> H0 i Hi.
have Hnn : forall k, In k (List.seq 0 d) -> 0 <= a k ^ 2 by move=> k _; apply: pow2_ge_0.
have Hle : a i ^ 2 <= finite_sum (fun k => a k ^ 2) (List.seq 0 d).
  apply: (finite_sum_member (fun k => a k ^ 2) (List.seq 0 d) i); last by apply/List.in_seq; lia.
  exact: Hnn.
rewrite H0 in Hle; have := pow2_ge_0 (a i); nra.
Qed.

Theorem paper_main_weighted_square_upper_tail_quadratic d (a : nat -> R) L u :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d [set x | Rle u (paper_main_weighted_square d a (tval x))] <=
    (exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> Ha HL Hu Hden.
set v := finite_sum (fun i => a i ^ 2) (List.seq 0 d).
have Hv0 : 0 <= v by apply: finite_sum_nonneg => i _; apply: pow2_ge_0.
case: (Req_dec v 0) => Hv.
  have Hz := paper_main_weighted_square_variance_zero d a Hv.
  have -> : [set x : d.-tuple (measurableTypeR R) |
      Rle u (paper_main_weighted_square d a (tval x))] = set0.
    apply/seteqP; split=> x //=.
    by rewrite (paper_main_weighted_square_zero d a (tval x) Hz); lra.
  by rewrite measure0 lee_fin; apply/RleP; apply: Rlt_le; exact: exp_pos.
have Hvp : 0 < v by lra.
pose t := u / (2 * (v + L * u)).
have Hden' : 0 < v + L * u by exact: Hden.
have Ht : 0 < t by rewrite /t; apply: Rdiv_lt_0_compat; lra.
have HtL : 2 * t * L < 1.
  rewrite /t; apply: (Rmult_lt_reg_r (v + L * u)); first lra.
  have -> : 2 * (u / (2 * (v + L * u))) * L * (v + L * u) = L * u by field; lra.
  lra.
have H := paper_main_weighted_square_upper_tail d a L t u Ha Ht HtL.
have Hexp : t * t * v / (1 - 2 * t * L) - t * u = - u ^ 2 / (4 * v + 4 * L * u).
  rewrite /t; field.
  split; [lra | split; [lra | nra]].
rewrite -Hexp.
exact: H.
Qed.

Lemma paper_main_weighted_square_neg d (a : nat -> R) xs :
  paper_main_weighted_square d (fun i => - a i) xs = - paper_main_weighted_square d a xs.
Proof.
rewrite /paper_main_weighted_square -finite_sum_opp.
by apply: finite_sum_ext => i _; ring.
Qed.

Theorem paper_main_weighted_square_lower_tail_quadratic d (a : nat -> R) L u :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d [set x | Rle (paper_main_weighted_square d a (tval x)) (- u)] <=
    (exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> Ha HL Hu Hden.
have Ha' : forall i, (i < d)%coq_nat -> Rabs (- a i) <= L.
  by move=> i Hi; rewrite Rabs_Ropp; exact: Ha.
have Hv : finite_sum (fun i => (- a i) ^ 2) (List.seq 0 d) =
    finite_sum (fun i => a i ^ 2) (List.seq 0 d).
  by apply: finite_sum_ext => i _; ring.
have H := paper_main_weighted_square_upper_tail_quadratic d (fun i => - a i) L u Ha' HL Hu
  (ltac:(rewrite Hv; exact Hden)).
rewrite Hv in H.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle (paper_main_weighted_square d a (tval x)) (- u)] =
  [set x | Rle u (paper_main_weighted_square d (fun i => - a i) (tval x))].
  apply/seteqP; split=> x /=; rewrite paper_main_weighted_square_neg; lra.
by rewrite HS.
Qed.

(* The two-sided tail. *)

Theorem paper_main_weighted_square_two_sided_tail d (a : nat -> R) L u :
  (forall i, (i < d)%coq_nat -> Rabs (a i) <= L) -> 0 <= L -> 0 < u ->
  0 < finite_sum (fun i => a i ^ 2) (List.seq 0 d) + L * u ->
  (gaussian_product_law d [set x | Rle u (Rabs (paper_main_weighted_square d a (tval x)))] <=
    (2 * exp (- u ^ 2 / (4 * finite_sum (fun i => a i ^ 2) (List.seq 0 d) + 4 * L * u)))%:E)%E.
Proof.
move=> Ha HL Hu Hden.
have HS : [set x : d.-tuple (measurableTypeR R) |
    Rle u (Rabs (paper_main_weighted_square d a (tval x)))] =
  [set x | Rle u (paper_main_weighted_square d a (tval x))] `|`
  [set x | Rle (paper_main_weighted_square d a (tval x)) (- u)].
  apply/seteqP; split=> x /=.
  - move=> Hx.
    case: (Rle_lt_dec 0 (paper_main_weighted_square d a (tval x))) => Hs.
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
apply: (le_trans (measureU2 _ (paper_main_weighted_square_ge_measurable d a u)
  (paper_main_weighted_square_le_measurable d a (- u)))).
have H1 := paper_main_weighted_square_upper_tail_quadratic d a L u Ha HL Hu Hden.
have H2 := paper_main_weighted_square_lower_tail_quadratic d a L u Ha HL Hu Hden.
have E2 : forall z : R, ((2 * z)%:E = z%:E + z%:E)%E.
  move=> z; rewrite -EFinD; congr (_%:E).
  by change (2 * z = z + z); ring.
rewrite E2.
exact: (leeD H1 H2).
Qed.

(* The threshold form: for s > 0 and v > 0, Q exceeds 2 sqrt(v s) + 2 L s,
   or falls below its negative, with probability at most exp(-s) each. *)
