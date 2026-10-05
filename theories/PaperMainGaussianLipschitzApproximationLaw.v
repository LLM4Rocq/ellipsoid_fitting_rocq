(* Public-law transfer of the clipped Gaussian smoothings of a
   Euclidean-Lipschitz test F, in the form used by the limit bound for
   centered exponentials: on samples x : d.-tuple, the approximants
   A_n (tval x) are measurable and converge to F (tval x); their iterated
   Gaussian means converge to the mean of F; and these means are the
   integrals for gaussian_product_law d. The envelope is integrable for
   the public law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCoordinateDefinitions
  GaussianCoordinateWeightDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateTopology GaussianCoordinatePolynomialContinuity
  GaussianCoordinateWeights GaussianProbabilityProductDefinitions
  GaussianProbabilityProductIntegrals GaussianProbabilityProductContinuity
  PaperMainGaussianSmoothCalculus PaperMainGaussianSmoothLaw PaperMainGordonLipschitz
  PaperMainGaussianNorm PaperMainGaussianLipschitzClip
  PaperMainGaussianLipschitzSmooth PaperMainGaussianLipschitzApproximation.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

(* Stdlib sequence convergence implies MathComp convergence. *)
Lemma paper_main_gaussian_un_cv_cvg (u : nat -> R) (l : R) :
  Un_cv u l -> u @ \oo --> l.
Proof.
move=> Hu; apply/(cvgrPdist_lt (V := R^o)) => e /RltP e0.
have [N HN] := Hu e e0.
apply: filterS (nbhs_infty_ge N) => n /leP Hn.
have H := HN n Hn; rewrite /R_dist Rabs_minus_sym in H.
apply/RltP; rewrite -RabsE; exact: H.
Qed.

Definition paper_main_gaussian_approximant_random d (F : list R -> R) (n : nat) :
    d.-tuple (measurableTypeR R) -> measurableTypeR R :=
  paper_main_gaussian_smooth_random d (paper_main_gaussian_approximant d F n).

Theorem paper_main_gaussian_approximant_random_measurable d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_approximant_random d F n).
Proof.
move=> HL HLip.
exact: (paper_main_gaussian_smooth_random_measurable d _
  (paper_main_gaussian_approximant_continuous d F L n HL HLip)).
Qed.

Theorem paper_main_gaussian_lipschitz_random_measurable d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    (paper_main_gaussian_smooth_random d F).
Proof.
move=> HL HLip.
exact: (paper_main_gaussian_smooth_random_measurable d F
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)).
Qed.

Theorem paper_main_gaussian_approximant_random_cvg d F L
    (x : d.-tuple (measurableTypeR R)) :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (fun n => paper_main_gaussian_approximant_random d F n x) @ \oo -->
    paper_main_gaussian_smooth_random d F x.
Proof.
move=> HL HLip; apply: paper_main_gaussian_un_cv_cvg.
exact: (paper_main_gaussian_approximant_pointwise d F L (tval x) HL HLip (size_tuple x)).
Qed.

Theorem paper_main_gaussian_approximant_mean_cvg d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (fun n => gaussian_iterated_expectation d (paper_main_gaussian_approximant d F n))
    @ \oo --> gaussian_iterated_expectation d F.
Proof.
move=> HL HLip; apply: paper_main_gaussian_un_cv_cvg.
exact: (paper_main_gaussian_approximant_mean d F L HL HLip).
Qed.

Theorem paper_main_gaussian_lipschitz_law d F L :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> HL HLip.
exact: (paper_main_gaussian_law_transport d F _ 2
  (paper_main_gaussian_lipschitz_continuous d F L HL HLip)
  (paper_main_gaussian_lipschitz_polynomial_bound d F L HL HLip)).
Qed.

Theorem paper_main_gaussian_approximant_law d F L n :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  (gaussian_product_law d).-integrable setT
    (fun x => (paper_main_gaussian_approximant d F n (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (paper_main_gaussian_approximant d F n (tval x))%:E =
    (gaussian_iterated_expectation d (paper_main_gaussian_approximant d F n))%:E)%E.
Proof.
move=> HL HLip.
have HB : finite_polynomial_bound d (paper_main_gaussian_level n) 0
    (paper_main_gaussian_approximant d F n).
  apply (proj2 (paper_main_polynomial_zero_bound d _ _)); split.
  - exact: (Rlt_le _ _ (paper_main_gaussian_level_pos n)).
  - move=> xs _; exact: (paper_main_gaussian_approximant_bound d F L n xs HL HLip).
exact: (paper_main_gaussian_law_transport d _ _ 0
  (paper_main_gaussian_approximant_continuous d F L n HL HLip) HB).
Qed.

Definition paper_main_gaussian_envelope d (F : list R -> R) L (xs : list R) : R :=
  Rabs (F (paper_main_gaussian_zero_list d)) + L * paper_main_gaussian_norm xs +
  L * sqrt (INR d).

Lemma paper_main_gaussian_envelope_continuous d F L :
  finite_joint_continuous d (paper_main_gaussian_envelope d F L).
Proof.
rewrite /paper_main_gaussian_envelope.
apply: finite_joint_continuous_add; last exact: finite_joint_continuous_constant.
apply: finite_joint_continuous_add; first exact: finite_joint_continuous_constant.
apply: finite_joint_continuous_scale; exact: paper_main_gaussian_norm_continuous.
Qed.

Lemma paper_main_gaussian_envelope_polynomial_bound d F L :
  0 <= L ->
  finite_polynomial_bound d
    (Rabs (F (paper_main_gaussian_zero_list d)) + L * (1 + INR d) + L * sqrt (INR d)) 2
    (paper_main_gaussian_envelope d F L).
Proof.
move=> HL.
have Hd := pos_INR d.
have Hs := sqrt_pos (INR d).
have HF0 := Rabs_pos (F (paper_main_gaussian_zero_list d)).
split.
- apply: Rplus_le_le_0_compat; last exact: Rmult_le_pos.
  apply: Rplus_le_le_0_compat; first exact: HF0.
  apply: Rmult_le_pos; [exact: HL|lra].
- move=> xs Hxs.
  have [_ Hn] := paper_main_gaussian_norm_polynomial d.
  have Hnb := Hn xs Hxs.
  have Hw := gaussian_coordinate_product_weight_at_least_one 2 xs.
  have Hn0 := paper_main_gaussian_norm_nonnegative xs.
  rewrite (Rabs_pos_eq _ Hn0) in Hnb.
  rewrite /paper_main_gaussian_envelope.
  have He0 : 0 <= Rabs (F (paper_main_gaussian_zero_list d)) +
    L * paper_main_gaussian_norm xs + L * sqrt (INR d).
    apply: Rplus_le_le_0_compat; last exact: Rmult_le_pos.
    apply: Rplus_le_le_0_compat; first exact: HF0.
    exact: Rmult_le_pos.
  rewrite (Rabs_pos_eq _ He0).
  set w := gaussian_coordinate_product_weight 2 xs in Hw Hnb *.
  have H1 : Rabs (F (paper_main_gaussian_zero_list d)) <=
      Rabs (F (paper_main_gaussian_zero_list d)) * w.
    rewrite -{1}(Rmult_1_r (Rabs (F (paper_main_gaussian_zero_list d)))).
    exact: (Rmult_le_compat_l _ _ _ HF0 Hw).
  have H2 : L * paper_main_gaussian_norm xs <= L * ((1 + INR d) * w).
    exact: (Rmult_le_compat_l _ _ _ HL Hnb).
  have H3 : L * sqrt (INR d) <= L * sqrt (INR d) * w.
    rewrite -{1}(Rmult_1_r (L * sqrt (INR d))).
    exact: (Rmult_le_compat_l _ _ _ (Rmult_le_pos _ _ HL Hs) Hw).
  have Hexp : (Rabs (F (paper_main_gaussian_zero_list d)) + L * (1 + INR d) +
      L * sqrt (INR d)) * w =
    Rabs (F (paper_main_gaussian_zero_list d)) * w + L * ((1 + INR d) * w) +
      L * sqrt (INR d) * w by ring.
  rewrite Hexp; lra.
Qed.

Theorem paper_main_gaussian_envelope_law d F L :
  0 <= L ->
  (gaussian_product_law d).-integrable setT
    (fun x => (paper_main_gaussian_envelope d F L (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (paper_main_gaussian_envelope d F L (tval x))%:E =
    (gaussian_iterated_expectation d (paper_main_gaussian_envelope d F L))%:E)%E.
Proof.
move=> HL.
exact: (paper_main_gaussian_law_transport d _ _ 2
  (paper_main_gaussian_envelope_continuous d F L)
  (paper_main_gaussian_envelope_polynomial_bound d F L HL)).
Qed.

Theorem paper_main_gaussian_approximant_random_envelope d F L n
    (x : d.-tuple (measurableTypeR R)) :
  0 <= L ->
  (forall xs ys, List.length xs = d -> List.length ys = d ->
    Rabs (F xs - F ys) <= L * paper_main_gordon_distance d xs ys) ->
  Rabs (paper_main_gaussian_approximant_random d F n x) <=
    paper_main_gaussian_envelope d F L (tval x).
Proof.
move=> HL HLip.
exact: (paper_main_gaussian_approximant_envelope d F L n (tval x) HL HLip (size_tuple x)).
Qed.
