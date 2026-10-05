(* Polynomially small conditional residual exceptions for the actual data law. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From EllipsoidFitting Require Import AnalysisBridge2 PaperMainDefinitions PaperMainAsymptotics
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainClippingLimits PaperMainResidualRates PaperMainGaussianConditionalException
  PaperMainGaussianResidualJoint PaperMainConeConditionOperator PaperMainGeometryPsd
  PaperMainConeApproxSelectorResidual PaperMainGeometryHeadWidth PaperMainGeometryHomogeneous
  PaperMainGaussianSymmetricLawPublic PaperMainGaussianFeatureCoordinates.
Import GRing.Theory Num.Theory Order.TTheory.
Open Scope R_scope.

Theorem paper_main_weighted_residual_union_tends_to_zero (p : nat -> \bar R)
    (N : nat -> nat) C kappa k :
  0 <= C -> 0 <= kappa -> (forall d, (0 <= p d)%E) ->
  (exists D, forall d, Nat.le D d -> INR (N d) <= C*(INR d)^2 /\
    (p d <= (((INR d)^k * (2*INR (N d)*exp(-INR d*(paper_main_residual_threshold kappa (INR d))^2 /
      (4+4*kappa*paper_main_residual_threshold kappa (INR d)))))%Rcoq)%:E)%E) ->
  paper_main_tends_to p 0.
Proof.
move=> HC Hk Hp [D HD].
have [K HK] := INR_unbounded ((4+4*kappa)^2).
apply: (paper_main_sqrt_polynomial_tends_to_zero p (2*C) (k+2)) => //; first lra.
exists (Nat.max D (S K)) => d Hdd.
have Hd : 0 < INR d by apply lt_0_INR; lia.
have Hlarge : (4+4*kappa)^2 <= INR d by have := le_INR K d ltac:(lia); lra.
have [HN HB] := HD d ltac:(lia).
have HE := paper_main_residual_exponential_rate kappa (INR d) Hk Hd Hlarge.
apply: (le_trans HB); rewrite lee_fin; apply/RleP.
change ((INR d)^k*(2*INR (N d)*exp(-INR d*(paper_main_residual_threshold kappa (INR d))^2 /
    (4+4*kappa*paper_main_residual_threshold kappa (INR d)))) <=
  (2*C)*(INR d)^(k+2)*exp(-sqrt(INR d)/2)).
have HM := Rmult_le_compat_l (2*INR (N d)) _ _ ltac:(have := pos_INR (N d); lra) HE.
have Hexp := exp_pos (-sqrt(INR d)/2).
have HN' := Rmult_le_compat_r (exp(-sqrt(INR d)/2)) _ _ (Rlt_le _ _ Hexp) HN.
have HB0 : 2*INR (N d)*exp(-INR d*(paper_main_residual_threshold kappa (INR d))^2 /
    (4+4*kappa*paper_main_residual_threshold kappa (INR d))) <=
    (2*C)*(INR d)^2*exp(-sqrt(INR d)/2) by nra.
have Hdk : 0 <= (INR d)^k by apply pow_le; exact: pos_INR.
have HBk := Rmult_le_compat_l ((INR d)^k) _ _ Hdk HB0.
rewrite pow_add; nra.
Qed.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Notation T := (measurableTypeR R).

Definition paper_main_residual_conditional_event D N d
    (P : D.-tuple T -> 'M[R]_d) r tau : set (paper_main_sample N d) :=
  paper_main_conditional_exception_reverse D (N*d)%N
    (paper_main_gaussian_residual_joint_set D N d P r) tau.

Theorem paper_main_residual_conditional_bound D N n
    (P : D.-tuple T -> 'M[R]_(S n)) (kappa r tau : R) :
  (forall a b, measurable_fun [set: D.-tuple T] ((fun z => P z a b) : _ -> T)) ->
  (forall z, [/\ paper_main_symmetric (P z), paper_main_pairing (P z) (P z) = 1 &
    paper_main_cone_opnorm_le (P z) (kappa / Num.sqrt (S n)%:R)]) ->
  0 <= kappa -> 0 < r -> 0 < tau ->
  measurable (paper_main_residual_conditional_event D N (S n) P r tau) /\
  (paper_main_probability N (S n) (paper_main_residual_conditional_event D N (S n) P r tau) <=
    tau^-1%:E * (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
      (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> mP HP Hk Hr Htau.
have mE := paper_main_gaussian_residual_joint_set_measurable D N (S n) P r mP.
have [_ HB] := paper_main_gaussian_residual_joint_tail_all D N n P kappa r mP HP Hk Hr.
split; first exact: paper_main_conditional_exception_reverse_measurable.
exact: paper_main_conditional_exception_reverse_bound mE Htau HB.
Qed.

Lemma paper_main_residual_conditional_good D N d
    (P : D.-tuple T -> 'M[R]_d) r tau (x : paper_main_sample N d) :
  ~ paper_main_residual_conditional_event D N d P r tau x ->
  (gaussian_product_law D (ysection (paper_main_gaussian_residual_joint_set D N d P r) x) < tau%:E)%E.
Proof.
move=> H; rewrite ltNge; apply/negP => Hge; exact: H Hge.
Qed.

Theorem paper_main_residual_conditional_tends_to_zero
    (D N : nat -> nat) (P : forall d, (D d).-tuple T -> 'M[R]_d) (C kappa : R) k :
  0 <= C -> 0 <= kappa ->
  (forall d a b, measurable_fun [set: (D d).-tuple T] ((fun z => P d z a b) : _ -> T)) ->
  (forall n z, [/\ paper_main_symmetric (P (S n) z),
    paper_main_pairing (P (S n) z) (P (S n) z) = 1 &
    paper_main_cone_opnorm_le (P (S n) z) (kappa / Num.sqrt (S n)%:R)]) ->
  (exists K, forall d, Nat.le K d -> Rle (INR (N d)) (Rmult C (pow (INR d) 2))) ->
  paper_main_tends_to
    (fun d => paper_main_probability (N d) d
      (paper_main_residual_conditional_event (D d) (N d) d (P d)
        (paper_main_residual_threshold kappa (INR d)) ((INR d)^+k)^-1)) 0.
Proof.
move=> HC Hk mP HP [K HN].
apply: (paper_main_weighted_residual_union_tends_to_zero _ N C kappa k).
- exact/RleP.
- exact/RleP.
- move=> d; exact: measure_ge0.
- exists (S K) => d Hd.
  split; first exact: (HN d ltac:(lia)).
  case: d Hd => [|n] Hd; first lia.
  have HD : Rlt 0 (INR (S n)) by apply lt_0_INR; lia.
  have HkR : Rle 0 kappa by exact/RleP.
  have [Hr _] := paper_main_residual_threshold_scale kappa (INR (S n)) HkR HD.
  have HrMC : 0 < paper_main_residual_threshold kappa (INR (S n)) by exact/RltP.
  have Htau : 0 < ((INR (S n))^+k)^-1.
  { rewrite invr_gt0 exprn_gt0 //; exact/RltP. }
  have [_ HB] := paper_main_residual_conditional_bound (D (S n)) (N (S n)) n
    (P (S n)) kappa (paper_main_residual_threshold kappa (INR (S n)))
    (((INR (S n))^+k)^-1) (mP (S n)) (HP n) Hk HrMC Htau.
  rewrite invrK -EFinM in HB.
  apply: le_trans HB _; rewrite lee_fin; apply/RleP.
  rewrite -RpowE -!RmultE.
  rewrite -(Rmult_assoc (INR (N (S n))) 2) (Rmult_comm (INR (N (S n))) 2).
  rewrite Ropp_mult_distr_l.
  exact: Rle_refl.
Qed.

Theorem paper_main_cone_selector_conditional N n (kappa eps r tau : R) :
  1 <= kappa -> 0 < eps -> 0 < r -> 0 < tau ->
  exists P : (paper_main_symmetric_dimension n).-tuple T -> 'M[R]_(S n),
    (forall a b, measurable_fun [set: (paper_main_symmetric_dimension n).-tuple T]
      ((fun z => P z a b) : _ -> T)) /\
    (forall z, paper_main_head_cone_sphere kappa (P z) /\
      paper_main_head_support (paper_main_public_symmetric_gaussian n (tval z))
        (paper_main_head_cone_sphere kappa) -
        eps*paper_main_frobenius (paper_main_public_symmetric_gaussian n (tval z)) <=
      paper_main_pairing (paper_main_public_symmetric_gaussian n (tval z)) (P z)) /\
    measurable (paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r tau) /\
    (paper_main_probability N (S n)
      (paper_main_residual_conditional_event (paper_main_symmetric_dimension n) N (S n) P r tau) <=
      tau^-1%:E * (Rmult (INR N) (Rmult 2 (exp (Rdiv (Ropp (Rmult (INR (S n)) (pow r 2)))
        (Rplus 4 (Rmult (Rmult 4 kappa) r))))))%:E)%E.
Proof.
move=> Hk He Hr Htau.
have [P [mP [HP [mE HB]]]] := paper_main_cone_selector_residual N n kappa eps r Hk He Hr.
exists P; split; first exact mP.
split; first by move=> z; case: (HP z) => H1 H2 H3; split.
have mS := paper_main_gaussian_residual_joint_set_measurable _ N (S n) P r mP.
split; first exact: paper_main_conditional_exception_reverse_measurable.
exact: paper_main_conditional_exception_reverse_bound mS Htau HB.
Qed.
