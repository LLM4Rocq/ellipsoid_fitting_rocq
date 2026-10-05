(* Products of bounded twice differentiable functions of the same finite
   list of coordinates. paper_main_gaussian_smooth_test d F DF D2F M 0
   says that F, with first and second partial derivatives DF and D2F, is
   continuous with continuous derivatives, and that F, DF and D2F are
   bounded by M in absolute value.
   - paper_main_loss_smooth_multiply: if F and G satisfy it with bounds M
     and N, their product, with the derivatives given by the Leibniz rule
     (paper_main_loss_product_first, paper_main_loss_product_second),
     satisfies it with the bound 4 M N.
   - paper_main_loss_test_smooth: for beta >= 0, the product
     paper_main_loss_test_product beta a J xs of the loss factors
     paper_main_loss_factor beta (a j) at the coordinates x_j, j in J, all
     below d, satisfies it with the bound (4 C)^(length J), where
     C = paper_main_loss_factor_constant beta. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From EllipsoidFitting Require Import AnalysisBridge2 GaussianCoordinateDefinitions
  GaussianCoordinateDerivativeDefinitions GaussianCoordinateTopology
  GaussianCoordinatePolynomialContinuity PaperMainGaussianSmoothCalculus
  PaperMainGaussianSmoothCovariance PaperMainLossSmoothFactor.
Open Scope R_scope.

Definition paper_main_loss_product_first (F G : list R -> R)
  (DF DG : nat -> list R -> R) (i : nat) (xs : list R) :=
  DF i xs*G xs+F xs*DG i xs.
Definition paper_main_loss_product_second (F G : list R -> R)
  (DF DG : nat -> list R -> R) (D2F D2G : nat -> nat -> list R -> R)
  (i j : nat) (xs : list R) :=
  D2F i j xs*G xs+DF i xs*DG j xs+DF j xs*DG i xs+F xs*D2G i j xs.

Lemma paper_main_loss_smooth_scalar M N x x1 x2 x12 y y1 y2 y12 :
  0 <= M -> 0 <= N ->
  Rabs x <= M -> Rabs x1 <= M -> Rabs x2 <= M -> Rabs x12 <= M ->
  Rabs y <= N -> Rabs y1 <= N -> Rabs y2 <= N -> Rabs y12 <= N ->
  Rabs(x*y) <= 4*M*N /\ Rabs(x1*y+x*y1) <= 4*M*N /\
  Rabs(x12*y+x1*y2+x2*y1+x*y12) <= 4*M*N.
Proof.
intros HM HN Hx Hx1 Hx2 Hx12 Hy Hy1 Hy2 Hy12.
assert (HB : forall a b, Rabs a <= M -> Rabs b <= N -> Rabs(a*b) <= M*N).
{ intros a b HA HB; rewrite Rabs_mult.
  apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact HA|exact HB]. }
pose proof (Rmult_le_pos M N HM HN) as Hpos.
pose proof (HB x y Hx Hy); pose proof (HB x1 y Hx1 Hy);
pose proof (HB x y1 Hx Hy1); pose proof (HB x12 y Hx12 Hy);
pose proof (HB x1 y2 Hx1 Hy2); pose proof (HB x2 y1 Hx2 Hy1);
pose proof (HB x y12 Hx Hy12).
pose proof (Rabs_triang (x1*y) (x*y1)).
pose proof (Rabs_triang (x12*y) (x1*y2)).
pose proof (Rabs_triang (x12*y+x1*y2) (x2*y1)).
pose proof (Rabs_triang (x12*y+x1*y2+x2*y1) (x*y12)).
repeat split; nra.
Qed.

Theorem paper_main_loss_smooth_multiply d F G DF DG D2F D2G M N :
  paper_main_gaussian_smooth_test d F DF D2F M 0 ->
  paper_main_gaussian_smooth_test d G DG D2G N 0 ->
  paper_main_gaussian_smooth_test d (fun xs => F xs*G xs)
    (paper_main_loss_product_first F G DF DG)
    (paper_main_loss_product_second F G DF DG D2F D2G) (4*M*N) 0.
Proof.
intros [HF HDF HDFc HD2F HD2Fc HFB HDFB HD2FB]
  [HG HDG HDGc HD2G HD2Gc HGB HDGB HD2GB].
apply paper_main_polynomial_zero_bound in HFB,HGB.
destruct HFB as [HM HFB]; destruct HGB as [HN HGB].
assert (HDFb : forall i, (i<d)%coq_nat -> forall xs, List.length xs=d -> Rabs(DF i xs)<=M).
{ intros i Hi; exact(proj2(proj1(paper_main_polynomial_zero_bound _ _ _) (HDFB i Hi))). }
assert (HDGb : forall i, (i<d)%coq_nat -> forall xs, List.length xs=d -> Rabs(DG i xs)<=N).
{ intros i Hi; exact(proj2(proj1(paper_main_polynomial_zero_bound _ _ _) (HDGB i Hi))). }
assert (HD2Fb : forall i j, (i<d)%coq_nat -> (j<d)%coq_nat -> forall xs,
  List.length xs=d -> Rabs(D2F i j xs)<=M).
{ intros i j Hi Hj; exact(proj2(proj1(paper_main_polynomial_zero_bound _ _ _) (HD2FB i j Hi Hj))). }
assert (HD2Gb : forall i j, (i<d)%coq_nat -> (j<d)%coq_nat -> forall xs,
  List.length xs=d -> Rabs(D2G i j xs)<=N).
{ intros i j Hi Hj; exact(proj2(proj1(paper_main_polynomial_zero_bound _ _ _) (HD2GB i j Hi Hj))). }
assert (HC : 0 <= 4*M*N) by nra.
assert (HZM : Rabs 0 <= M) by (rewrite Rabs_R0; exact HM).
assert (HZN : Rabs 0 <= N) by (rewrite Rabs_R0; exact HN).
constructor.
- apply finite_joint_continuous_mult; assumption.
- intros i Hi; unfold paper_main_loss_product_first.
  apply paper_main_coordinate_derivative_mult; [apply HDF|apply HDG]; exact Hi.
- intros i Hi; unfold paper_main_loss_product_first.
  apply finite_joint_continuous_add; apply finite_joint_continuous_mult;
    try assumption; [apply HDFc|apply HDGc]; exact Hi.
- intros i j Hi Hj; unfold paper_main_loss_product_first,paper_main_loss_product_second.
  apply (paper_main_coordinate_derivative_value_ext d j _
    (fun xs => (D2F i j xs*G xs+DF i xs*DG j xs)+(DF j xs*DG i xs+F xs*D2G i j xs))).
  + apply paper_main_coordinate_derivative_add; apply paper_main_coordinate_derivative_mult.
    * apply HD2F; assumption.
    * apply HDG; exact Hj.
    * apply HDF; exact Hj.
    * apply HD2G; assumption.
  + intros xs Hxs; ring.
- intros i j Hi Hj; unfold paper_main_loss_product_second.
  repeat apply finite_joint_continuous_add; apply finite_joint_continuous_mult;
    try assumption; first [apply HD2Fc|apply HD2Gc|apply HDFc|apply HDGc]; assumption.
- apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; exact(proj1(paper_main_loss_smooth_scalar M N
    (F xs) 0 0 0 (G xs) 0 0 0 HM HN (HFB xs Hxs) HZM HZM HZM (HGB xs Hxs) HZN HZN HZN)).
- intros i Hi; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; exact(proj1(proj2(paper_main_loss_smooth_scalar M N
    (F xs) (DF i xs) 0 0 (G xs) (DG i xs) 0 0 HM HN
    (HFB xs Hxs) (HDFb i Hi xs Hxs) HZM HZM (HGB xs Hxs) (HDGb i Hi xs Hxs) HZN HZN))).
- intros i j Hi Hj; apply paper_main_polynomial_zero_bound; split; [exact HC|].
  intros xs Hxs; exact(proj2(proj2(paper_main_loss_smooth_scalar M N
    (F xs) (DF i xs) (DF j xs) (D2F i j xs) (G xs) (DG i xs) (DG j xs) (D2G i j xs)
    HM HN (HFB xs Hxs) (HDFb i Hi xs Hxs) (HDFb j Hj xs Hxs) (HD2Fb i j Hi Hj xs Hxs)
    (HGB xs Hxs) (HDGb i Hi xs Hxs) (HDGb j Hj xs Hxs) (HD2Gb i j Hi Hj xs Hxs)))).
Qed.

Fixpoint paper_main_loss_test_product beta (a : nat -> R) (J : list nat) (xs : list R) : R :=
  match J with nil => 1 | j::K => paper_main_loss_coordinate (paper_main_loss_factor beta (a j)) j xs *
    paper_main_loss_test_product beta a K xs end.
Fixpoint paper_main_loss_test_first beta (a : nat -> R) (J : list nat) i (xs : list R) : R :=
  match J with nil => 0 | j::K => paper_main_loss_product_first
    (paper_main_loss_coordinate (paper_main_loss_factor beta (a j)) j)
    (paper_main_loss_test_product beta a K)
    (paper_main_loss_coordinate1 (paper_main_loss_factor1 beta (a j)) j)
    (paper_main_loss_test_first beta a K) i xs end.
Fixpoint paper_main_loss_test_second beta (a : nat -> R) (J : list nat) i k (xs : list R) : R :=
  match J with nil => 0 | j::K => paper_main_loss_product_second
    (paper_main_loss_coordinate (paper_main_loss_factor beta (a j)) j)
    (paper_main_loss_test_product beta a K)
    (paper_main_loss_coordinate1 (paper_main_loss_factor1 beta (a j)) j)
    (paper_main_loss_test_first beta a K)
    (paper_main_loss_coordinate2 (paper_main_loss_factor2 beta (a j)) j)
    (paper_main_loss_test_second beta a K) i k xs end.

Theorem paper_main_loss_test_smooth d beta a J : 0 <= beta ->
  (forall j, In j J -> (j<d)%coq_nat) ->
  paper_main_gaussian_smooth_test d (paper_main_loss_test_product beta a J)
    (paper_main_loss_test_first beta a J) (paper_main_loss_test_second beta a J)
    ((4*paper_main_loss_factor_constant beta)^List.length J) 0.
Proof.
intro Hb; induction J as [|j J IH]; intro HJ; simpl.
- constructor; try (intros; apply finite_joint_continuous_constant);
    try (intros; apply paper_main_coordinate_derivative_const).
  + apply paper_main_polynomial_zero_bound; split; [lra|intros; rewrite Rabs_R1; lra].
  + intros; apply paper_main_polynomial_zero_bound; split; [lra|intros; rewrite Rabs_R0; lra].
  + intros; apply paper_main_polynomial_zero_bound; split; [lra|intros; rewrite Rabs_R0; lra].
- apply paper_main_loss_smooth_multiply.
  + apply paper_main_loss_factor_smooth; [apply HJ; simpl; auto|exact Hb].
  + apply IH; intros k Hk; apply HJ; simpl; auto.
Qed.
