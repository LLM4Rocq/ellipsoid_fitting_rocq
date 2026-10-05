(* The finite prior is fixed before all data, with loss control on the actual feature event. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge2 SoftDefinitions GaussianCovarianceSums
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius PaperMainFeatureGramBlocks
  PaperMainFeatureLossControl PaperMainGaussianFeatureCoordinates PaperMainGordonEntropy PaperMainGordonEntropyMargin
  PaperMainLossJointNet PaperMainLossJointTransfer PaperMainLossEntropyBudget.
Open Scope R_scope.

Theorem paper_main_quadratic_prior n (T : 'M[R]_(S n) -> R -> Prop) L delta :
  0<=L -> 0<delta -> (exists A b, T A b) ->
  (forall A b, T A b -> paper_main_symmetric A /\
    paper_main_frobenius A^2<=4 /\ Rabs b<=L) ->
  exists s (A : nat -> 'M[R]_(S n)) (b : nat -> R), (0<s)%coq_nat /\
    (forall j, (j<s)%coq_nat -> T(A j)(b j)) /\
    Rpower.ln(INR s)<=paper_main_gordon_entropy_constant(delta/(L+3))*INR(S(S(paper_main_symmetric_dimension n))) /\
    forall N (x : paper_main_sample N (S n)) K,
      (0<N)%coq_nat -> (0<=K)%R ->
      paper_main_loewner_le (paper_main_feature_gram N (S n) x) (K *: 1%:M)%R ->
      K<=INR N*L^2 ->
      forall B c, T B c -> exists j, (j<s)%coq_nat /\
        Rabs(paper_main_quadratic_risk N (S n) x B c-
          paper_main_quadratic_risk N (S n) x (A j) (b j))<=4*(L+1)*delta.
Proof.
intros HL Hd HT HB.
assert (Hbound : forall A b, T A b -> paper_main_symmetric A /\
  2*paper_main_frobenius A^2+b^2<=(L+3)^2).
{ intros A b H; destruct(HB A b H) as [HS [HF Hbb]]; split; [exact HS|].
  apply paper_main_loss_joint_radius; assumption. }
destruct(paper_main_loss_joint_net n T (L+3) delta ltac:(Stdlib.micromega.Lra.lra) Hd HT Hbound)
  as [s [A [b [Hs [Hin [Hcover Hcard]]]]]].
exists s,A,b; split; [exact Hs|]; split; [exact Hin|]; split; [exact Hcard|].
intros N x K HN HK HG Hscale B c HBC.
destruct(Hcover B c HBC) as [j [Hj Hdist]].
exists j; split; [exact Hj|].
destruct(paper_main_loss_joint_distance n B (A j) c (b j) delta
  ltac:(Stdlib.micromega.Lra.lra) Hdist) as [HM Hscl].
pose proof(paper_main_feature_difference_normalized N (S n) x B (A j) K L HK HG Hscale) as HF.
pose proof(paper_main_loss_joint_risk_lipschitz n N
  (fun i A => paper_main_quadratic_form A (paper_main_point x i)-paper_main_trace A)
  B (A j) c (b j) L HN HL HF) as HR.
change (Rabs(paper_main_quadratic_risk N (S n) x B c-
  paper_main_quadratic_risk N (S n) x (A j) (b j))<=
  4*L*paper_main_frobenius(B-A j)%R+4*Rabs(c-b j)) in HR.
pose proof(Rmult_le_compat_l (4*L) _ _ ltac:(Stdlib.micromega.Lra.lra) HM).
Stdlib.micromega.Lra.nra.
Qed.

Corollary paper_main_quadratic_prior_witness n N x (T : 'M[R]_(S n) -> R -> Prop)
  s A b err a :
  (forall B c, T B c -> exists j, (j<s)%coq_nat /\
    Rabs(paper_main_quadratic_risk N (S n) x B c-
      paper_main_quadratic_risk N (S n) x (A j) (b j))<=err) ->
  (exists B c, T B c /\ paper_main_quadratic_risk N (S n) x B c<=a) ->
  exists j, (j<s)%coq_nat /\ paper_main_quadratic_risk N (S n) x (A j) (b j)<=a+err.
Proof.
intros Hcover [B [c [HT HB]]]; destruct(Hcover B c HT) as [j [Hj HD]].
exists j; split; [exact Hj|].
pose proof(Rle_abs(paper_main_quadratic_risk N (S n) x (A j) (b j)-
  paper_main_quadratic_risk N (S n) x B c)) as HA.
rewrite Rabs_minus_sym in HA; Stdlib.micromega.Lra.lra.
Qed.

Theorem paper_main_quadratic_prior_positive d (T : 'M[R]_d -> R -> Prop) L delta :
  (0<d)%coq_nat -> 0<=L -> 0<delta -> (exists A b, T A b) ->
  (forall A b, T A b -> paper_main_symmetric A /\
    paper_main_frobenius A^2<=4 /\ Rabs b<=L) ->
  exists s (A : nat -> 'M[R]_d) (b : nat -> R), (0<s)%coq_nat /\
    (forall j, (j<s)%coq_nat -> T(A j)(b j)) /\
    Rpower.ln(INR s)<=3*paper_main_gordon_entropy_constant(delta/(L+3))*(INR d)^2 /\
    forall N (x : paper_main_sample N d) K,
      (0<N)%coq_nat -> (0<=K)%R ->
      paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M)%R ->
      K<=INR N*L^2 ->
      forall B c, T B c -> exists j, (j<s)%coq_nat /\
        Rabs(paper_main_quadratic_risk N d x B c-
          paper_main_quadratic_risk N d x (A j) (b j))<=4*(L+1)*delta.
Proof.
destruct d as [|n]; [lia|].
intros Hd HL Hdelta HT HB.
destruct(paper_main_quadratic_prior n T L delta HL Hdelta HT HB)
  as [s [A [b [Hs [Hin [Hcard Hcover]]]]]].
exists s,A,b; split; [exact Hs|]; split; [exact Hin|]; split; [|exact Hcover].
assert (HE : 0<paper_main_gordon_entropy_constant(delta/(L+3))).
{ apply paper_main_gordon_entropy_constant_positive; apply Rdiv_lt_0_compat;
  Stdlib.micromega.Lra.lra. }
pose proof(Rmult_le_compat_l _ _ _ (Rlt_le _ _ HE) (paper_main_loss_joint_dimension n)).
Stdlib.micromega.Lra.nra.
Qed.
