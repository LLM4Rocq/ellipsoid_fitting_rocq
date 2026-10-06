(* Comparison of products of loss factors at quadratic forms with the same
   products at Gaussian linear forms, also averaged over Gibbs replicas.
   Let T_j be symmetric matrices of size n + 1 and
   u_j(t) = paper_main_loss_factor beta (a j) t = 1 - exp (- beta l(a_j + t)).
   Compare the expectation of prod_(j in js) u_j(Q_j(x)), where
   Q_j(x) = x^T T_j x - Tr T_j for a standard Gaussian vector x of R^(n+1),
   with that of prod_(j in js) u_j(G_j(z)), where
   G_j(z) = <paper_main_projection_goe_loading n T_j, z> for a standard
   Gaussian vector z of dimension paper_main_symmetric_dimension n; the G_j
   have the same covariances as the Q_j.
   - paper_main_loss_product_comparison: if every T_j has operator norm at
     most eps and Frobenius norm at most S, the two expectations differ by
     at most paper_main_loss_replica_error beta k eps S = 2 k^2 (4 C)^k eps S,
     with k the length of js and C = paper_main_loss_factor_constant beta.
     It applies paper_main_projection_public_comparison to the smooth test
     function paper_main_loss_test_product.
   - paper_main_loss_replicated_comparison: the same bound holds after
     averaging these products over k replicas with the Gibbs weights of
     gibbs_average c f I (paper_main_loss_replica), since the Gaussian
     expectation commutes with the replica average. *)
From Stdlib Require Import Reals List Lia Lra Psatz FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix Rstruct normedtype.
From EllipsoidFitting Require Import AnalysisBridge SoftDefinitions GaussianCovarianceSums
  GaussianCovarianceLinear GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinatePolynomialContinuity
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates PaperMainGaussianSmoothCovariance
  PaperMainProjectionImage PaperMainProjectionRegular PaperMainProjectionPublic
  PaperMainProjectionPublicOperator PaperMainLossSmoothFactor PaperMainLossSmoothProduct
  PaperMainLossReplica PaperMainLossReplicaIntegral.
Open Scope R_scope.

Lemma paper_main_loss_test_image K beta a J U xs :
  (forall j, In j J -> (j<K)%coq_nat) ->
  paper_main_loss_test_product beta a J (paper_main_projection_image K U xs)=
    paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) J.
Proof.
induction J as [|j J IH]; intro HJ; [reflexivity|].
change (paper_main_loss_factor beta (a j) (List.nth j (paper_main_projection_image K U xs) 0) *
  paper_main_loss_test_product beta a J (paper_main_projection_image K U xs)=
  paper_main_loss_factor beta (a j) (U j xs)*
  paper_main_loss_product (fun i => paper_main_loss_factor beta (a i) (U i xs)) J).
rewrite (paper_main_projection_image_nth K U xs j (HJ j ltac:(left; reflexivity))).
f_equal; apply IH; intros i Hi; apply HJ; right; exact Hi.
Qed.

Lemma paper_main_loss_product_map (f : nat -> R) (g : nat -> nat) J :
  paper_main_loss_product (fun j => f(g j)) J=paper_main_loss_product f (List.map g J).
Proof. induction J; simpl; [reflexivity|rewrite IHJ; reflexivity]. Qed.

Lemma paper_main_loss_index_list (js : list nat) :
  List.map (fun j => List.nth j js 0%nat) (List.seq 0 (List.length js))=js.
Proof.
induction js as [|j js IH]; [reflexivity|].
simpl; f_equal; rewrite -seq_shift map_map; exact IH.
Qed.

Lemma paper_main_loss_list_image beta a js U xs :
  paper_main_loss_test_product beta (fun j => a(List.nth j js 0%nat))
    (List.seq 0 (List.length js))
    (paper_main_projection_image (List.length js) (fun j => U (List.nth j js 0%nat)) xs)=
  paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (U j xs)) js.
Proof.
assert (HJ : forall j, In j (List.seq 0 (List.length js)) -> (j<List.length js)%coq_nat).
{ intros j Hj; apply in_seq in Hj; lia. }
rewrite (paper_main_loss_test_image (List.length js) beta (fun j => a(List.nth j js 0%nat))
  (List.seq 0 (List.length js)) (fun j => U(List.nth j js 0%nat)) xs HJ).
rewrite (paper_main_loss_product_map (fun j => paper_main_loss_factor beta (a j) (U j xs))
  (fun j => List.nth j js 0%nat) (List.seq 0 (List.length js))).
rewrite paper_main_loss_index_list; reflexivity.
Qed.

Lemma paper_main_loss_product_regular d beta a js U : 0<=beta ->
  (forall j, In j js -> pmdf_regular d (U j)) ->
  pmdf_regular d (fun xs => paper_main_loss_product
    (fun j => paper_main_loss_factor beta (a j) (U j xs)) js).
Proof.
intros Hb HU.
pose proof(paper_main_loss_test_smooth (List.length js) beta
  (fun j => a(List.nth j js 0%nat)) (List.seq 0 (List.length js)) Hb
  ltac:(intros j Hj; apply in_seq in Hj; lia)) as HF.
destruct HF as [HC _ _ _ _ HB _ _].
pose proof(paper_main_projection_regular_image d (List.length js)
  (fun j => U(List.nth j js 0%nat)) _ _
  ltac:(intros j Hj; apply HU; apply nth_In; exact Hj) HC HB) as H.
exact(pmdf_regular_ext d _ _ (paper_main_loss_list_image beta a js U) H).
Qed.

Definition paper_main_loss_replica_error beta k eps S :=
  INR k*(INR k*(2*(4*paper_main_loss_factor_constant beta)^k*eps*S)).

Theorem paper_main_loss_product_comparison n beta a js (T : nat -> 'M[R]_(S n)) eps S :
  0<=beta -> 0<=eps -> 0<=S ->
  (forall j, In j js -> paper_main_symmetric (T j)) ->
  (forall j, In j js -> paper_main_cone_opnorm_le (T j) eps) ->
  (forall j, In j js -> paper_main_frobenius (T j)^2<=S^2) ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j) (pmdf_quad n (T j) xs)) js)-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_loss_product (fun j => paper_main_loss_factor beta (a j)
      (linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j)) xs)) js))<=
    paper_main_loss_replica_error beta (List.length js) eps S.
Proof.
intros Hb Heps HS HT HO HN.
pose proof(paper_main_loss_test_smooth (List.length js) beta
  (fun j => a(List.nth j js 0%nat)) (List.seq 0 (List.length js)) Hb
  ltac:(intros j Hj; apply in_seq in Hj; lia)) as HF.
rewrite List.length_seq in HF.
pose proof(paper_main_projection_public_comparison n (List.length js)
  (fun j => T(List.nth j js 0%nat)) _ _ _ _ eps S HF
  ltac:(intros j Hj; apply HT; apply nth_In; exact Hj)
  ltac:(intros j Hj; apply HO; apply nth_In; exact Hj)
  ltac:(intros j Hj; apply HN; apply nth_In; exact Hj) Heps HS) as H.
pose proof(functional_extensionality _ _ (paper_main_loss_list_image beta a js
  (fun j => pmdf_quad n (T j)))) as EQ.
pose proof(functional_extensionality _ _ (paper_main_loss_list_image beta a js
  (fun j => linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j))))) as EG.
rewrite EQ EG in H; exact H.
Qed.

Theorem paper_main_loss_replicated_comparison n beta c f I k a (T : nat -> 'M[R]_(S n)) eps S :
  I<>nil -> 0<=beta -> 0<=eps -> 0<=S ->
  (forall j, In j I -> paper_main_symmetric (T j)) ->
  (forall j, In j I -> paper_main_cone_opnorm_le (T j) eps) ->
  (forall j, In j I -> paper_main_frobenius (T j)^2<=S^2) ->
  Rabs(gaussian_iterated_expectation (Datatypes.S n)
    (fun xs => paper_main_loss_replica c f I k (fun js => paper_main_loss_product
      (fun j => paper_main_loss_factor beta (a j) (pmdf_quad n (T j) xs)) js))-
    gaussian_iterated_expectation (paper_main_symmetric_dimension n)
    (fun xs => paper_main_loss_replica c f I k (fun js => paper_main_loss_product
      (fun j => paper_main_loss_factor beta (a j)
        (linear_form (paper_main_symmetric_dimension n) (paper_main_projection_goe_loading n (T j)) xs)) js)))<=
    paper_main_loss_replica_error beta k eps S.
Proof.
intros HI Hb Heps HS HT HO HN.
apply paper_main_loss_replica_comparison; [exact HI| | |].
- intros js Hlen Hjs; apply pmdf_regular_integrable.
  apply paper_main_loss_product_regular; [exact Hb|].
  intros j Hj; apply pmdf_quad_regular.
- intros js Hlen Hjs; apply pmdf_regular_integrable.
  apply paper_main_loss_product_regular; [exact Hb|].
  intros j Hj; apply paper_main_projection_regular_linear.
- intros js Hlen Hjs; rewrite -Hlen; apply paper_main_loss_product_comparison;
    try assumption; intros j Hj.
  + apply HT; rewrite Forall_forall in Hjs; apply Hjs; exact Hj.
  + apply HO; rewrite Forall_forall in Hjs; apply Hjs; exact Hj.
  + apply HN; rewrite Forall_forall in Hjs; apply Hjs; exact Hj.
Qed.
