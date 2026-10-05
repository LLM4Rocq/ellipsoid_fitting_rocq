(* The one-row law bridge for the quadratic data feature: the moments of
   PaperMainDataFeatureMoments hold for the head feature of each row of an
   m-point sample, under the actual sample law.

   The sample x : paper_main_sample m N, N = n + 1, has the law
   gaussian_product_law (m * N), the measure of paper_main_probability m N.
   For i < m, row i has the coordinates List.nth (i * N + j) (tval x) 0,
   j < N (paper_main_point x i), and its feature is
   W_i = paper_main_head_feature x i = (x_i x_i^T - I) / sqrt N. With actual
   integrability:
   - E <W_i, S> = 0 (paper_main_head_feature_mean);
   - E <W_i, S><W_i, T> = N^-1 (<S, T> + <S, T^T>), and (2/N) <S, T> for
     symmetric T (paper_main_head_feature_covariance,
     paper_main_head_feature_covariance_symmetric);
   - E |W_i|_F^2 = N + 1 (paper_main_head_feature_frobenius);
   - E c_k(W_i) = 0 and E c_k(W_i) c_l(W_i) = goe_scale n ^ 2 * delta_kl in
     the goe_basis (paper_main_head_feature_coefficient_mean,
     paper_main_head_feature_coefficient_covariance).

   Proof. On lists, row i is pmdf_row N i zs = firstn N (skipn (i * N) zs).
   For G continuous with a polynomial bound in dimension N, the iterated
   expectation of zs |-> G (pmdf_row N i zs) in dimension m * N equals that
   of G (pmdf_row_moment): the blocks before and after row i integrate out
   by gaussian_block_exchange_signed (pmdf_expectation_skipn,
   pmdf_expectation_firstn). pmdf_actual transports to the actual law. One
   row at a time: joint laws of several rows are not treated here. Nothing
   from the paper is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral measurable_realfun.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianCoordinateWeightDefinitions GaussianCoordinateWeights
  GaussianCovarianceSums MaximumRadiusRegularity GaussianBlockExchange
  GaussianProbabilityProductDefinitions MatrixDefinitions TensorDefinitions GoeDefinitions
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainMatrixTransport PaperMainGaussianFeatureCoordinates
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainSymmetricBilinear
  PaperMainDataFeatureMomentsCoordinates PaperMainDataFeatureMoments.
Import GRing.Theory Num.Theory Order.TTheory.

Section RowList.
Local Open Scope R_scope.

(* Row i of a list of m rows of length N. *)
Definition pmdf_row (N i : nat) (zs : list R) : list R :=
  firstn N (skipn (i * N)%coq_nat zs).

Lemma pmdf_row_nth N i zs j : (j < N)%coq_nat ->
  List.nth j (pmdf_row N i zs) 0 = List.nth (i * N + j) zs 0.
Proof. by move=> Hj; rewrite /pmdf_row (nth_firstn_lt _ _ _ Hj) nth_skipn_add. Qed.

Lemma pmdf_bound_firstn N k C p G :
  finite_polynomial_bound N C p G ->
  finite_polynomial_bound (N + k)%coq_nat C p (fun ys => G (firstn N ys)).
Proof.
move=> [HC HB]; split => // ys Hys.
have Hf : List.length (firstn N ys) = N by rewrite length_firstn; lia.
have HW1 := gaussian_coordinate_product_weight_nonnegative p (firstn N ys).
have HW2 := gaussian_coordinate_product_weight_at_least_one p (skipn N ys).
apply: Rle_trans (HB _ Hf) _.
rewrite -{2}(firstn_skipn N ys) gaussian_coordinate_product_weight_append.
apply: Rmult_le_compat_l => //.
rewrite -{1}(Rmult_1_r (gaussian_coordinate_product_weight p (firstn N ys))).
exact: Rmult_le_compat_l.
Qed.

Lemma pmdf_bound_skipn d k C p F :
  finite_polynomial_bound k C p F ->
  finite_polynomial_bound (d + k)%coq_nat C p (fun xs => F (skipn d xs)).
Proof.
move=> [HC HB]; split => // xs Hxs.
have Hs : List.length (skipn d xs) = k by rewrite length_skipn; lia.
have HW1 := gaussian_coordinate_product_weight_nonnegative p (skipn d xs).
have HW2 := gaussian_coordinate_product_weight_at_least_one p (firstn d xs).
apply: Rle_trans (HB _ Hs) _.
rewrite -{2}(firstn_skipn d xs) gaussian_coordinate_product_weight_append.
apply: Rmult_le_compat_l => //.
rewrite -{1}(Rmult_1_r (gaussian_coordinate_product_weight p (skipn d xs))) Rmult_comm.
exact: Rmult_le_compat_r.
Qed.

Lemma pmdf_regular_firstn N k G :
  pmdf_regular N G -> pmdf_regular (N + k)%coq_nat (fun ys => G (firstn N ys)).
Proof.
move=> [HC [C [p HB]]]; split; first exact: maximum_radius_continuous_firstn.
by exists C, p; exact: pmdf_bound_firstn.
Qed.

Lemma pmdf_regular_skipn d k F :
  pmdf_regular k F -> pmdf_regular (d + k)%coq_nat (fun xs => F (skipn d xs)).
Proof.
move=> [HC [C [p HB]]]; split; first exact: maximum_radius_continuous_skipn.
by exists C, p; exact: pmdf_bound_skipn.
Qed.

Lemma pmdf_expectation_firstn N k G :
  pmdf_regular N G ->
  gaussian_iterated_expectation (N + k)%coq_nat (fun ys => G (firstn N ys)) =
  gaussian_iterated_expectation N G.
Proof.
move=> HG; have [HC [C [p HB]]] := pmdf_regular_firstn N k G HG.
rewrite (gaussian_block_exchange_signed N k _ C p HC HB).1.
apply: gaussian_iterated_expectation_ext => ws Hws.
transitivity (gaussian_iterated_expectation k (fun _ => G ws)).
  apply: gaussian_iterated_expectation_ext => us _; cbv beta.
  by rewrite firstn_app -Hws firstn_all Nat.sub_diag /= app_nil_r.
by case: (gaussian_iterated_constant k (G ws)).
Qed.

Lemma pmdf_expectation_skipn d k F :
  pmdf_regular k F ->
  gaussian_iterated_expectation (d + k)%coq_nat (fun xs => F (skipn d xs)) =
  gaussian_iterated_expectation k F.
Proof.
move=> HF; have [HC [C [p HB]]] := pmdf_regular_skipn d k F HF.
rewrite (gaussian_block_exchange_signed d k _ C p HC HB).1.
transitivity (gaussian_iterated_expectation d (fun _ => gaussian_iterated_expectation k F)).
  apply: gaussian_iterated_expectation_ext => xs Hxs.
  apply: gaussian_iterated_expectation_ext => ys _; cbv beta.
  by rewrite skipn_app -Hxs skipn_all Nat.sub_diag.
by case: (gaussian_iterated_constant d (gaussian_iterated_expectation k F)).
Qed.

(* The other rows integrate out. *)
Theorem pmdf_row_moment m N i G :
  (i < m)%coq_nat -> pmdf_regular N G ->
  pmdf_regular (m * N)%coq_nat (fun zs => G (pmdf_row N i zs)) /\
  gaussian_iterated_expectation (m * N)%coq_nat (fun zs => G (pmdf_row N i zs)) =
  gaussian_iterated_expectation N G.
Proof.
move=> Hi HG.
have Hm : Nat.add i (S (Nat.sub m (S i))) = m by lia.
have E : Nat.mul m N =
    Nat.add (Nat.mul i N) (Nat.add N (Nat.mul (Nat.sub m (S i)) N)).
  by rewrite (Nat.add_comm N) -Nat.mul_succ_l -Nat.mul_add_distr_r Hm.
rewrite E /pmdf_row; split.
  exact: pmdf_regular_skipn (pmdf_regular_firstn N (Nat.mul (Nat.sub m (S i)) N) G HG).
rewrite (pmdf_expectation_skipn (Nat.mul i N) _ _
  (pmdf_regular_firstn N (Nat.mul (Nat.sub m (S i)) N) G HG)).
exact: pmdf_expectation_firstn.
Qed.

End RowList.

Local Open Scope ring_scope.

Lemma pmdf_data_feature_ext n (f g : nat -> R) :
  (forall j : 'I_(S n), f j = g j) ->
  paper_main_data_feature n f = paper_main_data_feature n g.
Proof. by move=> H; apply/matrixP => a b; rewrite !paper_main_data_feature_entry !H. Qed.

Section RowMoments.
Variables (m n : nat).
Local Notation N := (S n).
Implicit Types (S T : 'M[R]_N).

(* The head feature of row i is the data feature of pmdf_row. *)
Lemma pmdf_head_feature_row (x : paper_main_sample m N) i :
  paper_main_head_feature x i =
  paper_main_data_feature n (fun j => List.nth j (pmdf_row N i (tval x)) 0).
Proof.
rewrite paper_main_data_feature_head; apply: pmdf_data_feature_ext => j.
have Hj : (j < N)%coq_nat by apply/ssrnat.ltP.
by rewrite (pmdf_row_nth N i (tval x) j Hj).
Qed.

Lemma pmdf_head_feature_symmetric (x : paper_main_sample m N) i :
  paper_main_symmetric (paper_main_head_feature x i).
Proof. by rewrite pmdf_head_feature_row; exact: paper_main_data_feature_symmetric. Qed.

(* Transport of a regular function of the row to the actual sample law. *)
Lemma pmdf_head_actual i (G : list R -> R) :
  (i < m)%N -> pmdf_regular N G ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N => (G (pmdf_row N i (tval x)))%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (G (pmdf_row N i (tval x)))%:E = (gaussian_iterated_expectation N G)%:E)%E.
Proof.
move=> /ssrnat.ltP Hi HG.
have [RF EF] := pmdf_row_moment m N i G Hi HG.
have [HI HE] := pmdf_actual (m * N) (fun zs => G (pmdf_row N i zs)) RF.
split; first exact: HI.
rewrite HE; congr (_%:E); exact: EF.
Qed.

Theorem paper_main_head_feature_mean i S :
  (i < m)%N ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N =>
      (paper_main_pairing (paper_main_head_feature x i) S)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_pairing (paper_main_head_feature x i) S)%:E = 0%:E)%E.
Proof.
move=> Hi.
have RG := @pmdf_regular_scale N _ (Num.sqrt N%:R)^-1 (pmdf_quad_regular n S).
have -> : (fun x : paper_main_sample m N =>
      (paper_main_pairing (paper_main_head_feature x i) S)%:E) =
    (fun x => ((Num.sqrt N%:R)^-1 * pmdf_quad n S (pmdf_row N i (tval x)))%:E).
  by apply: funext => x; rewrite pmdf_head_feature_row pmdf_pairing_quad.
have [HI HE] := pmdf_head_actual i _ Hi RG.
split; first exact: HI.
rewrite HE; congr (_%:E).
by rewrite (pmdf_scale_expectation N _ _ (pmdf_quad_regular n S)) pmdf_quad_mean mulr0.
Qed.

Theorem paper_main_head_feature_covariance i S T :
  (i < m)%N ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N =>
      (paper_main_pairing (paper_main_head_feature x i) S *
       paper_main_pairing (paper_main_head_feature x i) T)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_pairing (paper_main_head_feature x i) S *
     paper_main_pairing (paper_main_head_feature x i) T)%:E =
   ((N%:R)^-1 * (paper_main_pairing S T + paper_main_pairing S T^T))%:E)%E.
Proof.
move=> Hi.
have [Rq Eq] := pmdf_quad_covariance n S T.
have RG := @pmdf_regular_scale N _ (N%:R)^-1 Rq.
have -> : (fun x : paper_main_sample m N =>
      (paper_main_pairing (paper_main_head_feature x i) S *
       paper_main_pairing (paper_main_head_feature x i) T)%:E) =
    (fun x => ((N%:R)^-1 * (pmdf_quad n S (pmdf_row N i (tval x)) *
                            pmdf_quad n T (pmdf_row N i (tval x))))%:E).
  apply: funext => x; rewrite pmdf_head_feature_row !pmdf_pairing_quad.
  by rewrite -pmdf_sqrt_inv2; congr (_%:E); ring.
have [HI HE] := pmdf_head_actual i _ Hi RG.
split; first exact: HI.
by rewrite HE; congr (_%:E); rewrite (pmdf_scale_expectation N _ _ Rq) Eq.
Qed.

Corollary paper_main_head_feature_covariance_symmetric i S T :
  (i < m)%N -> paper_main_symmetric T ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N =>
      (paper_main_pairing (paper_main_head_feature x i) S *
       paper_main_pairing (paper_main_head_feature x i) T)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_pairing (paper_main_head_feature x i) S *
     paper_main_pairing (paper_main_head_feature x i) T)%:E =
   (2%:R / N%:R * paper_main_pairing S T)%:E)%E.
Proof.
move=> Hi HT; have HTt : T^T = T by exact/paper_main_symmetricP.
have [HI HE] := paper_main_head_feature_covariance i S T Hi.
split; first exact: HI.
by rewrite HE HTt; congr (_%:E); rewrite -mulr2n -mulr_natl; ring.
Qed.

Theorem paper_main_head_feature_frobenius i :
  (i < m)%N ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N =>
      (paper_main_frobenius (paper_main_head_feature x i) ^+ 2)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_frobenius (paper_main_head_feature x i) ^+ 2)%:E = (N%:R + 1)%:E)%E.
Proof.
move=> Hi.
have [Rs Es] := pmdf_square_moment n.
have RG := @pmdf_regular_scale N _ (N%:R)^-1 Rs.
have -> : (fun x : paper_main_sample m N =>
      (paper_main_frobenius (paper_main_head_feature x i) ^+ 2)%:E) =
    (fun x => ((N%:R)^-1 * pmdf_square n (pmdf_row N i (tval x)))%:E).
  by apply: funext => x; rewrite pmh_frobenius_sqr pmdf_head_feature_row pmdf_pairing_self.
have [HI HE] := pmdf_head_actual i _ Hi RG.
split; first exact: HI.
rewrite HE; congr (_%:E); rewrite (pmdf_scale_expectation N _ _ Rs) Es.
have HN : (N%:R : R) != 0 by rewrite pnatr_eq0.
by rewrite mulrDr (mulKf HN) (mulVf HN).
Qed.

Theorem paper_main_head_feature_coefficient_mean i k :
  (i < m)%N ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N => (paper_main_symmetric_coordinates n
      (paper_main_matrix_from_public n (paper_main_head_feature x i)) k)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_symmetric_coordinates n
      (paper_main_matrix_from_public n (paper_main_head_feature x i)) k)%:E = 0%:E)%E.
Proof.
move=> Hi.
have -> : (fun x : paper_main_sample m N => (paper_main_symmetric_coordinates n
      (paper_main_matrix_from_public n (paper_main_head_feature x i)) k)%:E) =
    (fun x => (paper_main_pairing (paper_main_head_feature x i) (pmdf_basis n k))%:E).
  apply: funext => x; rewrite pmdf_coefficient_pairing //.
  exact: pmdf_head_feature_symmetric.
exact: paper_main_head_feature_mean.
Qed.

Theorem paper_main_head_feature_coefficient_covariance i k l :
  (i < m)%N ->
  (k < paper_main_symmetric_dimension n)%N -> (l < paper_main_symmetric_dimension n)%N ->
  (gaussian_product_law (m * N)).-integrable setT
    (fun x : paper_main_sample m N =>
      (paper_main_symmetric_coordinates n
        (paper_main_matrix_from_public n (paper_main_head_feature x i)) k *
       paper_main_symmetric_coordinates n
        (paper_main_matrix_from_public n (paper_main_head_feature x i)) l)%:E) /\
  (\int[gaussian_product_law (m * N)]_x
    (paper_main_symmetric_coordinates n
      (paper_main_matrix_from_public n (paper_main_head_feature x i)) k *
     paper_main_symmetric_coordinates n
      (paper_main_matrix_from_public n (paper_main_head_feature x i)) l)%:E =
   (goe_scale n ^+ 2 * (k == l)%:R)%:E)%E.
Proof.
move=> Hi Hk Hl.
have -> : (fun x : paper_main_sample m N =>
      (paper_main_symmetric_coordinates n
        (paper_main_matrix_from_public n (paper_main_head_feature x i)) k *
       paper_main_symmetric_coordinates n
        (paper_main_matrix_from_public n (paper_main_head_feature x i)) l)%:E) =
    (fun x => (paper_main_pairing (paper_main_head_feature x i) (pmdf_basis n k) *
               paper_main_pairing (paper_main_head_feature x i) (pmdf_basis n l))%:E).
  apply: funext => x; rewrite !pmdf_coefficient_pairing //;
    exact: pmdf_head_feature_symmetric.
have [HI HE] := paper_main_head_feature_covariance_symmetric i (pmdf_basis n k)
  (pmdf_basis n l) Hi (pmdf_basis_symmetric n l).
split; first exact: HI.
by rewrite HE pmdf_basis_orthonormal // pmdf_goe_scale_sqr.
Qed.

End RowMoments.
