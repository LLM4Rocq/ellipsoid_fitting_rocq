(* Soft minimax of clipped data-feature scores (G11).
   For finite index lists Y and Q, with a symmetric public B(z, q) of internal
   operator norm at most k and a dual vector y(z, q) of Euclidean norm at most 1
   on seq 0 N for every z in Y and q in Q, the soft minimax of the clipped
   scores is 2 k U-Lipschitz in paper_main_gordon_distance (N * d), d = S n.
   This instantiates the checked PaperMainSoftLipschitz results with
   paper_main_data_clipped_score_lipschitz. The Gaussian statements are on
   gaussian_product_law (N * d), exactly as in PaperMainSoftLipschitz. No other
   law, tail or concentration statement is assumed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral measurable_realfun.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  GaussianCoordinateDefinitions GaussianProductDefinitions
  GaussianProbabilityProductDefinitions OperatorDefinitions PaperMainDefinitions
  PaperMainMatrixTransport PaperMainGordonLipschitz PaperMainDataClipped
  PaperMainSoftLipschitz.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Import ListNotations.
Open Scope R_scope.

(* The clipped score family indexed by z in Y and q in Q. *)
Definition paper_main_data_clipped_family U n N (Bf : nat -> nat -> 'M[R]_(S n))
    (yf : nat -> nat -> nat -> R) (xs : list R) : nat -> nat -> R :=
  fun z q => paper_main_data_clipped_score U n N (Bf z q) (yf z q) xs.

(* The admissible pairs: symmetric, operator-bounded, unit dual vector. *)
Definition paper_main_data_clipped_admissible n N k (Bf : nat -> nat -> 'M[R]_(S n))
    (yf : nat -> nat -> nat -> R) (Y Q : list nat) : Prop :=
  forall z q, In z Y -> In q Q ->
    paper_main_symmetric (Bf z q) /\
    matrix_operator_norm n (paper_main_matrix_from_public n (Bf z q)) <= k /\
    euclidean_norm (yf z q) (List.seq 0 N) <= 1.

Lemma pmdcs_family_lipschitz U n N k Bf yf Y Q :
  0 <= U -> 0 <= k -> paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  forall xs ys z q, List.length xs = (N * S n)%N -> List.length ys = (N * S n)%N ->
    In z Y -> In q Q ->
    Rabs (paper_main_data_clipped_family U n N Bf yf xs z q -
          paper_main_data_clipped_family U n N Bf yf ys z q) <=
      2 * k * U * paper_main_gordon_distance (N * S n) xs ys.
Proof.
move=> HU Hk Had xs ys z q _ _ Hz Hq.
have [HB [HA Hy]] := Had z q Hz Hq.
exact: paper_main_data_clipped_score_lipschitz.
Qed.

(* 1. The soft minimax keeps the 2kU bound, for all lists. *)
Theorem paper_main_data_clipped_soft_lipschitz U n N k beta gamma Bf yf Y Q xs ys :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  Rabs (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf xs) Y Q -
        soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf ys) Y Q) <=
    2 * k * U * paper_main_gordon_distance (N * S n) xs ys.
Proof.
move=> HU Hk Hb Hg HY HQ Had.
apply: paper_main_soft_minimax_lipschitz => // z q Hz Hq.
have [HB [HA Hy]] := Had z q Hz Hq.
exact: paper_main_data_clipped_score_lipschitz.
Qed.

(* 2. Gaussian integrability and the iterated expectation. *)
Theorem paper_main_data_clipped_soft_gaussian_law U n N k beta gamma Bf yf Y Q :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  (gaussian_product_law (N * S n)).-integrable setT
    (fun x => (soft_minimax beta gamma
      (paper_main_data_clipped_family U n N Bf yf (tval x)) Y Q)%:E) /\
  (\int[gaussian_product_law (N * S n)]_x
      (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf (tval x)) Y Q)%:E =
    (gaussian_iterated_expectation (N * S n)
      (fun xs => soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf xs) Y Q))%:E)%E.
Proof.
move=> HU Hk Hb Hg HY HQ Had.
apply: (paper_main_soft_gaussian_law (N * S n) beta gamma
  (paper_main_data_clipped_family U n N Bf yf) Y Q (2 * k * U)) => //.
- by apply: Rmult_le_pos => //; lra.
- exact: pmdcs_family_lipschitz.
Qed.

(* 3. Measurability of the sublevel sets. *)
Theorem paper_main_data_clipped_soft_le_measurable U n N k beta gamma Bf yf Y Q c :
  0 <= U -> 0 <= k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  measurable [set x : (N * S n)%N.-tuple (measurableTypeR R) |
    Rle (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf (tval x)) Y Q) c].
Proof.
move=> HU Hk Hb Hg HY HQ Had.
apply: (paper_main_soft_gaussian_le_measurable (N * S n) beta gamma
  (paper_main_data_clipped_family U n N Bf yf) Y Q (2 * k * U)) => //.
- by apply: Rmult_le_pos => //; lra.
- exact: pmdcs_family_lipschitz.
Qed.

(* 4. The Gaussian lower tail with L = 2kU, for k > 0 and U > 0. *)
Theorem paper_main_data_clipped_soft_lower_tail U n N k beta gamma Bf yf Y Q u :
  0 < U -> 0 < k -> 0 < beta -> 0 < gamma -> Y <> [] -> Q <> [] -> 0 < u ->
  paper_main_data_clipped_admissible n N k Bf yf Y Q ->
  (gaussian_product_law (N * S n)
    [set x | Rle (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf (tval x)) Y Q)
      (fine (\int[gaussian_product_law (N * S n)]_v
        (soft_minimax beta gamma (paper_main_data_clipped_family U n N Bf yf (tval v)) Y Q)%:E)%E
       - u)] <=
    (exp (- u ^ 2 / (2 * (2 * k * U) ^ 2)))%:E)%E.
Proof.
move=> HU Hk Hb Hg HY HQ Hu Had.
apply: (paper_main_soft_gaussian_lower_tail (N * S n) beta gamma
  (paper_main_data_clipped_family U n N Bf yf) Y Q (2 * k * U) u) => //.
- by apply: Rmult_lt_0_compat => //; lra.
- exact: pmdcs_family_lipschitz U n N k Bf yf Y Q (Rlt_le _ _ HU) (Rlt_le _ _ Hk) Had.
Qed.
