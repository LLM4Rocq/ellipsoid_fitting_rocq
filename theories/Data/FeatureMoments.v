(* Moments of the quadratic data feature of one standard Gaussian row.

   Let N = n + 1. The row x has the law gaussian_product_law N on N-tuples:
   N independent standard normal coordinates x_j = List.nth j (tval x) 0.
   Its feature is W x = (x x^T - I) / sqrt N (paper_main_data_row_feature,
   an instance of paper_main_data_feature). The feature of the point i of an
   m-point sample is paper_main_data_feature at the coordinates of that row
   (paper_main_data_feature_head), so the head feature
   paper_main_head_feature x i is this map applied to row i.

   - pmdf_actual: an integrand F that is continuous and polynomially bounded
     (pmdf_regular) is integrable under gaussian_product_law d, and its
     Lebesgue integral is the iterated expectation
     gaussian_iterated_expectation d F (from gpp_all_sections and
     gpp_joint_measurable). pmdf_bigsum: regularity and linearity of the
     iterated expectation over finite sums.
   - pmdf_quad_covariance: for q_S = sum_ab S_ab (x_a x_b - delta_ab)
     (pmdf_quad), E q_S q_T = <S, T> + <S, T^T>.
   - paper_main_data_feature_frobenius: |W|_F^2 is integrable and
     E |W|_F^2 = N + 1.

   Proofs. The coordinate moments of Data.FeatureMomentsCoordinates
   give E (x_a x_b - delta_ab) (x_c x_e - delta_ce) = delta_ac delta_be +
   delta_ae delta_bc, and the expectation is linear over the finite sums
   (pmdf_bigsum). *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral measurable_realfun.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import Soft.Definitions
  Gaussian.IteratedExpectationDefinitions Gaussian.IteratedExpectation
  Analysis.CoordinateContinuityDefinitions Gaussian.CoordinateWeightDefinitions
  Gaussian.CoordinatePolynomialDomain Gaussian.CovarianceDefinitions
  GaussianProbabilityProductDefinitions Analysis.ContinuousTupleMeasurability
  Gaussian.ProductLawIntegrals Matrix.Definitions Tensor.Definitions
  Goe.Definitions Goe.MatrixBasis PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Spectral.Transport Gaussian.FeatureCoordinates
  Geometry.HeadFrobenius Geometry.HeadFeature Spectral.SymmetricBilinear
  Data.FeatureMomentsCoordinates.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* W f = (f f^T - I) / sqrt N for the coordinates f of a point of R^N. *)
Definition paper_main_data_feature n (f : nat -> R) : 'M[R]_(S n) :=
  (Num.sqrt (S n)%:R)^-1 *:
    (paper_main_symmetric_column n f *m (paper_main_symmetric_column n f)^T - 1%:M).

(* The head feature of point i of an m-point sample is the data feature of
   the coordinates of row i. *)
Theorem paper_main_data_feature_head m n (x : paper_main_sample m (S n)) (i : nat) :
  paper_main_head_feature x i =
  paper_main_data_feature n (fun j => List.nth (i * S n + j) (tval x) 0).
Proof. by []. Qed.

(* For regular integrands the iterated expectation is the Lebesgue integral. *)
Lemma pmdf_actual d (F : list R -> R) :
  pmdf_regular d F ->
  (gaussian_product_law d).-integrable setT (fun x => (F (tval x))%:E) /\
  (\int[gaussian_product_law d]_x (F (tval x))%:E =
    (gaussian_iterated_expectation d F)%:E)%E.
Proof.
move=> HR; have [HI [HA _]] := pmdf_regular_domain HR.
apply: gpp_all_sections => //.
apply/measurable_EFinP; apply: gpp_joint_measurable; exact: HR.1.
Qed.

(* Regularity and linearity over finite sums with ordinal indices. *)
Lemma pmdf_bigsum d m (G : 'I_m -> list R -> R) :
  (forall i, pmdf_regular d (G i)) ->
  pmdf_regular d (fun xs => \sum_(i < m) G i xs) /\
  gaussian_iterated_expectation d (fun xs => \sum_(i < m) G i xs) =
  \sum_(i < m) gaussian_iterated_expectation d (G i).
Proof.
elim: m G => [|m IH] G HG.
  have -> : (fun xs => \sum_(i < 0) G i xs) = (fun _ => 0).
    by apply: funext => xs; rewrite big_ord0.
  rewrite big_ord0; split; first exact: pmdf_regular_const.
  by case: (gaussian_iterated_constant d 0).
have -> : (fun xs => \sum_(i < m.+1) G i xs) =
    (fun xs => \sum_(i < m) G (widen_ord (leqnSn m) i) xs + G ord_max xs).
  by apply: funext => xs; rewrite big_ord_recr.
rewrite big_ord_recr /=.
have [IHr IHe] := IH (fun i => G (widen_ord (leqnSn m) i)) (fun i => HG _).
split; first exact: pmdf_regular_add IHr (HG ord_max).
have [_ HE] := gaussian_iterated_add d _ _ (pmdf_regular_integrable IHr)
  (pmdf_regular_integrable (HG ord_max)).
rewrite -IHe; exact: HE.
Qed.

Lemma pmdf_scale_expectation d F (c : R) :
  pmdf_regular d F ->
  gaussian_iterated_expectation d (fun xs => c * F xs) =
  c * gaussian_iterated_expectation d F.
Proof. by move=> HR; case: (gaussian_iterated_scale d F c (pmdf_regular_integrable HR)). Qed.

Lemma pmdf_sum_kron m (a : 'I_m) (F : 'I_m -> R) :
  \sum_(c < m) (a == c)%:R * F c = F a.
Proof.
rewrite (bigD1 a) //= eqxx mul1r big1 ?addr0 // => c Hc.
by rewrite eq_sym (negbTE Hc) mul0r.
Qed.

Section DataFeature.
Variable n : nat.
Local Notation N := (S n).
Implicit Types (S T : 'M[R]_N).

(* The feature of the standard Gaussian row x. *)
Definition paper_main_data_row_feature (x : N.-tuple (measurableTypeR R)) : 'M[R]_N :=
  paper_main_data_feature n (fun j => List.nth j (tval x) 0).

Lemma paper_main_data_feature_entry (f : nat -> R) (a b : 'I_N) :
  paper_main_data_feature n f a b = (Num.sqrt N%:R)^-1 * (f a * f b - (a == b)%:R).
Proof. by rewrite !mxE big_ord1 !mxE. Qed.

Lemma pmdf_ord_le (a : 'I_N) : (a <= n)%coq_nat.
Proof. by have /ssrnat.ltP := ltn_ord a; lia. Qed.

Lemma pmdf_kron_ord (a b : 'I_N) : pmdf_kron a b = (a == b)%:R.
Proof.
rewrite /pmdf_kron; case: (Nat.eqb_spec a b) => [/val_inj ->|H]; first by rewrite eqxx.
by rewrite (introF eqP) // => E; apply: H; rewrite E.
Qed.

(* sum_ab S_ab (x_a x_b - delta_ab). *)
Definition pmdf_quad S (xs : list R) : R :=
  \sum_(a < N) \sum_(b < N) S a b * pmdf_centered a b xs.

Lemma pmdf_regular_entry S (a b : 'I_N) :
  pmdf_regular N (fun xs => S a b * pmdf_centered a b xs).
Proof.
apply: pmdf_regular_scale; apply: pmdf_regular_centered.
- by have := pmdf_ord_le a; lia.
- by have := pmdf_ord_le b; lia.
Qed.

Lemma pmdf_quad_regular S : pmdf_regular N (pmdf_quad S).
Proof.
have [H _] := pmdf_bigsum N N (fun a xs => \sum_(b < N) S a b * pmdf_centered a b xs)
  (fun a => (pmdf_bigsum N N _ (fun b => pmdf_regular_entry S a b)).1).
exact: H.
Qed.

(* E (x_a x_b - delta_ab) q_T = T_ab + T_ba. *)
Lemma pmdf_centered_quad (a b : 'I_N) T :
  pmdf_regular N (fun xs => pmdf_centered a b xs * pmdf_quad T xs) /\
  gaussian_iterated_expectation N (fun xs => pmdf_centered a b xs * pmdf_quad T xs) =
  T a b + T b a.
Proof.
have Rc : forall c e : 'I_N, pmdf_regular N (pmdf_centered c e).
  by move=> c e; apply: pmdf_regular_centered; [have := pmdf_ord_le c | have := pmdf_ord_le e]; lia.
have RG : forall (c e : 'I_N),
    pmdf_regular N (fun xs => T c e * (pmdf_centered a b xs * pmdf_centered c e xs)).
  by move=> c e; apply: pmdf_regular_scale; exact: pmdf_regular_mult (Rc a b) (Rc c e).
have E : (fun xs => pmdf_centered a b xs * pmdf_quad T xs) =
    (fun xs => \sum_(c < N) \sum_(e < N) T c e * (pmdf_centered a b xs * pmdf_centered c e xs)).
  apply: funext => xs; rewrite /pmdf_quad mulr_sumr; apply: eq_bigr => c _.
  rewrite mulr_sumr; apply: eq_bigr => e _; ring.
rewrite E.
have [HR HE] := pmdf_bigsum N N
  (fun c xs => \sum_(e < N) T c e * (pmdf_centered a b xs * pmdf_centered c e xs))
  (fun c => (pmdf_bigsum N N _ (fun e => RG c e)).1).
split => //; rewrite HE.
transitivity (\sum_(c < N) \sum_(e < N)
    T c e * ((a == c)%:R * (b == e)%:R + (a == e)%:R * (b == c)%:R)).
  apply: eq_bigr => c _.
  have [_ ->] := pmdf_bigsum N N _ (fun e => RG c e).
  apply: eq_bigr => e _.
  rewrite (pmdf_scale_expectation N _ (T c e) (pmdf_regular_mult (Rc a b) (Rc c e))).
  rewrite (pmdf_centered_moment n a b c e (pmdf_ord_le a) (pmdf_ord_le b)
    (pmdf_ord_le c) (pmdf_ord_le e)).2.
  by rewrite !pmdf_kron_ord RplusE !RmultE.
transitivity (\sum_(c < N) ((a == c)%:R * T c b + (b == c)%:R * T c a)).
  apply: eq_bigr => c _.
  transitivity (\sum_(e < N) ((b == e)%:R * ((a == c)%:R * T c e) +
                              (a == e)%:R * ((b == c)%:R * T c e))).
    by apply: eq_bigr => e _; ring.
  by rewrite big_split /= !pmdf_sum_kron.
by rewrite big_split /= !pmdf_sum_kron.
Qed.

(* E q_S q_T = <S, T> + <S, T^T>. *)
Lemma pmdf_quad_covariance S T :
  pmdf_regular N (fun xs => pmdf_quad S xs * pmdf_quad T xs) /\
  gaussian_iterated_expectation N (fun xs => pmdf_quad S xs * pmdf_quad T xs) =
  paper_main_pairing S T + paper_main_pairing S T^T.
Proof.
have RG : forall a b : 'I_N,
    pmdf_regular N (fun xs => S a b * (pmdf_centered a b xs * pmdf_quad T xs)).
  by move=> a b; apply: pmdf_regular_scale; exact: (pmdf_centered_quad a b T).1.
have E : (fun xs => pmdf_quad S xs * pmdf_quad T xs) =
    (fun xs => \sum_(a < N) \sum_(b < N) S a b * (pmdf_centered a b xs * pmdf_quad T xs)).
  apply: funext => xs; rewrite {1}/pmdf_quad mulr_suml; apply: eq_bigr => a _.
  rewrite mulr_suml; apply: eq_bigr => b _; ring.
rewrite E.
have [HR HE] := pmdf_bigsum N N
  (fun a xs => \sum_(b < N) S a b * (pmdf_centered a b xs * pmdf_quad T xs))
  (fun a => (pmdf_bigsum N N _ (fun b => RG a b)).1).
split => //; rewrite HE.
transitivity (\sum_(a < N) \sum_(b < N) S a b * (T a b + T b a)).
  apply: eq_bigr => a _.
  have [_ ->] := pmdf_bigsum N N _ (fun b => RG a b).
  apply: eq_bigr => b _.
  rewrite (pmdf_scale_expectation N _ (S a b) (pmdf_centered_quad a b T).1).
  by rewrite (pmdf_centered_quad a b T).2.
rewrite /paper_main_pairing -big_split; apply: eq_bigr => a _.
rewrite -big_split; apply: eq_bigr => b _; rewrite mxE.
by rewrite mulrDr.
Qed.

(* sum_ab (x_a x_b - delta_ab)^2, and its expectation N^2 + N. *)
Definition pmdf_square (xs : list R) : R :=
  \sum_(a < N) \sum_(b < N) pmdf_centered a b xs * pmdf_centered a b xs.

Lemma pmdf_square_moment :
  pmdf_regular N pmdf_square /\
  gaussian_iterated_expectation N pmdf_square = N%:R * N%:R + N%:R.
Proof.
have Rc : forall c e : 'I_N, pmdf_regular N (pmdf_centered c e).
  by move=> c e; apply: pmdf_regular_centered; [have := pmdf_ord_le c | have := pmdf_ord_le e]; lia.
have RG : forall a b : 'I_N,
    pmdf_regular N (fun xs => pmdf_centered a b xs * pmdf_centered a b xs).
  by move=> a b; exact: pmdf_regular_mult (Rc a b) (Rc a b).
have [HR HE] := pmdf_bigsum N N
  (fun a xs => \sum_(b < N) pmdf_centered a b xs * pmdf_centered a b xs)
  (fun a => (pmdf_bigsum N N _ (fun b => RG a b)).1).
split; first exact: HR.
rewrite /pmdf_square HE.
transitivity (\sum_(a < N) (N%:R + 1) : R).
  apply: eq_bigr => a _.
  have [_ ->] := pmdf_bigsum N N _ (fun b => RG a b).
  transitivity (\sum_(b < N) (1 + (a == b)%:R * 1) : R).
    apply: eq_bigr => b _.
    rewrite (pmdf_centered_moment n a b a b (pmdf_ord_le a) (pmdf_ord_le b)
      (pmdf_ord_le a) (pmdf_ord_le b)).2.
    rewrite !pmdf_kron_ord !eqxx RplusE !RmultE (eq_sym b a).
    by case: (a == b); rewrite /= ?mulr1 ?mul1r ?mulr0 ?addr0.
  rewrite big_split /= pmdf_sum_kron sumr_const card_ord.
  by rewrite -[1 *+ N]mulr_natl mulr1 addrC.
rewrite sumr_const card_ord -mulr_natl; ring.
Qed.

Lemma pmdf_sqrt_inv2 : (Num.sqrt N%:R)^-1 * (Num.sqrt N%:R)^-1 = (N%:R)^-1 :> R.
Proof. by rewrite -invfM -expr2 sqr_sqrtr // ler0n. Qed.

Lemma pmdf_pairing_self xs :
  paper_main_pairing (paper_main_data_feature n (fun j => List.nth j xs 0))
    (paper_main_data_feature n (fun j => List.nth j xs 0)) =
  (N%:R)^-1 * pmdf_square xs.
Proof.
rewrite /paper_main_pairing /pmdf_square mulr_sumr; apply: eq_bigr => a _.
rewrite mulr_sumr; apply: eq_bigr => b _.
rewrite paper_main_data_feature_entry /pmdf_centered pmdf_kron_ord RminusE RmultE.
by rewrite -pmdf_sqrt_inv2; ring.
Qed.

Theorem paper_main_data_feature_frobenius :
  (gaussian_product_law N).-integrable setT
    (fun x => (paper_main_frobenius (paper_main_data_row_feature x) ^+ 2)%:E) /\
  (\int[gaussian_product_law N]_x
    (paper_main_frobenius (paper_main_data_row_feature x) ^+ 2)%:E = (N%:R + 1)%:E)%E.
Proof.
have [Rs Es] := pmdf_square_moment.
pose F := fun xs : list R => (N%:R)^-1 * pmdf_square xs.
have -> : (fun x => (paper_main_frobenius (paper_main_data_row_feature x) ^+ 2)%:E) =
    (fun x => (F (tval x))%:E).
  apply: funext => x.
  by rewrite pmh_frobenius_sqr /paper_main_data_row_feature pmdf_pairing_self.
have [HI HE] := pmdf_actual N F (@pmdf_regular_scale N _ (N%:R)^-1 Rs).
split; first exact: HI.
rewrite HE; congr (_%:E); rewrite /F (pmdf_scale_expectation N _ _ Rs) Es.
have HN : (N%:R : R) != 0 by rewrite pnatr_eq0.
by rewrite mulrDr (mulKf HN) (mulVf HN).
Qed.

End DataFeature.
