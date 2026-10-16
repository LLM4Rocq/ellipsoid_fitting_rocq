(* Raw quadratic-feature adjoints for Gaussian and admissible mixture samples.
   sample_adj uses W_i=(x_i x_i^T-I)/sqrt(d); the reserve uses the raw
   feature B_i=x_i x_i^T-I. Its adjoint bound is therefore C*d, with the
   same C=adj_const K (252)%R (alpha+1). No fourth moment or symmetry is used.

   For countable families we reuse the proved truncation with tail mass
   at most (d+1)^(-3). The plan suggested d^(-4), but the existing bound
   already gives n(d)*tail ->0 at density n(d)/d^2 ->alpha. The theorem
   trunc_nr_small proves that estimate explicitly, so no new cutoff or
   replacement construction is needed. The replacement keeps the same K. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype sequences.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import measurable_realfun numfun probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean opnorm nuclear.
From GaussianAnalysis.matrix Require Import centered_quadratic_correction.
From GaussianAnalysis.comparison Require Import gauss_matrix_law.
From GaussianAnalysis.random_matrix Require Import symmetric_reserve.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions MixtureDefinitions.
From EllipsoidUniversality Require Import CountableMixtureDefinitions.
From EllipsoidUniversality.Sat Require Import Apriori.
From EllipsoidUniversality.Condition Require Import Unsat.
From EllipsoidUniversality.Countable Require Import Truncation.
Require Import EllipsoidUniversality.Countable.Theorem.
From EllipsoidUniversality.Shifted Require Import GaussianRows GaussianExports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition raw_sample_adj {n d} (x : paper_main_sample n d) (z : 'rV[RR]_n) :=
  coef_adj (reserve_feature (gauss_matrix_law.tuple_mx (sample_row_tuple x))) z.

Lemma sample_row_matrix_row n d (x : paper_main_sample n d) i :
  row i (gauss_matrix_law.tuple_mx (sample_row_tuple x)) = (paper_main_point x i)^T.
Proof.
apply/matrixP => a b.
by rewrite /gauss_matrix_law.tuple_mx /sample_row_tuple !mxE tnth_mktuple !mxE.
Qed.

Lemma raw_sample_adj_scaled n d (x : paper_main_sample n d) z : (0<d)%N ->
  raw_sample_adj x z = Num.sqrt d%:R *: sample_adj x z.
Proof.
move=> d0.
have dn : Num.sqrt d%:R != (0:RR) by rewrite gt_eqF // sqrtr_gt0 ltr0n.
rewrite /raw_sample_adj /sample_adj /coef_adj scaler_sumr.
apply: eq_bigr => i _.
rewrite /reserve_feature sample_row_matrix_row trmxK /sample_W.
by rewrite !scalerA mulrAC mulfV // mul1r.
Qed.

Lemma raw_sample_adjoint_le n d (x : paper_main_sample n d) (C : R) :
  (0<d)%N ->
  (forall z : 'rV[RR]_n, frobenius (sample_adj x z) <= C*Num.sqrt d%:R*frobenius z) ->
  forall z : 'rV[RR]_n, frobenius (raw_sample_adj x z) <= C*d%:R*frobenius z.
Proof.
move=> d0 h z; rewrite raw_sample_adj_scaled // frobeniusZ ger0_norm ?sqrtr_ge0 //.
apply: le_trans (ler_wpM2l (sqrtr_ge0 _) (h z)) _.
have -> : Num.sqrt d%:R * (C * Num.sqrt d%:R * frobenius z) =
    C * (Num.sqrt d%:R)^+2 * frobenius z by ring.
by rewrite sqr_sqrtr ?ler0n.
Qed.

(* The actual adjoint success event is Borel, independently of the
   exceptional sets supplied by the a priori estimates. *)
Definition raw_adjoint_matrix_event n d (L : R) : set 'M[RR]_(n,d) :=
  [set H | forall z : 'rV[RR]_n,
    frobenius (coef_adj (reserve_feature H) z) <= L*frobenius z].

Lemma raw_adjoint_matrix_closed n d L : closed (@raw_adjoint_matrix_event n d L).
Proof.
have -> : @raw_adjoint_matrix_event n d L =
    \bigcap_(z in [set: 'rV[RR]_n])
    [set H : 'M[RR]_(n,d) | frobenius (coef_adj (reserve_feature H) z) <= L*frobenius z].
  apply/seteqP; split=> H h.
  - by move=> z _; exact: h.
  - by move=> z; exact: (h z I).
apply: closed_bigI => z _.
have cf : continuous (fun H : 'M[RR]_(n,d) => frobenius (coef_adj (reserve_feature H) z)).
  move=> H; apply: (continuous_comp
    (f:=fun X : 'M[RR]_(n,d) => coef_adj (reserve_feature X) z)
    (g:=@frobenius RR d d)).
  - exact: reserve_adjoint_continuous.
  - exact: reserve_frobenius_continuous.
exact: (continuous_closedP _).1 cf _ (@closed_le RR (L*frobenius z)).
Qed.

Lemma raw_adjoint_matrix_measurable n d L : measurable (@raw_adjoint_matrix_event n d L).
Proof.
rewrite -[X in measurable X]setCK; apply: measurableC.
apply: open_measurable_mx; apply: closed_openC; exact: raw_adjoint_matrix_closed.
Qed.

Theorem finite_raw_adjoint_bound (K alpha : R) (N : nat -> nat)
    (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) :
  mixture_family K N w mu -> 0 < alpha ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D<=d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x -> forall z : 'rV[RR]_(n d),
        frobenius (raw_sample_adj x z) <= adj_const K (252)%R (alpha+1)*d%:R*frobenius z].
Proof.
move=> hfam a0 n hn eps e0.
have [D hD] := mixture_adjoint_bound K alpha N w mu hfam a0 n hn eps e0.
exists (maxn D 1%N) => d; rewrite geq_max => /andP[dD d0].
have [E [mE PE hE]] := hD d dD; exists E; split=> // x nx.
exact: (@raw_sample_adjoint_le (n d) d x _ d0 (hE x nx)).
Qed.

Theorem gaussian_raw_adjoint_bound (alpha : R) : 0 < alpha ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D<=d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (gaussian_product_law (n d*d) E <= eps%:E)%E &
      forall x, ~ E x -> forall z : 'rV[RR]_(n d),
        frobenius (raw_sample_adj x z) <= adj_const 2%:R 252%:R (alpha+1)*d%:R*frobenius z].
Proof.
move=> a0 n hn eps e0.
have [D hD] := gaussian_adjoint_holds alpha a0 n hn eps e0.
exists (maxn D 1%N) => d; rewrite geq_max => /andP[dD d0].
have [E [mE PE hE]] := hD d dD; exists E; split=> // x nx.
have [_ h] := hE x nx; exact: (@raw_sample_adjoint_le (n d) d x _ d0 h).
Qed.

Theorem countable_raw_adjoint_bound (K alpha : R) (w : nat -> nat -> R)
    (mu : nat -> nat -> nat -> probability (measurableTypeR R) R) :
  countable_mixture_family K w mu -> 0 < alpha ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D<=d)%N ->
  exists E : set (paper_main_sample (n d) d),
    [/\ measurable E,
      (countable_mixture_probability (w d) (mu d) (n d) d E <= eps%:E)%E &
      forall x, ~ E x -> forall z : 'rV[RR]_(n d),
        frobenius (raw_sample_adj x z) <= adj_const K (252)%R (alpha+1)*d%:R*frobenius z].
Proof.
move=> hfam a0 n hn eps e0.
have e2 : 0 < eps/2 by rewrite divr_gt0.
have [D1 h1] := @finite_raw_adjoint_bound K alpha _ _ _
  (trunc_family K w mu hfam) a0 n hn (eps/2) e2.
have [D2 h2] := trunc_nr_small K w mu hfam n alpha a0 hn (eps/2) e2.
exists (maxn D1 D2) => d; rewrite geq_max => /andP[d1 d2].
have [E [mE PE hE]] := h1 d d1; exists E; split=> //.
have hc := trunc_coupling K w mu hfam (n d) d E mE.
have ff := trunc_probability_fin K w mu hfam n d E mE.
have hr : (n d)%:R*trunc_r K w mu hfam d <= eps/2 := h2 d d2.
move: hc PE ff.
set X := countable_mixture_probability _ _ _ _ E.
set Y := mixture_probability _ _ _ _ _ E => hc PE ff.
have xf : X \is a fin_num.
  clearbody X Y.
  by move: hc PE ff; case: X => [x||]; case: Y => [y||] //=.
move: hc PE; rewrite -(fineK xf) -(fineK ff) /= !lee_fin.
rewrite ler_norml => /andP[_ h] PE.
change (is_true (fine Y <= eps / 2)) in PE.
lra.
Qed.
