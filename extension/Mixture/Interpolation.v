(* Theorem 1.9 of Koehler and Sohn (arXiv 2608.27372, lines 549-566 of
   arxiv_v1.tex), the small-residual interpolation, for finite mixtures of
   product laws, at Stdlib's R: mixture_interpolation_statement of
   MixtureStatement. Item X5 of phase 6 (notes/paired-law-plan-v2.md,
   section 4.3).

   Proved here.
   - interpolation_of_residual: the conclusion of
     small_residual_interpolation_flat (Sat/SmallResidual) at a sample x
     gives mixture_interpolation n d C1 x. For y : 'I_n -> R take the row
     vector of the y_i and Y = max_i |y_i|; then
     <W_i, Delta> = (x_i^T Delta x_i - tr Delta) / sqrt d
     (quadratic_form_mxdot, trace_mxdot of Unsat/LeastSquares) and
     |v^T Delta v| <= opnorm Delta |v|^2 (mxdot_opnorm of
     library/matrix/opnorm.v).
   - mixture_small_residual: Theorem 1.9 for mixture_probability, in the
     form of small_residual_interpolation_flat. Given the labels s of the
     points, the sample law mixture_labelled_law is the flat family
     k |-> mu (s_(k / d)) (k mod d) of component laws (labelled_component
     of Mixture/Flat), so small_residual_interpolation_flat gives, for
     every large d and every label tuple s, a measurable event E_s of
     probability at most eps outside which the conclusion holds; the
     threshold does not depend on s. The intersection of the E_s is
     measurable, contains the samples where the conclusion fails, and has
     mixture probability at most eps (mixture_cover of
     library/probability/mixture.v, with the product weights of
     mixture_weights_prod).
   - mixture_interpolation_holds: mixture_interpolation_statement, by
     interpolation_of_residual. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals Rstruct.
From mathcomp Require Import exp.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From GaussianAnalysis.probability Require Import lindeberg mixture.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidFitting Require Import Spectral.SymmetricDiagonalization.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Mixture Require Import Flat.
From EllipsoidUniversality.Sat Require Import Apriori SmallResidual.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Local Notation RR := (R : realType).

(* The conclusion of the small-residual interpolation at a sample gives the
   interpolation property of MixtureDefinitions. *)
Lemma interpolation_of_residual (n d : nat) (x : paper_main_sample n d)
    (C1 : R) :
  (forall (y : 'rV[R]_n) (Y : R), (forall i, `|y 0 i| <= Y) ->
    exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
      forall i, mxdot (sample_W x i) Delta = y 0 i + b &
      opnorm Delta <=
        C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y +
              frobenius y / d%:R)]) ->
  mixture_interpolation n d C1 x.
Proof.
move=> h y.
pose yr : 'rV[R]_n := \row_i y i.
pose Y := \big[Num.max/0]_(i < n) `|y i|.
have hY i : `|yr 0 i| <= Y by rewrite mxE; exact: le_bigmax.
have [Delta [b [Ds hD hop]]] := h yr Y hY.
exists Delta, b; split.
- rewrite /paper_main_symmetric => i j; move/symmetricmxP: Ds => Ds.
  by rewrite -[in LHS]Ds mxE.
- move=> i; have := hD i; rewrite mxE => <-.
  by rewrite /sample_W mxdotZl mxdotBl -quadratic_form_mxdot -trace_mxdot mulrC.
- move=> v; rewrite !paper_main_quadratic_form_mxdot mul1mx.
  apply: le_trans (mxdot_opnorm _ _ _) _.
  rewrite -mulrA -expr2 frobenius_sqr.
  apply: ler_wpM2r; first exact: mxdot_ge0.
  apply: le_trans hop _.
  have -> : frobenius yr = Num.sqrt (\sum_(i < n) y i ^+ 2).
    rewrite /frobenius /mxdot big_ord1; congr Num.sqrt.
    by apply: eq_bigr => i _; rewrite mxE expr2.
  by rewrite addrC.
Qed.

(* Theorem 1.9 for finite mixtures of product laws, in the form of
   small_residual_interpolation_flat: the threshold D does not depend on the
   family, and the event is the intersection over the label tuples. *)
Theorem mixture_small_residual (K alpha : R) :
  0 < K -> 0 < alpha -> alpha < 2^-1 ->
  exists C1 : R, 0 < C1 /\
  forall (N : nat -> nat) (w : nat -> nat -> R)
         (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
    mixture_family K N w mu ->
  forall n : nat -> nat, universality_density_tends_to n alpha ->
  forall eps : R, 0 < eps -> exists D : nat, forall d, (D <= d)%N ->
  exists E : set (paper_main_sample (n d) d), [/\ measurable E,
    (mixture_probability (N d) (w d) (mu d) (n d) d E <= eps%:E)%E &
    forall x, ~ E x -> forall (y : 'rV[R]_(n d)) (Y : R),
      (forall i, `|y 0 i| <= Y) ->
      exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
        forall i, mxdot (sample_W x i) Delta = y 0 i + b &
        opnorm Delta <=
          C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y +
                frobenius y / d%:R)]].
Proof.
move=> K0 a0 ah.
have [C1 [C10 hC]] := small_residual_interpolation_flat K alpha K0 a0 ah.
exists C1; split => // N w mu hfam n hn eps e0.
have [D hD] := hC n hn eps e0.
exists D => d dD.
have [w0 [w1 hmu]] := hfam d.
have hw : mixture_weights (fun t : 'I_(N d) => w d t) by split => // t; exact: w0.
have hws := @mixture_weights_prod _ _ _ (n d) hw.
pose P (s : (n d).-tuple 'I_(N d)) :=
  mixture_labelled_law (N d) (mu d) (n d) d s.
pose Q (x : paper_main_sample (n d) d) := forall (y : 'rV[R]_(n d)) (Y : R),
  (forall i, `|y 0 i| <= Y) ->
  exists (Delta : 'M[R]_d) (b : R), [/\ Delta \is symmetricmx,
    forall i, mxdot (sample_W x i) Delta = y 0 i + b &
    opnorm Delta <=
      C1 * (ln (d%:R : RR) ^+ 4 / Num.sqrt d%:R * Y + frobenius y / d%:R)].
pose F := [set x : paper_main_sample (n d) d | ~ Q x].
have hE (s : (n d).-tuple 'I_(N d)) :
    exists E : set (paper_main_sample (n d) d),
    [/\ measurable E, F `<=` E & (P s E <= eps%:E)%E].
  have [E [mE PE hE]] := hD d dD _
    (labelled_component K (N d) (mu d) (n d) d s hmu).
  exists E; split => // x Fx; apply: contrapT => nE; apply: Fx.
  exact: hE x nE.
pose E s := projT1 (cid (hE s)).
have mE s : measurable (E s) by case: (projT2 (cid (hE s))).
have FE s : F `<=` E s by case: (projT2 (cid (hE s))).
have PE s : (P s (E s) <= eps%:E)%E by case: (projT2 (cid (hE s))).
have [mI FI PI] := mixture_cover (P := P) hws mE FE PE.
exists (\bigcap_(s in [set: (n d).-tuple 'I_(N d)]) E s); split.
- exact: mI.
- by move: PI; rewrite mixtureE.
- by move=> x nx; apply: contrapT => hx; apply: nx; exact: FI.
Qed.

(* Theorem 1.9 for finite mixtures of product laws: the interpolation
   statement of MixtureStatement. *)
Theorem mixture_interpolation_holds : mixture_interpolation_statement.
Proof.
move=> K alpha K0 a0 ah.
have [C1 [C10 hC]] := mixture_small_residual K alpha K0 a0 ah.
exists C1; split => // N w mu hfam n hn eps e0.
have [D hD] := hC N w mu hfam n hn eps e0.
exists D => d dD; have [E [mE PE hE]] := hD d dD.
exists E; split => // x nE.
exact: interpolation_of_residual (hE x nE).
Qed.
