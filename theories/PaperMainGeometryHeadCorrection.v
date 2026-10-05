(* The deterministic core of the exact head correction and support transfer
   of the satisfiable phase (manuscript lem:head-correction-bounds, lines
   971-1061), with explicit finite-dimensional hypotheses.

   A head is a finite family W : 'I_m -> 'M[R]_d of feature matrices (in the
   paper W_i = (x_i x_i^T - I) / sqrt d for i in J). For a matrix P put
   r_i = <W_i, P>, Q_ij = <W_i, W_j>, and for coefficients a with Q a = r put
   E = - sum_j a_j W_j. Then:

   1. <W_i, P + E> = 0 for every head index (paper_main_head_correction_kernel),
      with the invertible-Gram choice a = Q^-1 r, the empty head (Q is the
      invertible 0 x 0 matrix and E = 0), the symmetry of E for symmetric
      W_i, and |E|_F^2 = a^T Q a (eq:EJ-frob, first identity).
   2. If |P|_F = 1 and |E|_F <= eta < 1, then P + E <> 0, the normalized matrix
      Pt = (P + E) / |P + E|_F has unit norm, keeps every constraint
      <W_i, .> = 0, satisfies |Pt - P|_F <= 2 eta, and
      <Z, Pt> >= <Z, P> - 2 eta |Z|_F for every Z.
   3. With the operator bound on E written as the Loewner hypothesis
      -delta I <= E <= delta I: lm I <= P <= lp I gives
      (lm - delta) I <= P + E <= (lp + delta) I, positive definiteness for
      delta < lm, the scaled bounds after normalization, and the
      bounded-condition form lam I <= Pt <= kappa lam I when
      lp + delta <= kappa (lm - delta).

   paper_main_head_correction_close assembles 1-3 into the deterministic
   form of eq:PJ-close and eq:width-transfer. The data event, the bounds on
   a_J and the cone-width asymptotics are not proved here; they are
   hypotheses (the norm bound eta and the Loewner slack delta). Nothing from
   the paper is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* The Gram matrix Q_ij = <W_i, W_j> of a head. *)
Definition paper_main_head_gram {d m : nat} (W : 'I_m -> 'M[R]_d) : 'M[R]_m :=
  \matrix_(i, j) paper_main_pairing (W i) (W j).

(* The residuals r_i = <W_i, P>. *)
Definition paper_main_head_residual {d m : nat} (W : 'I_m -> 'M[R]_d)
    (P : 'M[R]_d) : 'cV[R]_m :=
  \col_i paper_main_pairing (W i) P.

(* The correction E = - sum_j a_j W_j. *)
Definition paper_main_head_correction {d m : nat} (W : 'I_m -> 'M[R]_d)
    (a : 'cV[R]_m) : 'M[R]_d :=
  - \sum_(j < m) a j 0 *: W j.

(* The coefficients a = Q^-1 r. *)
Definition paper_main_head_coefficients {d m : nat} (W : 'I_m -> 'M[R]_d)
    (P : 'M[R]_d) : 'cV[R]_m :=
  invmx (paper_main_head_gram W) *m paper_main_head_residual W P.

(* S / |S|_F. *)
Definition paper_main_head_normalize {d : nat} (S : 'M[R]_d) : 'M[R]_d :=
  (paper_main_frobenius S)^-1 *: S.

(* The Loewner form of "S is a nonzero element of the bounded-condition cone
   K_kappa = {S >= 0 : lambda_max S <= kappa lambda_min S}":
   lam I <= S <= kappa lam I for some lam > 0. *)
Definition paper_main_head_condition {d : nat} (kappa : R) (S : 'M[R]_d) : Prop :=
  exists lam : R, 0 < lam /\ paper_main_loewner_le (lam *: 1%:M) S /\
    paper_main_loewner_le S ((kappa * lam) *: 1%:M).

Section HeadCorrection.
Variables (d m : nat).
Implicit Types (A B C D P E S Z : 'M[R]_d) (W : 'I_m -> 'M[R]_d) (a : 'cV[R]_m).

(* 1. The exact correction. *)

Lemma paper_main_head_correction_pairing W a S :
  paper_main_pairing S (paper_main_head_correction W a) =
  - \sum_(j < m) a j 0 * paper_main_pairing S (W j).
Proof. by rewrite /paper_main_head_correction pmh_pairingNr paper_main_pairing_sum. Qed.

Theorem paper_main_head_correction_kernel W P a :
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  forall i : 'I_m, paper_main_pairing (W i) (P + paper_main_head_correction W a) = 0.
Proof.
move=> Ha i.
have Hi : (paper_main_head_gram W *m a) i 0 = (paper_main_head_residual W P) i 0
  by rewrite Ha.
rewrite !mxE in Hi.
rewrite pmh_pairingDr paper_main_head_correction_pairing -Hi.
rewrite /paper_main_head_gram -sumrB big1 // => j _.
by rewrite mxE mulrC subrr.
Qed.

Theorem paper_main_head_coefficients_solve W P :
  paper_main_head_gram W \in unitmx ->
  paper_main_head_gram W *m paper_main_head_coefficients W P =
  paper_main_head_residual W P.
Proof.
by move=> HQ; rewrite /paper_main_head_coefficients mulmxA mulmxV // mul1mx.
Qed.

Lemma paper_main_head_correction_symmetric W a :
  (forall i, paper_main_symmetric (W i)) ->
  paper_main_symmetric (paper_main_head_correction W a).
Proof.
move=> HW i j; rewrite /paper_main_head_correction !mxE !summxE.
congr (- _); apply: eq_bigr => k _.
by rewrite !mxE HW.
Qed.

Theorem paper_main_head_correction_frobenius W a :
  paper_main_frobenius (paper_main_head_correction W a) ^+ 2 =
  (a^T *m paper_main_head_gram W *m a) 0 0.
Proof.
rewrite pmh_frobenius_sqr /paper_main_head_correction pmh_pairingNl pmh_pairingNr.
rewrite opprK pmh_pairing_suml mxE.
under eq_bigr do rewrite paper_main_pairing_sum mulr_sumr.
under [RHS]eq_bigr do rewrite mxE mulr_suml.
rewrite exchange_big /=; apply: eq_bigr => i _; apply: eq_bigr => j _.
rewrite /paper_main_head_gram !mxE; ring.
Qed.

(* 2. Normalization and support transfer. *)

Lemma paper_main_head_normalize_unit S :
  S != 0 -> paper_main_frobenius (paper_main_head_normalize S) = 1.
Proof. exact: pmh_frobenius_normalize. Qed.

Lemma paper_main_head_normalize_kernel (V S : 'M[R]_d) :
  paper_main_pairing V S = 0 ->
  paper_main_pairing V (paper_main_head_normalize S) = 0.
Proof.
by move=> H; rewrite /paper_main_head_normalize paper_main_pairing_scale H mulr0.
Qed.

Theorem paper_main_head_perturbation_lower P E :
  paper_main_frobenius P = 1 ->
  1 - paper_main_frobenius E <= paper_main_frobenius (P + E).
Proof.
move=> HP; have := pmh_frobenius_triangle _ (P + E) (- E).
rewrite addrK pmh_frobeniusN HP => H; lra.
Qed.

Theorem paper_main_head_perturbation_nonzero P E (eta : R) :
  paper_main_frobenius P = 1 -> paper_main_frobenius E <= eta -> eta < 1 ->
  P + E != 0.
Proof.
move=> HP HE Heta; apply/eqP => H0.
have := paper_main_head_perturbation_lower _ E HP.
rewrite H0 pmh_frobenius0 => H; lra.
Qed.

Theorem paper_main_head_normalize_close P E (eta : R) :
  paper_main_frobenius P = 1 -> paper_main_frobenius E <= eta -> eta < 1 ->
  paper_main_frobenius (paper_main_head_normalize (P + E) - P) <= 2 * eta.
Proof.
move=> HP HE Heta.
have HQ := paper_main_head_perturbation_nonzero _ _ _ HP HE Heta.
have Hc := pmh_frobenius_gt0 _ _ HQ.
have Hr := pmh_frobenius_reverse_triangle _ P E.
rewrite HP in Hr.
set c := paper_main_frobenius (P + E) in Hc Hr *.
have Hc0 : c != 0 := lt0r_neq0 Hc.
have Hsplit : paper_main_head_normalize (P + E) - P = (c^-1 - 1) *: (P + E) + E.
  by apply/matrixP => i j; rewrite /paper_main_head_normalize -/c !mxE; ring.
rewrite Hsplit.
apply: le_trans (pmh_frobenius_triangle _ _ _) _.
rewrite pmh_frobeniusZ -/c.
have -> : `|c^-1 - 1| * c = `|c - 1|.
  by rewrite -{2}(ger0_norm (ltW Hc)) -normrM mulrBl (mulVf Hc0) mul1r distrC.
lra.
Qed.

Theorem paper_main_head_support_transfer P E Z (eta : R) :
  paper_main_frobenius P = 1 -> paper_main_frobenius E <= eta -> eta < 1 ->
  paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <=
  paper_main_pairing Z (paper_main_head_normalize (P + E)).
Proof.
move=> HP HE Heta.
have Hcl := paper_main_head_normalize_close _ _ _ HP HE Heta.
have Hb := pmh_pairing_frobenius_bound _ Z (paper_main_head_normalize (P + E) - P).
rewrite pmh_pairingBr in Hb.
have HZ := pmh_frobenius_ge0 _ Z.
have H2 : paper_main_frobenius Z *
    paper_main_frobenius (paper_main_head_normalize (P + E) - P) <=
    paper_main_frobenius Z * (2 * eta) by apply: (ler_wpM2l HZ).
move: Hb; rewrite ler_norml => /andP [Hlo _].
nra.
Qed.

(* 3. Loewner spectral slack. *)

Lemma pmh_form_id (v : 'cV[R]_d) : paper_main_quadratic_form 1%:M v = (v^T *m v) 0 0.
Proof. by rewrite paper_main_quadratic_formE mulmx1. Qed.

Lemma pmh_psd_id : paper_main_psd (1%:M : 'M[R]_d).
Proof.
split; first by apply/paper_main_symmetricP; rewrite trmx1.
move=> v; rewrite pmh_form_id pms_sqnorm.
by apply: sumr_ge0 => i _; rewrite -expr2 sqr_ge0.
Qed.

Lemma pmh_psd_scalar (c : R) : 0 <= c -> paper_main_psd (c *: (1%:M : 'M[R]_d)).
Proof. by move=> Hc; apply: paper_main_psd_scale => //; exact: pmh_psd_id. Qed.

Lemma pmh_loewner_add A B C D :
  paper_main_loewner_le A B -> paper_main_loewner_le C D ->
  paper_main_loewner_le (A + C) (B + D).
Proof.
rewrite /paper_main_loewner_le => H1 H2.
by rewrite opprD addrACA; exact: pms_psd_add.
Qed.

Lemma pmh_loewner_trans A B C :
  paper_main_loewner_le A B -> paper_main_loewner_le B C ->
  paper_main_loewner_le A C.
Proof.
rewrite /paper_main_loewner_le => H1 H2.
have -> : C - A = (C - B) + (B - A) by rewrite addrA subrK.
exact: pms_psd_add.
Qed.

Lemma pmh_loewner_scale (c : R) A B :
  0 <= c -> paper_main_loewner_le A B -> paper_main_loewner_le (c *: A) (c *: B).
Proof.
rewrite /paper_main_loewner_le => Hc H; rewrite -scalerBr.
exact: paper_main_psd_scale.
Qed.

Lemma pmh_loewner_scalar (a b : R) :
  a <= b -> paper_main_loewner_le (a *: (1%:M : 'M[R]_d)) (b *: 1%:M).
Proof.
move=> Hab; rewrite /paper_main_loewner_le -scalerBl.
by apply: pmh_psd_scalar; rewrite subr_ge0.
Qed.

Lemma pmh_loewner_pd (c : R) S :
  0 < c -> paper_main_loewner_le (c *: 1%:M) S -> paper_main_pd S.
Proof.
move=> Hc H.
have HS : paper_main_psd S.
  have -> : S = (S - c *: 1%:M) + c *: 1%:M by rewrite subrK.
  by apply: pms_psd_add => //; apply: pmh_psd_scalar; rewrite ltW.
split; first by case: HS.
move=> v Hv.
have -> : paper_main_quadratic_form S v =
    paper_main_quadratic_form (S - c *: 1%:M) v + c * (v^T *m v) 0 0.
  by rewrite pms_formB paper_main_form_scale pmh_form_id subrK.
case: H => _ Hq.
have Hq0 := Hq v.
have Hp := pms_sqnorm_gt0 _ _ Hv.
have Hcp := mulr_gt0 Hc Hp.
lra.
Qed.

Theorem paper_main_head_loewner_slack P E (lm lp delta : R) :
  paper_main_loewner_le (lm *: 1%:M) P -> paper_main_loewner_le P (lp *: 1%:M) ->
  paper_main_loewner_le ((- delta) *: 1%:M) E -> paper_main_loewner_le E (delta *: 1%:M) ->
  paper_main_loewner_le ((lm - delta) *: 1%:M) (P + E) /\
  paper_main_loewner_le (P + E) ((lp + delta) *: 1%:M).
Proof.
move=> H1 H2 H3 H4; split.
- rewrite scalerDl; exact: pmh_loewner_add.
- rewrite scalerDl; exact: pmh_loewner_add.
Qed.

Theorem paper_main_head_loewner_scale S (c lo hi : R) : 0 < c ->
  paper_main_loewner_le (lo *: 1%:M) S -> paper_main_loewner_le S (hi *: 1%:M) ->
  paper_main_loewner_le ((lo / c) *: 1%:M) (c^-1 *: S) /\
  paper_main_loewner_le (c^-1 *: S) ((hi / c) *: 1%:M).
Proof.
move=> Hc H1 H2.
have Hi : 0 <= c^-1 by rewrite invr_ge0 ltW.
have E1 : (lo / c) *: 1%:M = c^-1 *: (lo *: 1%:M) :> 'M[R]_d
  by rewrite scalerA mulrC.
have E2 : (hi / c) *: 1%:M = c^-1 *: (hi *: 1%:M) :> 'M[R]_d
  by rewrite scalerA mulrC.
by rewrite E1 E2; split; apply: pmh_loewner_scale.
Qed.

Theorem paper_main_head_condition_transfer P E (lm lp delta kappa : R) :
  P + E != 0 -> delta < lm -> lp + delta <= kappa * (lm - delta) ->
  paper_main_loewner_le (lm *: 1%:M) P -> paper_main_loewner_le P (lp *: 1%:M) ->
  paper_main_loewner_le ((- delta) *: 1%:M) E -> paper_main_loewner_le E (delta *: 1%:M) ->
  paper_main_head_condition kappa (paper_main_head_normalize (P + E)).
Proof.
move=> HQ Hd Hk H1 H2 H3 H4.
have Hc := pmh_frobenius_gt0 _ _ HQ.
have [L1 L2] := paper_main_head_loewner_slack _ _ _ _ _ H1 H2 H3 H4.
have [N1 N2] := paper_main_head_loewner_scale _ _ _ _ Hc L1 L2.
exists ((lm - delta) / paper_main_frobenius (P + E)); split.
  by rewrite divr_gt0 // subr_gt0.
split; first exact: N1.
apply: pmh_loewner_trans N2 _; apply: pmh_loewner_scalar.
by rewrite mulrA ler_pM2r ?invr_gt0.
Qed.

(* Assembly: the deterministic form of eq:PJ-close and eq:width-transfer. *)

Theorem paper_main_head_correction_transfer W P Z a (eta : R) :
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  paper_main_frobenius P = 1 ->
  paper_main_frobenius (paper_main_head_correction W a) <= eta -> eta < 1 ->
  [/\ paper_main_frobenius (paper_main_head_normalize (P + paper_main_head_correction W a)) = 1,
      (forall i : 'I_m, paper_main_pairing (W i)
         (paper_main_head_normalize (P + paper_main_head_correction W a)) = 0),
      paper_main_frobenius
        (paper_main_head_normalize (P + paper_main_head_correction W a) - P) <= 2 * eta &
      paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <=
        paper_main_pairing Z (paper_main_head_normalize (P + paper_main_head_correction W a))].
Proof.
move=> Ha HP HE Heta; split.
- apply: paper_main_head_normalize_unit.
  exact: (paper_main_head_perturbation_nonzero _ _ _ HP HE Heta).
- move=> i; apply: paper_main_head_normalize_kernel.
  exact: paper_main_head_correction_kernel.
- exact: paper_main_head_normalize_close.
- exact: paper_main_head_support_transfer.
Qed.

Theorem paper_main_head_correction_close W P Z a (eta lm lp delta kappa : R) :
  paper_main_head_gram W *m a = paper_main_head_residual W P ->
  paper_main_frobenius P = 1 ->
  paper_main_frobenius (paper_main_head_correction W a) <= eta -> eta < 1 ->
  delta < lm -> lp + delta <= kappa * (lm - delta) ->
  paper_main_loewner_le (lm *: 1%:M) P -> paper_main_loewner_le P (lp *: 1%:M) ->
  paper_main_loewner_le ((- delta) *: 1%:M) (paper_main_head_correction W a) ->
  paper_main_loewner_le (paper_main_head_correction W a) (delta *: 1%:M) ->
  let Pt := paper_main_head_normalize (P + paper_main_head_correction W a) in
  [/\ paper_main_head_condition kappa Pt, paper_main_frobenius Pt = 1,
      (forall i : 'I_m, paper_main_pairing (W i) Pt = 0),
      paper_main_frobenius (Pt - P) <= 2 * eta &
      paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <= paper_main_pairing Z Pt].
Proof.
move=> Ha HP HE Heta Hd Hk H1 H2 H3 H4 Pt.
have [U K Cl T] := paper_main_head_correction_transfer _ _ Z _ _ Ha HP HE Heta.
split => //.
apply: (paper_main_head_condition_transfer _ _ _ _ _ _ _ Hd Hk H1 H2 H3 H4).
exact: (paper_main_head_perturbation_nonzero _ _ _ HP HE Heta).
Qed.

End HeadCorrection.
