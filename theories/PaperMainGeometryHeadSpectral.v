(* The spectral box of a unit element of the bounded-condition cone, in
   Loewner form: the deterministic fact eq:P-eigen-generic used for
   eq:DJ-box and eq:P-eigen (manuscript, the paragraph opening the proof of
   prop:heads).

   If lam I <= S <= kappa lam I with lam > 0 and |S|_F = 1, then
   (kappa sqrt d)^-1 I <= S <= (kappa / sqrt d) I. The proof avoids
   eigenvalues. <A, B> >= 0 for positive semidefinite A and B (from the
   rank-one decomposition paper_main_psd_decomp), so
   d lam <= Tr S <= d mu and lam Tr S <= |S|_F^2 <= mu Tr S for
   lam I <= S <= mu I with lam >= 0; hence d lam^2 <= 1 <= d kappa^2 lam^2.
   With paper_main_head_condition this gives the box hypothesis
   lm I <= P <= lp I of paper_main_head_correction_bounds for
   lm = (kappa_0 sqrt d)^-1 and lp = kappa_0 / sqrt d.
   paper_main_head_correction_bounds_cone is that combination: the
   hypothesis on P is the paper's P in K_(kappa_0) with |P|_F = 1. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryGram PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadFeature
  PaperMainGeometryHeadEntries.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Spectral.
Variable d : nat.
Implicit Types (A B S : 'M[R]_d).

Theorem pmh_pairing_psd_ge0 A B :
  paper_main_psd A -> paper_main_psd B -> 0 <= paper_main_pairing A B.
Proof.
move=> HA [_ HB].
have [m [w E]] := paper_main_psd_decomp d A HA.
have -> : A = \sum_(i < m) 1 *: (w i *m (w i)^T).
  by rewrite E; apply: eq_bigr => i _; rewrite scale1r.
rewrite paper_main_pairingC paper_main_pairing_sum.
apply: sumr_ge0 => i _; rewrite mul1r paper_main_pairing_outer.
exact: HB.
Qed.

Lemma pmh_trace_id : paper_main_trace (1%:M : 'M[R]_d) = d%:R.
Proof.
rewrite /paper_main_trace; under eq_bigr do rewrite mxE eqxx.
by rewrite sumr_const card_ord.
Qed.

Lemma pmh_trace_scalar (c : R) : paper_main_trace (c *: (1%:M : 'M[R]_d)) = c * d%:R.
Proof. by rewrite pms_trace_scale pmh_trace_id. Qed.

Lemma pmh_trace_psd_ge0 S : paper_main_psd S -> 0 <= paper_main_trace S.
Proof.
move=> HS; rewrite -pmh_pairing_id.
by apply: pmh_pairing_psd_ge0 => //; exact: pmh_psd_id.
Qed.

Lemma pmh_loewner_trace_lower S (lam : R) :
  paper_main_loewner_le (lam *: 1%:M) S -> lam * d%:R <= paper_main_trace S.
Proof.
move=> H; have := pmh_trace_psd_ge0 _ H.
by rewrite pms_traceB pmh_trace_scalar subr_ge0.
Qed.

Lemma pmh_loewner_trace_upper S (mu : R) :
  paper_main_loewner_le S (mu *: 1%:M) -> paper_main_trace S <= mu * d%:R.
Proof.
move=> H; have := pmh_trace_psd_ge0 _ H.
by rewrite pms_traceB pmh_trace_scalar subr_ge0.
Qed.

Lemma pmh_loewner_psd S (lam : R) :
  0 <= lam -> paper_main_loewner_le (lam *: 1%:M) S -> paper_main_psd S.
Proof.
move=> Hl H.
have -> : S = (S - lam *: 1%:M) + lam *: 1%:M by rewrite subrK.
by apply: pms_psd_add => //; exact: pmh_psd_scalar.
Qed.

Theorem pmh_loewner_frobenius_lower S (lam : R) :
  0 <= lam -> paper_main_loewner_le (lam *: 1%:M) S ->
  lam * paper_main_trace S <= paper_main_frobenius S ^+ 2.
Proof.
move=> Hl H.
have HS := pmh_loewner_psd _ _ Hl H.
have := pmh_pairing_psd_ge0 _ _ H HS.
rewrite pmh_pairingBl pmh_pairingZl pmh_pairing_id pmh_frobenius_sqr subr_ge0.
done.
Qed.

Theorem pmh_loewner_frobenius_upper S (mu : R) :
  paper_main_psd S -> paper_main_loewner_le S (mu *: 1%:M) ->
  paper_main_frobenius S ^+ 2 <= mu * paper_main_trace S.
Proof.
move=> HS H.
have := pmh_pairing_psd_ge0 _ _ H HS.
rewrite pmh_pairingBl pmh_pairingZl pmh_pairing_id pmh_frobenius_sqr subr_ge0.
done.
Qed.

(* eq:P-eigen-generic in Loewner form. *)
Theorem paper_main_head_spectral_box S (lam kappa : R) :
  (0 < d)%N -> 0 < lam ->
  paper_main_loewner_le (lam *: 1%:M) S ->
  paper_main_loewner_le S ((kappa * lam) *: 1%:M) ->
  paper_main_frobenius S = 1 ->
  paper_main_loewner_le ((kappa * Num.sqrt d%:R)^-1 *: 1%:M) S /\
  paper_main_loewner_le S ((kappa / Num.sqrt d%:R) *: 1%:M).
Proof.
move=> Hd Hl H1 H2 HF.
have HS := pmh_loewner_psd _ _ (ltW Hl) H1.
have Tl := pmh_loewner_trace_lower _ _ H1.
have Tu := pmh_loewner_trace_upper _ _ H2.
have Fl := pmh_loewner_frobenius_lower _ _ (ltW Hl) H1.
have Fu := pmh_loewner_frobenius_upper _ _ HS H2.
rewrite HF expr1n in Fl Fu.
have Hdp : 0 < d%:R :> R by rewrite ltr0n.
set sd := Num.sqrt d%:R.
have Hs : 0 < sd by rewrite /sd sqrtr_gt0.
have Hs2 : sd ^+ 2 = d%:R by rewrite /sd sqr_sqrtr // ltW.
(* d lam^2 <= 1 and 1 <= d (kappa lam)^2 *)
have Hlo : lam ^+ 2 * d%:R <= 1.
  have := ler_wpM2l (ltW Hl) Tl; nra.
have Hk : 0 < kappa.
  have Htr : 0 <= paper_main_trace S by exact: pmh_trace_psd_ge0.
  have Hku : 0 < kappa * lam by nra.
  by move: Hku; rewrite pmulr_lgt0.
have Hhi : 1 <= (kappa * lam) ^+ 2 * d%:R.
  have := ler_wpM2l (ltW (mulr_gt0 Hk Hl)) Tu; nra.
have Hl1 : lam * sd <= 1 by nra.
have Ht : (kappa * lam * sd) ^+ 2 = (kappa * lam) ^+ 2 * d%:R by rewrite exprMn Hs2.
have Ht0 : 0 <= kappa * lam * sd.
  by apply: mulr_ge0; [apply: mulr_ge0; exact: ltW | exact: ltW].
have Hl2 : 1 <= kappa * lam * sd by nra.
split.
- apply: pmh_loewner_trans H1; apply: pmh_loewner_scalar.
  have Hks : 0 < kappa * sd by exact: mulr_gt0.
  rewrite -(mul1r ((kappa * sd)^-1)) ler_pdivrMr //; nra.
- apply: pmh_loewner_trans H2 _; apply: pmh_loewner_scalar.
  rewrite ler_pdivlMr //; nra.
Qed.

End Spectral.

(* The spectral box of a unit element of the bounded-condition cone. *)
Corollary paper_main_head_condition_box d (S : 'M[R]_d) (kappa : R) :
  (0 < d)%N -> paper_main_head_condition kappa S -> paper_main_frobenius S = 1 ->
  paper_main_loewner_le ((kappa * Num.sqrt d%:R)^-1 *: 1%:M) S /\
  paper_main_loewner_le S ((kappa / Num.sqrt d%:R) *: 1%:M).
Proof.
move=> Hd [lam [Hl [H1 H2]]] HF.
exact: (paper_main_head_spectral_box _ _ _ _ Hd Hl H1 H2 HF).
Qed.

(* paper_main_head_correction_bounds with the paper's hypothesis on P:
   P in K_(kappa_0) with |P|_F = 1 (eq:P-eigen). *)
Theorem paper_main_head_correction_bounds_cone n d m (x : paper_main_sample n d)
    (s : 'I_m -> 'I_n) (P Z : 'M[R]_d)
    (mu q0 q1 Rd lam eta A_1 A_inf delta kappa0 kappa : R) :
  (0 < d)%N -> injective s -> 0 < mu ->
  paper_main_head_coercive
    (paper_main_head_gram (fun i : 'I_n => paper_main_head_feature x i)) mu ->
  0 < q0 ->
  (forall k : 'I_m, q0 <= paper_main_pairing (paper_main_head_feature x (s k))
                              (paper_main_head_feature x (s k))) ->
  0 <= q1 ->
  (forall k l : 'I_m, l != k ->
     `|paper_main_pairing (paper_main_head_feature x (s k))
                          (paper_main_head_feature x (s l))| <= q1) ->
  0 <= Rd ->
  (forall k : 'I_m, `|paper_main_pairing (paper_main_head_feature x (s k)) P| <= Rd) ->
  paper_main_loewner_le (paper_main_head_data_gram x s) (lam *: 1%:M) ->
  m%:R * Rd ^+ 2 <= mu * eta ^+ 2 -> 0 <= eta -> eta < 1 ->
  m%:R * Rd <= mu * A_1 -> Rd + q1 * A_1 <= q0 * A_inf ->
  (Num.sqrt d%:R)^-1 * (A_inf * lam + A_1) <= delta ->
  delta < (kappa0 * Num.sqrt d%:R)^-1 ->
  kappa0 / Num.sqrt d%:R + delta <= kappa * ((kappa0 * Num.sqrt d%:R)^-1 - delta) ->
  paper_main_head_condition kappa0 P -> paper_main_frobenius P = 1 ->
  let W := fun k : 'I_m => paper_main_head_feature x (s k) in
  let Pt := paper_main_head_normalize
    (P + paper_main_head_correction W (paper_main_head_coefficients W P)) in
  paper_main_head_gram W \in unitmx /\
  [/\ paper_main_head_condition kappa Pt, paper_main_frobenius Pt = 1,
      (forall k : 'I_m, paper_main_quadratic_form Pt (paper_main_point x (s k)) =
         paper_main_trace Pt),
      paper_main_frobenius (Pt - P) <= 2 * eta &
      paper_main_pairing Z P - 2 * eta * paper_main_frobenius Z <= paper_main_pairing Z Pt].
Proof.
move=> Hd Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel
  Hlm Hk HC HP W Pt.
have [B1 B2] := paper_main_head_condition_box _ _ _ Hd HC HP.
exact: (paper_main_head_correction_bounds _ _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ _ _ _ Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam
  Heta2 Heta0 Heta HA1 HAinf Hdel Hlm Hk HP B1 B2).
Qed.
