(* Entry-level coefficient bounds of the exact head correction, the
   deterministic core of eq:aJ-l1 and eq:aJ-linf in the proof of
   lem:head-correction-bounds (manuscript lines 1005-1017).

   For any family F : 'I_m -> R, (sum_i F i)^2 <= m sum_i F i^2; hence
   |a|_1^2 <= m |a|_2^2 (eq:aJ-l1). If Q a = r, Q_ii >= q0 >= 0 and
   |Q_ij| <= q1 for j <> i (with q1 >= 0), then
   q0 |a_i| <= |r_i| + q1 |a|_1, from Q_ii a_i = r_i - sum_(j <> i) Q_ij a_j
   (eq:aJ-linf). With the coercive Gram bound of
   PaperMainGeometryHeadCoefficients these give the constants A_1 and A_inf
   of PaperMainGeometryHeadFeature.

   paper_main_head_correction_bounds assembles the deterministic core of
   the whole lemma on the features W_i = (x_i x_i^T - I) / sqrt d.
   Its inputs are the data-event quantities, all hypotheses: the lower
   edge of the full feature Gram matrix (coercivity with mu > 0), the
   diagonal and off-diagonal Gram entry bounds q0 > 0 and q1, the residual
   bound |r_(s k)| <= Rd, and X_J X_J^T <= lam I. For constants with
   m Rd^2 <= mu eta^2, m Rd <= mu A_1, Rd + q1 A_1 <= q0 A_inf,
   (A_inf lam + A_1) / sqrt d <= delta, eta < 1, delta < lm and
   lp + delta <= kappa (lm - delta), the exact correction a = Q^-1 r of every
   injective head s gives eq:PJ-close and the support transfer behind
   eq:width-transfer. In the paper these inputs come from cor:feature-sat,
   lem:data, eq:sparse-norms and eq:Rd, which are not proved here. *)
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
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadCoefficients PaperMainGeometryHeadPrincipal
  PaperMainGeometryHeadFeature.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Entries.
Variable m : nat.
Implicit Types (Q : 'M[R]_m) (a r : 'cV[R]_m).

Lemma pmh_sum_const (c : R) : \sum_(j < m) c = m%:R * c.
Proof. by rewrite sumr_const card_ord mulr_natl. Qed.

Lemma pmh_sum_sqr_le (F : 'I_m -> R) :
  (\sum_(i < m) F i) ^+ 2 <= m%:R * \sum_(i < m) F i ^+ 2.
Proof.
have H0 : 0 <= \sum_(i < m) \sum_(j < m) (F i - F j) ^+ 2.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; exact: sqr_ge0.
have Hin : forall i, \sum_(j < m) (F i - F j) ^+ 2 =
    m%:R * F i ^+ 2 - 2 * F i * (\sum_(j < m) F j) + \sum_(j < m) F j ^+ 2.
  move=> i.
  have -> : \sum_(j < m) (F i - F j) ^+ 2 =
      \sum_(j < m) (F i ^+ 2 - 2 * F i * F j + F j ^+ 2).
    by apply: eq_bigr => j _; ring.
  by rewrite big_split sumrB /= pmh_sum_const -mulr_sumr.
have Hout : \sum_(i < m) \sum_(j < m) (F i - F j) ^+ 2 =
    2 * (m%:R * \sum_(i < m) F i ^+ 2 - (\sum_(i < m) F i) ^+ 2).
  rewrite (eq_bigr _ (fun i _ => Hin i)) big_split sumrB /= pmh_sum_const.
  rewrite -mulr_sumr -mulr_suml.
  have -> : \sum_(i < m) 2 * F i = 2 * \sum_(i < m) F i by rewrite mulr_sumr.
  ring.
rewrite Hout in H0; nra.
Qed.

(* eq:aJ-l1. *)
Theorem paper_main_head_coefficients_l1 a :
  (\sum_(i < m) `|a i 0|) ^+ 2 <= m%:R * (a^T *m a) 0 0.
Proof.
apply: le_trans (pmh_sum_sqr_le (fun i => `|a i 0|)) _ => /=.
rewrite pmh_vec_dot.
under eq_bigr do rewrite (real_normK (num_real _)) expr2.
exact: lexx.
Qed.

(* eq:aJ-linf, multiplied by q0. *)
Theorem paper_main_head_coefficients_linf Q a r (q0 q1 : R) (i : 'I_m) :
  Q *m a = r -> 0 <= q0 -> q0 <= Q i i -> 0 <= q1 ->
  (forall j, j != i -> `|Q i j| <= q1) ->
  q0 * `|a i 0| <= `|r i 0| + q1 * \sum_(j < m) `|a j 0|.
Proof.
move=> Ha Hq0 Hd Hq1 Hoff.
have Hi : (Q *m a) i 0 = r i 0 by rewrite Ha.
rewrite mxE (bigD1 i) //= in Hi.
have Hsum : `|\sum_(j < m | j != i) Q i j * a j 0| <= q1 * \sum_(j < m) `|a j 0|.
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: (@le_trans _ _ (\sum_(j < m | j != i) q1 * `|a j 0|)).
    apply: ler_sum => j Hj; rewrite normrM.
    exact: (ler_wpM2r (normr_ge0 _) (Hoff j Hj)).
  rewrite -mulr_sumr; apply: (ler_wpM2l Hq1).
  rewrite [X in _ <= X](bigD1 i) //= lerDr; exact: normr_ge0.
have HQ : 0 <= Q i i by exact: le_trans Hq0 Hd.
have Hrow : Q i i * a i 0 = r i 0 - \sum_(j < m | j != i) Q i j * a j 0.
  by rewrite -Hi addrK.
have Hn : Q i i * `|a i 0| <= `|r i 0| + `|\sum_(j < m | j != i) Q i j * a j 0|.
  rewrite -(ger0_norm HQ) -normrM Hrow.
  by apply: le_trans (ler_normD _ _) _; rewrite normrN.
have Hm := ler_wpM2r (normr_ge0 (a i 0)) Hd.
lra.
Qed.

End Entries.

(* The deterministic core of lem:head-correction-bounds on the features. *)
Theorem paper_main_head_correction_bounds n d m (x : paper_main_sample n d)
    (s : 'I_m -> 'I_n) (P Z : 'M[R]_d)
    (mu q0 q1 Rd lam eta A_1 A_inf delta lm lp kappa : R) :
  injective s -> 0 < mu ->
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
  delta < lm -> lp + delta <= kappa * (lm - delta) ->
  paper_main_frobenius P = 1 ->
  paper_main_loewner_le (lm *: 1%:M) P -> paper_main_loewner_le P (lp *: 1%:M) ->
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
move=> Hs Hmu HG Hq0 Hdiag Hq1 Hoff HRd0 HRd Hlam Heta2 Heta0 Heta HA1 HAinf Hdel
  Hd Hk HP H1 H2 W Pt.
have HQ : paper_main_head_coercive (paper_main_head_gram W) mu
  by exact: (paper_main_head_sub_coercive _ _ _ _ _ _ Hs HG).
have HU := paper_main_head_gram_coercive_unit _ _ _ _ Hmu HQ.
have Ha := paper_main_head_coefficients_solve _ _ _ P HU.
set a := paper_main_head_coefficients W P in Ha *.
set r := paper_main_head_residual W P in Ha *.
have Hrk : forall k : 'I_m, `|r k 0| <= Rd by move=> k; rewrite /r mxE; exact: HRd.
have Hr : (r^T *m r) 0 0 <= m%:R * Rd ^+ 2.
  rewrite pmh_vec_dot -pmh_sum_const; apply: ler_sum => k _.
  rewrite -expr2 -(real_normK (num_real _)).
  have := Hrk k; have := normr_ge0 (r k 0); nra.
(* |E|_F <= eta *)
have HE := paper_main_head_correction_energy _ _ _ _ _ _ Hmu HQ Ha.
have Hf := pmh_frobenius_ge0 _ (paper_main_head_correction W a).
have Hsq : paper_main_frobenius (paper_main_head_correction W a) ^+ 2 <= eta ^+ 2.
  rewrite -(ler_pM2l Hmu).
  by apply: le_trans HE _; apply: le_trans Hr Heta2.
have HEeta : paper_main_frobenius (paper_main_head_correction W a) <= eta by nra.
(* |a|_1 <= A_1 *)
have Ha2 := paper_main_head_coefficients_bound _ _ _ _ _ _ Hmu HQ Ha.
have Hl1 := paper_main_head_coefficients_l1 _ a.
have Hn1 : 0 <= \sum_(k < m) `|a k 0| by apply: sumr_ge0 => k _; exact: normr_ge0.
have Hm0 : 0 <= m%:R :> R by exact: ler0n.
have Hl1b : mu * \sum_(k < m) `|a k 0| <= m%:R * Rd.
  have Hsq1 : (mu * \sum_(k < m) `|a k 0|) ^+ 2 <= (m%:R * Rd) ^+ 2.
    rewrite !exprMn.
    have Ham := ler_wpM2l (sqr_ge0 mu) Hl1.
    have Hbb : mu ^+ 2 * (a^T *m a) 0 0 <= m%:R * Rd ^+ 2 by exact: le_trans Ha2 Hr.
    have := ler_wpM2l Hm0 Hbb; nra.
  have Hp : 0 <= m%:R * Rd by exact: mulr_ge0.
  have Hl : 0 <= mu * \sum_(k < m) `|a k 0| by apply: mulr_ge0 => //; exact: ltW.
  nra.
have HA1' : \sum_(k < m) `|a k 0| <= A_1.
  by rewrite -(ler_pM2l Hmu); exact: le_trans Hl1b HA1.
(* |a_k| <= A_inf *)
have HAk : forall k : 'I_m, `|a k 0| <= A_inf.
  move=> k.
  have Hdk : q0 <= paper_main_head_gram W k k by rewrite /paper_main_head_gram mxE; exact: Hdiag.
  have Hok : forall l, l != k -> `|paper_main_head_gram W k l| <= q1.
    by move=> l Hl; rewrite /paper_main_head_gram mxE; exact: Hoff.
  have Hli := paper_main_head_coefficients_linf _ _ _ _ _ _ k Ha (ltW Hq0) Hdk Hq1 Hok.
  have Hq1A := ler_wpM2l Hq1 HA1'.
  rewrite -(ler_pM2l Hq0).
  have := Hrk k; lra.
have HA0 : 0 <= A_inf.
  have Hq1A1 : 0 <= q1 * A_1 by apply: mulr_ge0 => //; exact: le_trans Hn1 HA1'.
  have : 0 <= q0 * A_inf by lra.
  by rewrite pmulr_rge0.
have [C U K Cl T] := paper_main_head_feature_close _ _ _ _ _ _ Z _ _ _ _ _ _ _ _ _ Ha HP HEeta Heta HA0
  HAk HA1' Hlam Hdel Hd Hk H1 H2.
by split.
Qed.
