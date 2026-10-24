(* Normalization bridge for the deterministic quadric certificate.
   The existing fitting error divides squared quadratic residuals by n*d.
   A certificate with margin t and squared weight norm w2 therefore gives
   the lower bound d*t^2/(n*w2). No probability assertion is made here. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean psd_part quadric_certificate.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Unsat Require Import LeastSquares.
From EllipsoidUniversality.Gaussian Require Import Limit Representation.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma certificate_normalize (d n w s t : R) :
  0 < d -> 0 < n -> 0 < w ->
  (t * d) ^+ 2 <= w * (d * s) ->
  d * t ^+ 2 / (n * w) <= s / n.
Proof.
move=> d0 n0 w0 h.
have h1 : d * (d * t ^+ 2) <= d * (s * w).
  have e1 : d * (d * t ^+ 2) = (t * d) ^+ 2 by ring.
  have e2 : d * (s * w) = w * (d * s) by ring.
  by rewrite e1 e2.
rewrite ler_pM2l // in h1.
rewrite invfM mulrA ler_pdivrMr //.
have -> : s / n * w = s * w / n by ring.
by rewrite ler_pdivrMr // mulfVK // gt_eqF.
Qed.

Lemma sample_certificate_candidate n d (x : paper_main_sample n d)
    (w : 'I_n -> R) (t : R) (Q : 'M[R]_d) (r : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= t ->
  0 < \sum_(i < n) (w i) ^+ 2 ->
  \sum_(i < n) w i = 0 -> \sum_(i < n) w i *: paper_main_point x i = 0 ->
  psdmx (weighted_outer w (fun i : 'I_n => paper_main_point x i) - t%:M) ->
  paper_main_psd Q -> paper_main_trace Q = d%:R ->
  d%:R * t ^+ 2 / (n%:R * \sum_(i < n) (w i) ^+ 2) <=
    (\sum_(i < n) (paper_main_quadratic_form Q (paper_main_point x i) /
      Num.sqrt d%:R - r) ^+ 2) / n%:R.
Proof.
move=> n0 d0 t0 w2 w0 wx0 H Qp Qtr.
have Qp' : psdmx Q by exact/paper_psdP.
have dr0 : (0 : R) < d%:R by rewrite ltr0n.
have nr0 : (0 : R) < n%:R by rewrite ltr0n.
pose sd : R := Num.sqrt d%:R.
have sd0 : 0 < sd by rewrite /sd sqrtr_gt0.
have sdn : sd != 0 := lt0r_neq0 sd0.
have hc := @quadric_certificate_residual RR _ d w
  (fun i : 'I_n => paper_main_point x i) t Q 0 (- (sd * r)) w0 wx0 t0 Qp' H.
rewrite -paper_traceE Qtr in hc.
have he i : quadric_eval Q 0 (- (sd * r)) (paper_main_point x i) =
    sd * (paper_main_quadratic_form Q (paper_main_point x i) / sd - r).
  rewrite /quadric_eval mxdot0l addr0 -paper_quadratic_mxdot.
  by field.
have hs : \sum_(i < n) (quadric_eval Q 0 (- (sd * r)) (paper_main_point x i)) ^+ 2 =
    d%:R * \sum_(i < n) (paper_main_quadratic_form Q (paper_main_point x i) / sd - r) ^+ 2.
  under eq_bigr do rewrite he exprMn.
  by rewrite -mulr_sumr /sd sqr_sqrtr // ler0n.
rewrite hs in hc.
exact: certificate_normalize dr0 nr0 w2 hc.
Qed.

Theorem sample_certificate_error n d (x : paper_main_sample n d)
    (w : 'I_n -> R) (t : R) :
  (0 < n)%N -> (0 < d)%N -> 0 <= t ->
  0 < \sum_(i < n) (w i) ^+ 2 ->
  \sum_(i < n) w i = 0 -> \sum_(i < n) w i *: paper_main_point x i = 0 ->
  psdmx (weighted_outer w (fun i : 'I_n => paper_main_point x i) - t%:M) ->
  d%:R * t ^+ 2 / (n%:R * \sum_(i < n) (w i) ^+ 2) <=
    universality_fitting_error n d x.
Proof.
move=> n0 d0 t0 w2 w0 wx0 H.
rewrite /universality_fitting_error.
apply: lb_le_inf => [|v [Q [r [Qp [Qtr [r0 ->]]]]]].
- exists ((\sum_(i < n)
    (paper_main_quadratic_form 1%:M (paper_main_point x i) /
      Num.sqrt d%:R - 0) ^+ 2) / n%:R), 1%:M, 0.
  have [Ipsd Itr] := psd_trace_slice1 d.
  by split; [exact: Ipsd | split; [exact: Itr | split]].
exact: sample_certificate_candidate n0 d0 t0 w2 w0 wx0 H Qp Qtr.
Qed.
