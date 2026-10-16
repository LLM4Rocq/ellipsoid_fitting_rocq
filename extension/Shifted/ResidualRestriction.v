(* Restrict the frozen fitting error to the trailing coordinates.
   In dimension d=1+p, the zero-head embedding of a PSD trace-p matrix,
   scaled by d/p, has trace d. Scaling the nonnegative fitted level by
   sqrt(d)/sqrt(p) multiplies the complete squared objective by d/p.
   Comparing the infima gives the restriction bound for every sample,
   including the empty sample. No law or rotation assumption is used. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology normedtype.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.matrix Require Import euclidean psd_part psd_splitting.
From GaussianAnalysis.matrix Require Import psd_factorization condition_perturbation.
From GaussianAnalysis.probability Require Import tuple_rows.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality.Gaussian Require Import Limit Representation.
From EllipsoidUniversality.Shifted Require Import GaussianRows.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Definition sample_trailing n p (x : paper_main_sample n (1+p)) :
    paper_main_sample n p :=
  sample_of_row_tuple
    (tuple_map (fun _ (z : 'rV[RR]_(1+p)) => rsubmx z) (sample_row_tuple x)).

Lemma sample_trailing_point n p (x : paper_main_sample n (1+p)) (i : 'I_n) :
  paper_main_point (sample_trailing x) i = dsubmx (paper_main_point x i).
Proof.
have hi := congr1 (fun z : n.-tuple 'rV[RR]_p => tnth z i)
  (sample_of_row_tupleK
    (tuple_map (fun _ (z : 'rV[RR]_(1+p)) => rsubmx z) (sample_row_tuple x))).
have ht : (paper_main_point (sample_trailing x) i)^T =
    rsubmx (paper_main_point x i)^T.
  by move: hi; rewrite /sample_row_tuple /tuple_map !tnth_mktuple.
by move: (congr1 trmx ht); rewrite trmxK trmx_rsub trmxK.
Qed.

Section restriction_scalars.
Variable F : realType.

Lemma restriction_sqrt_ratio_pos (u v : F) : 0 < u -> 0 < v ->
  0 < Num.sqrt u / Num.sqrt v.
Proof. by move=> u0 v0; rewrite divr_gt0 ?sqrtr_gt0. Qed.

Lemma restriction_sqrt_ratio_sqr (u v : F) : 0 <= u -> 0 <= v ->
  (Num.sqrt u / Num.sqrt v)^+2 = u/v.
Proof. by move=> u0 v0; rewrite expr_div_n !sqr_sqrtr. Qed.

Lemma restriction_residual_scale (u v q r : F) : 0 < u -> 0 < v ->
  (u/v)*q/Num.sqrt u - (Num.sqrt u/Num.sqrt v)*r =
    (Num.sqrt u/Num.sqrt v)*(q/Num.sqrt v-r).
Proof.
move=> u0 v0.
have suN : Num.sqrt u != 0 by rewrite gt_eqF // sqrtr_gt0.
have svN : Num.sqrt v != 0 by rewrite gt_eqF // sqrtr_gt0.
have ue : u = (Num.sqrt u)^+2 by rewrite sqr_sqrtr // ltW.
have ve : v = (Num.sqrt v)^+2 by rewrite sqr_sqrtr // ltW.
rewrite {1}ue {1}ve; field.
Qed.

Lemma restriction_infimum_le_scaled (A B : set F) (c : F) :
  has_lbound A -> B !=set0 -> 0 < c ->
  (forall b, B b -> A (c*b)) -> inf A <= c*inf B.
Proof.
move=> Alb Bn c0 emb; rewrite mulrC -ler_pdivrMr //.
apply: lb_le_inf Bn _ => b Bb.
rewrite ler_pdivrMr // mulrC.
exact: (ge_inf Alb (emb b Bb)).
Qed.

End restriction_scalars.

Definition residual_embed p (S : 'M[R]_p) : 'M[R]_(1+p) :=
  ((1+p)%:R / p%:R) *: block_mx (0 : 'M[R]_1) 0 0 S.

Lemma residual_embed_psdmx p (S : 'M[R]_p) :
  psdmx S -> psdmx (residual_embed S).
Proof.
move=> Sp; apply: psdmxZ.
- by rewrite divr_ge0 // ler0n.
- apply: psdmx_block_diag => //.
  exact: psdmx0.
Qed.

Lemma residual_embed_psd p (S : 'M[R]_p) :
  paper_main_psd S -> paper_main_psd (residual_embed S).
Proof.
move=> /paper_psdP Sp; apply/paper_psdP.
exact: residual_embed_psdmx Sp.
Qed.

Lemma residual_embed_trace p (S : 'M[R]_p) :
  (0 < p)%N -> paper_main_trace S = p%:R ->
  paper_main_trace (residual_embed S) = (1+p)%:R.
Proof.
move=> p0 St.
have pn : (p%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite !paper_traceE /residual_embed mxtraceZ mxtrace_block mxtrace0 add0r
  -paper_traceE St mulfVK.
Qed.

Lemma residual_embed_slice p (S : 'M[R]_p) :
  (0 < p)%N -> psd_trace_slice p S ->
  psd_trace_slice (1+p) (residual_embed S).
Proof.
move=> p0 [Sp St]; split.
- exact: residual_embed_psd Sp.
- exact: residual_embed_trace p0 St.
Qed.

Lemma residual_embed_quadratic p (S : 'M[R]_p) (x : 'cV[R]_(1+p)) :
  paper_main_quadratic_form (residual_embed S) x =
  ((1+p)%:R / p%:R) * paper_main_quadratic_form S (dsubmx x).
Proof.
rewrite /residual_embed !paper_quadratic_mxdot -scalemxAl mxdotZr.
congr (_ * _).
by rewrite -[x](@vsubmxK _ 1 p 1) quadratic_block_diag mul0mx
  mxdot0r add0r col_mxKd.
Qed.

Definition restriction_objective {n d} (x : paper_main_sample n d)
    (S : 'M[R]_d) (r : R) : RR :=
  (\sum_(i < n)
    (paper_main_quadratic_form S (paper_main_point x i) / Num.sqrt d%:R - r)^+2)
  / n%:R.

Lemma restriction_objective_nonnegative n d (x : paper_main_sample n d)
    (S : 'M[R]_d) (r : R) : 0 <= restriction_objective x S r.
Proof.
rewrite /restriction_objective divr_ge0 // sumr_ge0 // => i _.
exact: sqr_ge0.
Qed.

Lemma restriction_objective_embed n p (x : paper_main_sample n (1+p))
    (g : paper_main_sample n p) (S : 'M[R]_p) (r : R) :
  (0 < p)%N ->
  (forall i : 'I_n, dsubmx (paper_main_point x i) = paper_main_point g i) ->
  restriction_objective x (residual_embed S)
    ((Num.sqrt (1+p)%:R / Num.sqrt p%:R) * r) =
  ((1+p)%:R / p%:R) * restriction_objective g S r.
Proof.
move=> p0 trailing.
have pr0 : (0 : RR) < p%:R by rewrite ltr0n.
have dr0 : (0 : RR) < (1+p)%:R by rewrite ltr0n add1n.
rewrite /restriction_objective.
under eq_bigr do rewrite residual_embed_quadratic trailing
  (restriction_residual_scale _ _ dr0 pr0) exprMn
  (restriction_sqrt_ratio_sqr (ltW dr0) (ltW pr0)).
by rewrite -mulr_sumr mulrA.
Qed.

Theorem fitting_error_restriction n p (x : paper_main_sample n (1+p))
    (g : paper_main_sample n p) :
  (0 < p)%N ->
  (forall i : 'I_n, dsubmx (paper_main_point x i) = paper_main_point g i) ->
  universality_fitting_error n (1+p) x <=
    ((1+p)%:R / p%:R) * universality_fitting_error n p g.
Proof.
move=> p0 trailing; rewrite /universality_fitting_error.
apply: restriction_infimum_le_scaled.
- exists 0 => v [S [r [Sp [St [r0 ->]]]]].
  exact: restriction_objective_nonnegative.
- exists (restriction_objective g 1%:M 0), 1%:M, 0.
  have [Ipsd Itr] := psd_trace_slice1 p.
  by split; [exact: Ipsd | split; [exact: Itr | split]].
- by rewrite divr_gt0 // ltr0n // add1n.
- move=> v [S [r [Sp [St [r0 ->]]]]].
  exists (residual_embed S), ((Num.sqrt (1+p)%:R / Num.sqrt p%:R) * r).
  split; first exact: residual_embed_psd Sp.
  split; first exact: residual_embed_trace p0 St.
  split.
  - by apply: mulr_ge0; rewrite // divr_ge0 ?sqrtr_ge0.
  - symmetry; exact: restriction_objective_embed p0 trailing.
Qed.

Corollary fitting_error_trailing n p (x : paper_main_sample n (1+p)) :
  (0 < p)%N ->
  universality_fitting_error n (1+p) x <=
    ((1+p)%:R / p%:R) * universality_fitting_error n p (sample_trailing x).
Proof.
move=> p0; apply: fitting_error_restriction p0 _ => i.
by rewrite sample_trailing_point.
Qed.
