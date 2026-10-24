From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp classical_sets reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm condition_cone.
From GaussianAnalysis.convex Require Import logdet_barrier.

(**md**************************************************************************)
(* # Condition numbers under additive and block perturbations                *)
(*                                                                            *)
(* Trace normalization supplies a common spectral scale t, not merely the    *)
(* separate bounds 1/D and D. Keeping t gives a condition bound tending to D  *)
(* as the perturbation vanishes. No commutation hypothesis is required.       *)
(*                                                                            *)
(* condition_perturbation_bound D e == D + (D+1)e/(1/D-e)                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section additive_condition.
Variable R : realType.

Definition condition_perturbation_bound (D e : R) :=
  D + (D + 1) * e / (D^-1 - e).

Lemma symmetric_add_form n (A E : 'M[R]_n) (D t e : R) :
  E \is symmetricmx -> 0 <= e -> opnorm E <= e ->
  (forall x : 'cV[R]_n,
    t * mxdot x x <= mxdot x (A *m x) <= D * t * mxdot x x) ->
  forall x : 'cV[R]_n,
    (t - e) * mxdot x x <= mxdot x ((A + E) *m x) <=
      (D * t + e) * mxdot x x.
Proof.
move=> Es e0 Ee hA x.
have /andP[ha hb] := hA x.
have := (opnorm_symP Es e0).2 Ee x.
rewrite ler_norml => /andP[he hf].
rewrite mulmxDl mxdotDr; apply/andP; split; nra.
Qed.

Lemma condition_perturbation_ratio (D t e : R) :
  1 <= D -> D^-1 <= t -> 0 <= e -> e < D^-1 ->
  (D * t + e) / (t - e) <= condition_perturbation_bound D e.
Proof.
move=> D1 Dt e0 eD.
have D0 : 0 < D := lt_le_trans ltr01 D1.
have te : 0 < t - e by rewrite subr_gt0; exact: lt_le_trans eD Dt.
have de : 0 < D^-1 - e by rewrite subr_gt0.
have tn : t - e != 0 := lt0r_neq0 te.
have -> : (D * t + e) / (t - e) = D + (D + 1) * e / (t - e).
  by field.
rewrite /condition_perturbation_bound lerD2l.
apply: ler_wpM2l.
  by apply: mulr_ge0 => //; lra.
by rewrite lef_pV2 ?posrE // lerD2r.
Qed.

Lemma cond_slice_perturb n (A E : 'M[R]_n) (D e : R) :
  (0 < n)%N -> 1 <= D -> cond_slice D A ->
  E \is symmetricmx -> 0 <= e -> opnorm E <= e -> e < D^-1 ->
  cond_cone (condition_perturbation_bound D e) (A + E) /\
  posdefmx (A + E).
Proof.
move=> n0 D1 hA Es e0 Ee eD.
have D0 : 0 < D := lt_le_trans ltr01 D1.
have [t /andP[Dt t1] ht] := cond_slice_t D0 n0 hA.
have te : 0 < t - e by rewrite subr_gt0; exact: lt_le_trans eD Dt.
have tn : t - e != 0 := lt0r_neq0 te.
have As : A \is symmetricmx by case: hA => [[h _] _].
have AEs : A + E \is symmetricmx.
  apply/symmetricmxP; move/symmetricmxP: As => As.
  by move/symmetricmxP: Es => Es; rewrite raddfD /= As Es.
have hAE := symmetric_add_form Es e0 Ee ht.
have hratio := condition_perturbation_ratio D1 Dt e0 eD.
split.
- split => //; exists (t - e); first exact: ltW.
  move=> x; have /andP[hlo hhi] := hAE x; apply/andP; split => //.
  apply: le_trans hhi _.
  apply: ler_wpM2r; first exact: mxdot_ge0.
  by rewrite -ler_pdivrMr.
- split => // x x0.
  have /andP[h _] := hAE x^T.
  have AEtr : (A + E)^T = A + E by apply/symmetricmxP.
  rewrite -{1}AEtr -trmx_mul !mxdot_trmx in h.
  apply: lt_le_trans h; apply: mulr_gt0 => //.
  by rewrite mxdot_gt0.
Qed.

Lemma mxdot_col_mx h n (u u' : 'cV[R]_h) (v v' : 'cV[R]_n) :
  mxdot (col_mx u v) (col_mx u' v') = mxdot u u' + mxdot v v'.
Proof. by rewrite !mxdot_colE tr_col_mx mul_row_col mxE. Qed.

Lemma quadratic_block_diag h n (A : 'M[R]_h) (B : 'M[R]_n)
    (u : 'cV[R]_h) (v : 'cV[R]_n) :
  mxdot (col_mx u v) (block_mx A 0 0 B *m col_mx u v) =
    mxdot u (A *m u) + mxdot v (B *m v).
Proof.
by rewrite mul_block_col !mul0mx add0r addr0 mxdot_col_mx.
Qed.

Lemma symmetric_block_diag h n (A : 'M[R]_h) (B : 'M[R]_n) :
  A \is symmetricmx -> B \is symmetricmx ->
  block_mx A 0 0 B \is symmetricmx.
Proof.
move=> /symmetricmxP AT /symmetricmxP BT.
by apply/symmetricmxP; rewrite tr_block_mx !trmx0 AT BT.
Qed.

Lemma block_diag_form_bounds h n (A : 'M[R]_h) (B : 'M[R]_n) (a b : R) :
  (forall u : 'cV[R]_h,
    a * mxdot u u <= mxdot u (A *m u) <= b * mxdot u u) ->
  (forall v : 'cV[R]_n,
    a * mxdot v v <= mxdot v (B *m v) <= b * mxdot v v) ->
  forall x : 'cV[R]_(h + n),
    a * mxdot x x <= mxdot x (block_mx A 0 0 B *m x) <= b * mxdot x x.
Proof.
move=> hA hB x.
rewrite -[x]vsubmxK quadratic_block_diag mxdot_col_mx !mulrDr.
have /andP[Al Au] := hA (usubmx x).
have /andP[Bl Bu] := hB (dsubmx x).
by apply/andP; split; exact: lerD.
Qed.

Lemma cond_slice_block1 h n (A : 'M[R]_n) (D : R) :
  (0 < n)%N -> 1 <= D -> cond_slice D A ->
  cond_slice D (block_mx (1%:M : 'M[R]_h) 0 0 A).
Proof.
move=> n0 D1 hA.
have D0 : 0 < D := lt_le_trans ltr01 D1.
have [t /andP[Dt t1] ht] := cond_slice_t D0 n0 hA.
have Di0 : 0 <= D^-1 by rewrite invr_ge0; exact: ltW.
have t0 : 0 <= t := le_trans Di0 Dt.
have Dtn : 1 <= D * t.
  by have := ler_wpM2l (ltW D0) Dt; rewrite mulfV ?gt_eqF.
have As : A \is symmetricmx by case: hA => [[H _] _].
split.
- split; first apply: symmetric_block_diag => //.
    by apply/symmetricmxP; rewrite trmx1.
  exists t => //; apply: block_diag_form_bounds ht => u.
  have uu0 := mxdot_ge0 u.
  rewrite mul1mx; apply/andP; split; nra.
- by rewrite mxtrace_block mxtrace1 (proj2 hA) natrD.
Qed.

Lemma cond_slice_weighted_block h n (A E : 'M[R]_n) (D s : R) :
  1 <= D -> cond_slice D A -> E \is symmetricmx ->
  opnorm E <= (2 * D)^-1 -> 0 < s -> s <= 1 ->
  cond_cone (4 * D ^+ 2 / s)
    (block_mx (s%:M : 'M[R]_h) 0 0 (A + E)) /\
  posdefmx (block_mx (s%:M : 'M[R]_h) 0 0 (A + E)).
Proof.
move=> D1 hA Es hE s0 s1.
have D0 : 0 < D := lt_le_trans ltr01 D1.
have Dn : D != 0 := lt0r_neq0 D0.
have sn : s != 0 := lt0r_neq0 s0.
pose e : R := (2 * D)^-1.
have e0 : 0 < e by rewrite /e invr_gt0 mulr_gt0 // ltr0n.
have e1 : e <= 1.
  rewrite /e -[X in X <= _]mul1r ler_pdivrMr ?mulr_gt0 //.
  by nra.
have eD : e <= D := le_trans e1 D1.
have half : D^-1 - e = e by rewrite /e; field.
have As : A \is symmetricmx by case: hA => [[H _] _].
have AEs : A + E \is symmetricmx.
  apply/symmetricmxP; move/symmetricmxP: As => As.
  by move/symmetricmxP: Es => Es; rewrite raddfD /= As Es.
have hAE (v : 'cV[R]_n) : e * mxdot v v <= mxdot v ((A + E) *m v) <=
    (2 * D) * mxdot v v.
  have /andP[ha hb] := cond_slice_form D0 hA v.
  have := (opnorm_symP Es (ltW e0)).2 hE v.
  rewrite ler_norml => /andP[he hf].
  have vv0 := mxdot_ge0 v.
  have hu : (D + e) * mxdot v v <= (2 * D) * mxdot v v.
    apply: ler_wpM2r => //; nra.
  rewrite mulmxDl mxdotDr; apply/andP; split.
  - rewrite -half mulrBl; nra.
  - nra.
pose Q : 'M[R]_(h + n) := block_mx (s%:M : 'M[R]_h) 0 0 (A + E).
have Qs : Q \is symmetricmx.
  apply: symmetric_block_diag => //.
  by apply/symmetricmxP; rewrite tr_scalar_mx.
have se0 : 0 < s * e := mulr_gt0 s0 e0.
have hQ (v : 'cV[R]_(h + n)) : (s * e) * mxdot v v <= mxdot v (Q *m v) <=
    (2 * D) * mxdot v v.
  apply: block_diag_form_bounds.
  - move=> u; rewrite mul_scalar_mx mxdotZr.
    have uu0 := mxdot_ge0 u.
    apply/andP; split; apply: ler_wpM2r => //; nra.
  - move=> u; have /andP[ha hb] := hAE u; apply/andP; split => //.
    apply: le_trans ha; apply: ler_wpM2r; first exact: mxdot_ge0.
    nra.
have scale : (4 * D ^+ 2 / s) * (s * e) = 2 * D.
  by rewrite /e; field.
split.
- split => //; exists (s * e); first exact: ltW.
  by move=> v; rewrite scale; exact: hQ.
- split => // v v0.
  have /andP[hv _] := hQ v^T.
  have Qt : Q^T = Q by apply/symmetricmxP.
  rewrite -{1}Qt -trmx_mul !mxdot_trmx in hv.
  apply: lt_le_trans hv; apply: mulr_gt0 => //.
  by rewrite mxdot_gt0.
Qed.

Lemma opnorm_zero_block h n (E : 'M[R]_n) : E \is symmetricmx ->
  opnorm (block_mx (0 : 'M[R]_h) 0 0 E) <= opnorm E.
Proof.
move=> Es.
have Zs : (0 : 'M[R]_h) \is symmetricmx by apply/symmetricmxP; rewrite trmx0.
have Bs := symmetric_block_diag Zs Es.
apply/(opnorm_symP Bs (opnorm_ge0 E)) => v.
rewrite ler_norml -mulNr; apply: block_diag_form_bounds.
- move=> u; rewrite mul0mx mxdot0r; apply/andP; split.
  + rewrite mulNr oppr_le0; exact: mulr_ge0 (opnorm_ge0 E) (mxdot_ge0 u).
  + exact: mulr_ge0 (opnorm_ge0 E) (mxdot_ge0 u).
- move=> u; have := (opnorm_symP Es (opnorm_ge0 E)).2 (lexx _) u.
  by rewrite ler_norml -mulNr.
Qed.

(* A weighted identity block is a standalone example, including empty blocks. *)
Example weighted_identity_condition h n (s : R) : 0 < s -> s <= 1 ->
  cond_cone (4 / s) (block_mx (s%:M : 'M[R]_h) 0 0 (1%:M : 'M[R]_n)) /\
  posdefmx (block_mx (s%:M : 'M[R]_h) 0 0 (1%:M : 'M[R]_n)).
Proof.
move=> s0 s1.
have hI : cond_slice (1 : R) (1%:M : 'M[R]_n) := @cond_slice1 R n 1 (lexx _).
have Zs : (0 : 'M[R]_n) \is symmetricmx by apply/symmetricmxP; rewrite trmx0.
have Zb : opnorm (0 : 'M[R]_n) <= (2 * (1 : R))^-1.
  by rewrite opnorm0 invr_ge0 mulr_ge0.
have := cond_slice_weighted_block h (lexx (1 : R)) hI Zs Zb s0 s1.
by rewrite expr1n mulr1 addr0.
Qed.

End additive_condition.
