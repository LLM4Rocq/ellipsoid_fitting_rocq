(* Deterministic positive support by a Frobenius-unit perturbation (G13,
   checkpoint A; manuscript lines 891-923, before convex separation).
   - A symmetric N with |N|_F <= c lies in the Loewner box -c I <= N <= c I,
     by Frobenius Cauchy-Schwarz against the rank-one v v^T.
   - For a symmetric M <> 0, the unit N(M) = M / |M|_F satisfies
     -I <= N(M) <= I and <M, N(M)> = |M|_F. For d = S n its internal
     operator norm is at most 1.
   - Perturbation: assume a I <= S0 <= b I, 0 < delta < a, <Mu, S0> = 0,
     0 < h <= |Mu|_F and |Mv|_F <= v. Then S' = S0 + delta N(Mu) satisfies
     (a - delta) I <= S' <= (b + delta) I and
     <Mu + Mv, S'> >= delta h - v (b + delta) sqrt d. So the support is
     positive when v (b + delta) sqrt d < delta h.
   No matrix sign function, nuclear norm or diagonalization is used. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import MatrixDefinitions OperatorDefinitions PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryHomogeneous PaperMainGeometrySeparation
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadCorrection
  PaperMainGeometryHeadFeature PaperMainGeometryHeadSpectral
  PaperMainGeometryHeadCoefficients PaperMainSymmetricBilinear PaperMainMatrixTransport
  PaperMainMatrixOperatorTransport.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* A positive Frobenius lower bound forces a positive dimension. *)
Lemma pmhs_dim_pos (d : nat) (M : 'M[R]_d) (h : R) :
  0 < h -> h <= paper_main_frobenius M -> (0 < d)%N.
Proof.
case: d M => [|d'] M Hh HM //.
have HM0 : M = 0 by exact: flatmx0.
rewrite HM0 pmh_frobenius0 in HM.
by have := lt_le_trans Hh HM; rewrite ltxx.
Qed.

Section Support.
Variable d : nat.
Implicit Types (S M N : 'M[R]_d).

(* 1. A Frobenius bound gives a Loewner box. *)
Lemma pmhs_rank_one_frobenius (v : 'cV[R]_d) :
  paper_main_frobenius (v *m v^T) = (v^T *m v) 0 0.
Proof.
rewrite /paper_main_frobenius pmsb_pairing_outer_outer -expr2 sqrtr_sqr.
by rewrite ger0_norm //; exact: pmh_vec_sqr_ge0.
Qed.

Lemma pmhs_form_bound N (v : 'cV[R]_d) :
  `|paper_main_quadratic_form N v| <= paper_main_frobenius N * (v^T *m v) 0 0.
Proof.
rewrite -paper_main_pairing_outer -pmhs_rank_one_frobenius.
exact: pmh_pairing_frobenius_bound.
Qed.

Theorem paper_main_frobenius_loewner_box N (c : R) :
  paper_main_symmetric N -> paper_main_frobenius N <= c ->
  paper_main_loewner_le ((- c) *: 1%:M) N /\ paper_main_loewner_le N (c *: 1%:M).
Proof.
move=> HN Hc.
have HI := pmh_symmetric_id d.
have HcI : paper_main_symmetric (c *: (1%:M : 'M[R]_d)) by exact: paper_main_symmetric_scale.
have HmcI : paper_main_symmetric ((- c) *: (1%:M : 'M[R]_d)) by exact: paper_main_symmetric_scale.
have Hb : forall v : 'cV[R]_d,
    - (c * (v^T *m v) 0 0) <= paper_main_quadratic_form N v <= c * (v^T *m v) 0 0.
  move=> v; have H := pmhs_form_bound N v.
  have Hv := pmh_vec_sqr_ge0 _ v.
  have HF : paper_main_frobenius N * (v^T *m v) 0 0 <= c * (v^T *m v) 0 0.
    exact: ler_pM (pmh_frobenius_ge0 _ N) Hv Hc (lexx _).
  have := le_trans H HF; rewrite ler_norml.
  by [].
split; split.
- exact: pmh_symmetricB.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id.
  have /andP [H1 _] := Hb v; lra.
- exact: pmh_symmetricB.
- move=> v; rewrite pms_formB paper_main_form_scale pmh_form_id.
  have /andP [_ H2] := Hb v; lra.
Qed.

(* 2. The Frobenius-unit direction of a nonzero matrix. *)
Definition paper_main_frobenius_unit M : 'M[R]_d := (paper_main_frobenius M)^-1 *: M.

Theorem paper_main_frobenius_unit_box M :
  paper_main_symmetric M -> M != 0 ->
  paper_main_loewner_le ((- 1) *: 1%:M) (paper_main_frobenius_unit M) /\
  paper_main_loewner_le (paper_main_frobenius_unit M) (1 *: 1%:M).
Proof.
move=> HM HM0; apply: paper_main_frobenius_loewner_box.
  exact: paper_main_symmetric_scale.
by rewrite /paper_main_frobenius_unit pmh_frobenius_normalize.
Qed.

Theorem paper_main_frobenius_unit_pairing M :
  M != 0 -> paper_main_pairing M (paper_main_frobenius_unit M) = paper_main_frobenius M.
Proof.
move=> HM0; have Hp := pmh_frobenius_gt0 _ M HM0.
rewrite /paper_main_frobenius_unit paper_main_pairing_scale -pmh_frobenius_sqr.
by rewrite expr2 mulrA mulVf ?mul1r // lt0r_neq0.
Qed.

(* 3. The perturbation. *)
Theorem paper_main_support_perturbation (S0 Mu Mv : 'M[R]_d) (a b delta h v : R) :
  paper_main_symmetric Mu -> 0 < delta -> delta < a ->
  paper_main_loewner_le (a *: 1%:M) S0 -> paper_main_loewner_le S0 (b *: 1%:M) ->
  paper_main_pairing Mu S0 = 0 -> 0 < h -> h <= paper_main_frobenius Mu ->
  paper_main_frobenius Mv <= v ->
  paper_main_loewner_le ((a - delta) *: 1%:M) (S0 + delta *: paper_main_frobenius_unit Mu) /\
  paper_main_loewner_le (S0 + delta *: paper_main_frobenius_unit Mu) ((b + delta) *: 1%:M) /\
  delta * h - v * (b + delta) * Num.sqrt d%:R <=
    paper_main_pairing (Mu + Mv) (S0 + delta *: paper_main_frobenius_unit Mu).
Proof.
move=> HMu Hd0 Hda Hlo Hup H0 Hh HhM Hv.
have Hdim := pmhs_dim_pos d Mu h Hh HhM.
have HMu0 : Mu != 0.
  apply/eqP => HM; rewrite HM pmh_frobenius0 in HhM.
  by have := lt_le_trans Hh HhM; rewrite ltxx.
have [Nlo Nup] := paper_main_frobenius_unit_box Mu HMu HMu0.
set N := paper_main_frobenius_unit Mu in Nlo Nup *.
(* The Loewner box of S' = S0 + delta N. *)
have Hdl := pmh_loewner_scale _ _ _ _ (ltW Hd0) Nlo.
have Hdu := pmh_loewner_scale _ _ _ _ (ltW Hd0) Nup.
have Blo := pmh_loewner_add _ _ _ _ _ Hlo Hdl.
have Bup := pmh_loewner_add _ _ _ _ _ Hup Hdu.
have E1 : a *: (1%:M : 'M[R]_d) + delta *: (-1 *: 1%:M) = (a - delta) *: 1%:M.
  by rewrite scalerA mulrN1 -scalerDl.
have E2 : b *: (1%:M : 'M[R]_d) + delta *: (1 *: 1%:M) = (b + delta) *: 1%:M.
  by rewrite scalerA mulr1 -scalerDl.
rewrite E1 in Blo; rewrite E2 in Bup.
split; first exact: Blo.
split; first exact: Bup.
(* |S'|_F <= (b + delta) sqrt d, from the Loewner Frobenius and trace bounds. *)
set S' := S0 + delta *: N in Blo Bup *.
have Had : 0 <= a - delta by rewrite subr_ge0 ltW.
have Hpsd := pmh_loewner_psd _ _ _ Had Blo.
have HF2 := pmh_loewner_frobenius_upper _ _ _ Hpsd Bup.
have Htr := pmh_loewner_trace_upper _ _ _ Bup.
have Htr0 := pmh_trace_psd_ge0 _ _ Hpsd.
have Hdr : 0 < (d%:R : R) by rewrite ltr0n.
have Hbd : 0 <= b + delta.
  have H := le_trans Htr0 Htr.
  by rewrite pmulr_lge0 in H.
have HFS : paper_main_frobenius S' <= (b + delta) * Num.sqrt d%:R.
  have H1 : paper_main_frobenius S' ^+ 2 <= ((b + delta) * Num.sqrt d%:R) ^+ 2.
    rewrite exprMn (sqr_sqrtr (ler0n _ d)).
    apply: le_trans HF2 _.
    by rewrite expr2 -mulrA; apply: ler_wpM2l.
  rewrite -ler_sqr ?nnegrE //; first exact: pmh_frobenius_ge0.
  by apply: mulr_ge0 => //; exact: sqrtr_ge0.
(* The pairing: <Mu, S0> = 0, <Mu, N> = |Mu|_F, and Cauchy-Schwarz for Mv. *)
have EP : paper_main_pairing (Mu + Mv) S' =
    delta * paper_main_frobenius Mu + paper_main_pairing Mv S'.
  rewrite pmh_pairingDl /S' pmh_pairingDr H0 add0r paper_main_pairing_scale.
  by rewrite /N paper_main_frobenius_unit_pairing.
rewrite EP.
have Hcs := pmh_pairing_frobenius_bound _ Mv S'.
have HMv0 := pmh_frobenius_ge0 _ Mv.
have HFS0 := pmh_frobenius_ge0 _ S'.
have Hprod : paper_main_frobenius Mv * paper_main_frobenius S' <=
    v * ((b + delta) * Num.sqrt d%:R).
  exact: ler_pM HMv0 HFS0 Hv HFS.
have Hlow : - (v * ((b + delta) * Num.sqrt d%:R)) <= paper_main_pairing Mv S'.
  by have := le_trans Hcs Hprod; rewrite ler_norml => /andP [H _].
have Hdh : delta * h <= delta * paper_main_frobenius Mu.
  by apply: ler_wpM2l; [exact: ltW | exact: HhM].
rewrite mulrA in Hlow.
lra.
Qed.

(* Positive support when v (b + delta) sqrt d < delta h. *)
Corollary paper_main_support_positive (S0 Mu Mv : 'M[R]_d) (a b delta h v : R) :
  paper_main_symmetric Mu -> 0 < delta -> delta < a ->
  paper_main_loewner_le (a *: 1%:M) S0 -> paper_main_loewner_le S0 (b *: 1%:M) ->
  paper_main_pairing Mu S0 = 0 -> 0 < h -> h <= paper_main_frobenius Mu ->
  paper_main_frobenius Mv <= v ->
  v * (b + delta) * Num.sqrt d%:R < delta * h ->
  exists S : 'M[R]_d,
    paper_main_loewner_le ((a - delta) *: 1%:M) S /\
    paper_main_loewner_le S ((b + delta) *: 1%:M) /\
    0 < paper_main_pairing (Mu + Mv) S.
Proof.
move=> HMu Hd0 Hda Hlo Hup H0 Hh HhM Hv Hpos.
have [B1 [B2 B3]] := paper_main_support_perturbation S0 Mu Mv a b delta h v
  HMu Hd0 Hda Hlo Hup H0 Hh HhM Hv.
exists (S0 + delta *: paper_main_frobenius_unit Mu); split => //; split => //.
by apply: lt_le_trans B3; rewrite subr_gt0.
Qed.

End Support.
