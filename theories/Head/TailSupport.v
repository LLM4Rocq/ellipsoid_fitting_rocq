(* Positive support by a Frobenius-unit perturbation. Deterministic.
   - A symmetric N with |N|_F <= c lies in the Loewner box -c I <= N <= c I,
     since its operator norm is at most its Frobenius norm
     (paper_main_frobenius_loewner_box, from opnorm_le_frobenius and
     opnorm_symP of GaussianAnalysis.matrix.opnorm).
   - For a symmetric M <> 0, the unit N(M) = M / |M|_F
     (paper_main_frobenius_unit) satisfies -I <= N(M) <= I and
     <M, N(M)> = |M|_F.
   - Perturbation (paper_main_support_perturbation): assume
     a I <= S0 <= b I, 0 < delta < a, <Mu, S0> = 0, 0 < h <= |Mu|_F and
     |Mv|_F <= v. Then S' = S0 + delta N(Mu) satisfies
     (a - delta) I <= S' <= (b + delta) I and
     <Mu + Mv, S'> >= delta h - v (b + delta) sqrt d. So the support is
     positive when v (b + delta) sqrt d < delta h
     (paper_main_support_positive).
   The perturbation uses Cauchy-Schwarz for the Frobenius pairing and the
   Loewner bounds on the Frobenius norm and on the trace. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean opnorm.
From EllipsoidFitting Require Import Matrix.Definitions
  Matrix.OperatorDefinitions PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.Separation Geometry.HeadFrobenius
  Geometry.HeadCorrection Geometry.HeadFeature Geometry.HeadSpectral
  Geometry.HeadCoefficients Spectral.SymmetricBilinear Spectral.Transport
  Spectral.OperatorTransport Spectral.SymmetricDiagonalization.
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
Theorem paper_main_frobenius_loewner_box N (c : R) :
  paper_main_symmetric N -> paper_main_frobenius N <= c ->
  paper_main_loewner_le ((- c) *: 1%:M) N /\ paper_main_loewner_le N (c *: 1%:M).
Proof.
move=> /paper_main_symmetricmx Ns Nc.
have c0 : 0 <= c := le_trans (pmh_frobenius_ge0 _ N) Nc.
apply/paper_main_loewner_boxP; split => //.
by apply/(opnorm_symP Ns c0); exact: le_trans (opnorm_le_frobenius N) Nc.
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
