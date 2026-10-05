(* Deterministic witnesses for fits in a finite family of orientations.

   For an orientation O and U = P_r(O) (PaperMainOrientationNet), the
   admissible candidates are
     paper_main_orientation_admissible r O eps L A b :=
       A PSD, paper_main_pinching U A = A, 1/4 <= ||A||_F^2 <= 4,
       paper_main_cone_opnorm_le ((1 - U) A (1 - U)) eps, and |b| <= L.
   The equality says that A is block diagonal in O, so PaperMainOrientationBlocks
   gives its head and bulk blocks, their PSD property and the norm split.
   1. P_r(O) is symmetric, and idempotent when O^T O = 1.
   2. For U U = U the pinching is idempotent, and the complement compression
      of paper_main_pinching U S equals (1 - U) S (1 - U).
   3. Main target: an actual fit, a feature Gram bound K I with K <= N L^2 and a
      finite family of orthogonal matrices that covers every orthogonal O
      within tau in head-projector distance, for every r <= rmax, give r <= rmax,
      a member k and an admissible candidate (A, b) with quadratic risk at most
      16 L tau. A28 orders the spectral head at the cutoff eps0, the cover gives
      the member, A is the pinching of the checked unit witness (M126), and the
      M126 and M124 estimates give the norm annulus, the bulk operator bound,
      the offset bound and the risk bound. r = 0 is included. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import GaussianProbabilityProductContinuity PaperMainDefinitions PaperMainGeometryPsd
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius PaperMainConeConditionOperator
  PaperMainFeatureGramBlocks PaperMainFeatureLossControl PaperMainProjectionFrobenius
  PaperMainProjectionPinching PaperMainPinchingOperator PaperMainPinchingLoss
  PaperMainSpectralCutoff PaperMainSpectralSplit PaperMainBlockGeometry PaperMainOrientationNet
  PaperMainOrientationSpectral PaperMainOrientationBlocks.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The head projector of an orientation. *)

Lemma paper_main_orientation_projector_tr {d : nat} (r : nat) (O : 'M[R]_d) :
  (paper_main_orientation_projector r O)^T = paper_main_orientation_projector r O.
Proof.
by rewrite /paper_main_orientation_projector !trmx_mul trmxK tr_diag_mx mulmxA.
Qed.

Lemma paper_main_orientation_projector_idem {d : nat} (r : nat) (O : 'M[R]_d) :
  O^T *m O = 1%:M ->
  paper_main_orientation_projector r O *m paper_main_orientation_projector r O =
  paper_main_orientation_projector r O.
Proof.
move=> HO; have HO' : O *m O^T = 1%:M by apply: mulmx1C.
rewrite /paper_main_orientation_projector.
set D := diag_mx (paper_main_orientation_mask (d := d) r).
have -> : O^T *m D *m O *m (O^T *m D *m O) = O^T *m (D *m (O *m O^T) *m D) *m O.
  by rewrite !mulmxA.
by rewrite HO' mulmx1 /D paper_main_orientation_mask_idem.
Qed.

(* 2. Pinching facts for an idempotent U. *)

Lemma paper_main_orientation_pinching_complement {d : nat} (U S : 'M[R]_d) :
  U *m U = U ->
  (1%:M - U) *m paper_main_pinching U S *m (1%:M - U) = (1%:M - U) *m S *m (1%:M - U).
Proof.
move=> HU.
have HCU : (1%:M - U) *m U = 0 by rewrite mulmxBl mul1mx HU subrr.
have HUC : U *m (1%:M - U) = 0 by rewrite mulmxBr mulmx1 HU subrr.
have HCC : (1%:M - U) *m (1%:M - U) = 1%:M - U by rewrite mulmxBr mulmx1 HCU subr0.
rewrite /paper_main_pinching.
set C := 1%:M - U.
rewrite (mulmxDr C) (mulmxDl _ _ C).
rewrite !mulmxA HCU !mul0mx add0r.
by rewrite HCC -!mulmxA HCC.
Qed.

Lemma paper_main_orientation_pinching_idem {d : nat} (U S : 'M[R]_d) :
  U *m U = U ->
  paper_main_pinching U (paper_main_pinching U S) = paper_main_pinching U S.
Proof.
move=> HU.
have HUC : U *m (1%:M - U) = 0 by rewrite mulmxBr mulmx1 HU subrr.
have Hhead : U *m paper_main_pinching U S *m U = U *m S *m U.
  rewrite /paper_main_pinching.
  set C := 1%:M - U.
  rewrite (mulmxDr U) (mulmxDl _ _ U) !mulmxA HUC !mul0mx addr0.
  by rewrite HU -!mulmxA HU.
rewrite [in LHS]/paper_main_pinching Hhead (paper_main_orientation_pinching_complement U S HU).
by [].
Qed.

(* 3. Admissible candidates and the deterministic fit witness. *)

Definition paper_main_orientation_admissible {d : nat} (r : nat) (O : 'M[R]_d)
    (eps L : R) (A : 'M[R]_d) (b : R) : Prop :=
  paper_main_psd A /\
  paper_main_pinching (paper_main_orientation_projector r O) A = A /\
  1 / 4 <= paper_main_frobenius A ^+ 2 <= 4 /\
  paper_main_cone_opnorm_le ((1%:M - paper_main_orientation_projector r O) *m A *m
    (1%:M - paper_main_orientation_projector r O)) eps /\
  `|b| <= L.

Theorem paper_main_orientation_fit_witness d (eps0 eps tau L K : R) (rmax : nat)
    (s : nat -> nat) (Os : nat -> nat -> 'M[R]_d) N (x : paper_main_sample N d) :
  0 < eps0 -> 0 <= eps -> 0 <= tau -> tau <= 1 / 8 -> eps0 + tau ^+ 2 <= eps ->
  0 <= L -> 0 <= K ->
  1 / eps0 ^+ 2 <= rmax%:R -> (rmax < d)%N ->
  (forall r, (r <= rmax)%N -> (0 < s r)%N) ->
  (forall r k, (r <= rmax)%N -> (k < s r)%N -> (Os r k)^T *m Os r k = 1%:M) ->
  (forall r, (r <= rmax)%N -> forall O : 'M[R]_d, O^T *m O = 1%:M ->
     exists k, (k < s r)%N /\
       paper_main_frobenius (paper_main_orientation_projector r O -
         paper_main_orientation_projector r (Os r k)) <= tau) ->
  (0 < N)%N ->
  paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
  (K <= INR N * L ^ 2)%Rcoq ->
  paper_main_fit_event N d x ->
  exists (r k : nat) (A : 'M[R]_d) (b : R),
    (r <= rmax)%N /\ (k < s r)%N /\ paper_main_orientation_admissible r (Os r k) eps L A b /\
    (paper_main_quadratic_risk N d x A b <= 16 * L * tau)%Rcoq.
Proof.
move=> He0 He Ht Ht8 Heps HL HK HR HRd Hs HOs Hcov HN HG HKN Hfit.
have Hd : (0 < d)%N by apply: leq_ltn_trans HRd.
have [S [b0 [HS [HSF Hb0]]]] := paper_main_fit_unit_witness N d x HN Hd Hfit.
have [r [O [a [Hrd [HO [HE [Hhead [Hr [HSHB [HH [HB [HBo [HHF [HPH [HPS [HPT HPP]]]]]]]]]]]]]]]] :=
  paper_main_orientation_spectral_decomposition d S eps0 HS HSF He0.
have Hrr : (r <= rmax)%N.
  by rewrite -(ler_nat R); apply: le_trans Hr HR.
have [k [Hk Hdist]] := Hcov r Hrr O HO.
have HOk := HOs r k Hrr Hk.
set P := paper_main_orientation_projector r O in HPH HPS HPT HPP Hdist.
set U := paper_main_orientation_projector r (Os r k) in Hdist *.
have HUT : U^T = U by exact: paper_main_orientation_projector_tr.
have HUU : U *m U = U by exact: paper_main_orientation_projector_idem.
have HST : S^T = S by apply/paper_main_symmetricP; exact: HS.1.
have HUP : paper_main_frobenius (U - P) <= tau by rewrite -opprB pmh_frobeniusN.
exists r, k, (paper_main_pinching U S), b0.
split => //; split => //.
have HLR : (0 <= L)%Rcoq by apply/RleP.
have HKN' : K <= N%:R * L ^+ 2.
  by apply/RleP; rewrite -INRE -RpowE -RmultE.
split.
  split; first exact: (paper_main_pinching_psd d U S HUT HS).
  split; first exact: paper_main_orientation_pinching_idem.
  split.
    exact: (paper_main_pinching_unit_norm d P U S HPT HPP HUT HUU HST HPS HSF (le_trans HUP Ht8)).
  split.
    rewrite (paper_main_orientation_pinching_complement U S HUU).
    have Hcb := paper_main_pinching_cutoff_bulk d P U _ _ eps0 tau HPT HUT HUU HPH (ltW He0) Ht
      HHF HUP HBo.
    rewrite -HSHB in Hcb.
    apply: (paper_main_opnorm_monotone d _ _ _ _ Heps Hcb).
    by apply: addr_ge0; [exact: ltW | exact: sqr_ge0].
  exact: (paper_main_feature_witness_offset N d x S b0 K L HN HK HL HG HKN' HSF Hb0).
exact: (paper_main_pinching_witness_risk N d x P U S b0 K L tau HN HK HLR HG HKN HPT HPP HUT HUU
  HST HPS HSF HUP Hb0).
Qed.

(* An admissible candidate in dimension r + m is block diagonal in O, with
   PSD head and bulk blocks, block norms in the annulus and the bulk bound. *)

Corollary paper_main_orientation_admissible_blocks {r m : nat} (O A : 'M[R]_(r + m))
    (eps L b : R) :
  O^T *m O = 1%:M -> paper_main_orientation_admissible r O eps L A b ->
  A = O^T *m block_mx (ulsubmx (O *m A *m O^T)) 0 0 (drsubmx (O *m A *m O^T)) *m O /\
  paper_main_psd (ulsubmx (O *m A *m O^T)) /\ paper_main_psd (drsubmx (O *m A *m O^T)) /\
  1 / 4 <= paper_main_frobenius (ulsubmx (O *m A *m O^T)) ^+ 2 +
    paper_main_frobenius (drsubmx (O *m A *m O^T)) ^+ 2 <= 4 /\
  paper_main_cone_opnorm_le (drsubmx (O *m A *m O^T)) eps /\
  `|b| <= L.
Proof.
move=> HO [HA [Hpin [Hnorm [Hop Hb]]]].
have Hblock := paper_main_orientation_pinching_block O A HO.
rewrite Hpin in Hblock.
have [HHp HBp] := paper_main_orientation_blocks_psd O A HA.
split; first exact: Hblock.
split => //; split => //.
split.
  have Hf := paper_main_orientation_pinching_frobenius O A HO.
  by rewrite Hpin in Hf; rewrite -Hf.
split => //.
exact: (paper_main_orientation_bulk_opnorm O A eps HO Hop).
Qed.
