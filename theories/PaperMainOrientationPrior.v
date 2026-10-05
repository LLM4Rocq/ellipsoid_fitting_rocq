(* A fixed finite prior of head/bulk blocks for each fixed orientation. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import GaussianProbabilityProductContinuity PaperMainDefinitions
  PaperMainGeometryHomogeneous PaperMainGeometryHeadFrobenius PaperMainFeatureGramBlocks
  PaperMainFeatureLossControl PaperMainConeConditionOperator PaperMainGaussianFeatureCoordinates
  PaperMainGordonEntropy PaperMainQuadraticPrior PaperMainOrientationWitness
  PaperMainOrientationBlocksLoss PaperMainOrientationRotation PaperMainHybridFiniteArray.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_orientation_admissible_standard d r (O A : 'M[R]_d) eps L b :
  paper_main_orientation_admissible r O eps L A b ->
  paper_main_symmetric A /\ (paper_main_frobenius A^2<=4)%Rcoq /\ (Rabs b<=L)%Rcoq.
Proof.
move=> [HA [Hpin [/andP[Hlo Hhi] [Hop Hb]]]].
split; first exact: (proj1 HA).
split.
- have E4 : IZR 4 = (4%:R : R) by rewrite -INRE INR_IZR_INZ.
  apply/RleP; rewrite RpowE E4; exact Hhi.
- apply/RleP; rewrite RabsE; exact Hb.
Qed.

Theorem paper_main_orientation_prior r mi (O : 'M[R]_(r+S mi)) eps L delta :
  O^T *m O = 1%:M -> (0<=L)%Rcoq -> (0<delta)%Rcoq ->
  (exists A b, paper_main_orientation_admissible r O eps L A b) ->
  exists s (Hs : nat -> 'M[R]_r) (bs : nat -> R) (Bs : nat -> 'M[R]_(S mi)),
    (0<s)%coq_nat /\
    (forall j, (j<s)%coq_nat -> paper_main_psd(Hs j) /\ paper_main_psd(Bs j) /\
      1/4<=paper_main_frobenius(Hs j)^+2+paper_main_frobenius(Bs j)^+2<=4 /\
      paper_main_cone_opnorm_le (Bs j) eps) /\
    (Rpower.ln(INR s)<=3*paper_main_gordon_entropy_constant(delta/(L+3))*(INR(r+S mi))^2)%Rcoq /\
    forall N (x : paper_main_sample N (r+S mi)) K beta a,
      (0<N)%coq_nat -> 0<=K -> (0<beta)%Rcoq ->
      paper_main_loewner_le (paper_main_feature_gram N (r+S mi) x) (K *: 1%:M) ->
      (K<=INR N*L^2)%Rcoq ->
      (exists A b, paper_main_orientation_admissible r O eps L A b /\
        (paper_main_quadratic_risk N (r+S mi) x A b<=a)%Rcoq) ->
      (paper_main_hybrid_finite_data N r mi beta (List.seq 0 s) Hs bs Bs
        (tval(paper_main_orientation_rotate N (r+S mi) O x)) <=
        a+4*(L+1)*delta+Rpower.ln(INR s)/(beta*INR N))%Rcoq.
Proof.
move=> HO HL Hdelta HT.
have Hd : (0<r+S mi)%coq_nat by rewrite -plusE; lia.
have HB := paper_main_orientation_admissible_standard (r+S mi) r O.
have [s [As [bs [Hspos [Hin [Hcard Hcover]]]]]] :=
  paper_main_quadratic_prior_positive (r+S mi)
    (paper_main_orientation_admissible r O eps L) L delta Hd HL Hdelta HT
    (fun A b H => HB A eps L b H).
pose Hs := fun j => ulsubmx (O *m As j *m O^T).
pose Bs := fun j => drsubmx (O *m As j *m O^T).
have Hblocks j (Hj : (j<s)%coq_nat) := paper_main_orientation_admissible_blocks O (As j) eps L (bs j) HO (Hin j Hj).
exists s,Hs,bs,Bs; split=> //; split.
- move=> j Hj; have [_ [HH [HBp [Hnorm [Hop _]]]]] := Hblocks j Hj.
  by split=> //; split=> //; split.
- split=> // N x K beta a HN HK Hbeta HG Hscale [A [b [HAB Hrisk]]].
  have [j [Hj Hdist]] := Hcover N x K HN HK HG Hscale A b HAB.
  have HArisk : (paper_main_quadratic_risk N (r+S mi) x (As j) (bs j)<=a+4*(L+1)*delta)%Rcoq.
  { have HA := Rle_abs (paper_main_quadratic_risk N (r+S mi) x (As j) (bs j)-
      paper_main_quadratic_risk N (r+S mi) x A b).
    rewrite Rabs_minus_sym in HA; lra. }
  have HI : List.seq 0 s <> nil.
  { move=> H; have HH := f_equal (@List.length nat) H.
    rewrite List.length_seq in HH; simpl in HH; lia. }
  have HjI : In j (List.seq 0 s) by apply in_seq; lia.
  have [EA _] := Hblocks j Hj.
  have Hrisk' : (paper_main_quadratic_risk N (r+S mi) x
      (O^T *m block_mx (Hs j) 0 0 (Bs j) *m O) (bs j)<=a+4*(L+1)*delta)%Rcoq.
  { by rewrite /Hs /Bs -EA. }
  have HH := paper_main_orientation_candidate_bound_rotate N r mi beta (List.seq 0 s)
    Hs bs Bs O x j (a+4*(L+1)*delta)%Rcoq HO HN HI Hbeta HjI Hrisk'.
  by rewrite List.length_seq in HH.
Qed.
