(* The actual finite nets for the head-section minimax bridge of
   PaperMainHeadSectionApprox, built from the fixed grids of
   PaperMainGordonEntropy, and the existence corollary with no net or
   cardinality premise. Matrices have size n+1, D =
   paper_main_symmetric_dimension n > 0 is the number of public symmetric
   coordinates and C(eps) = paper_main_gordon_entropy_constant eps.
   - Dual net. For a nonempty set Y of unit vectors for paper_main_gordon_dot q
     (so q > 0), paper_main_gordon_entropy_net_fixed gives an eps-net z of Y
     contained in Y, indexed by seq 0 r with
     r = length (paper_main_gordon_entropy_grid q eps) > 0, ln r <= C(eps) q.
   - Net of the section. For a nonempty section, the same construction on the code
     set paper_main_cone_code_set n section (PaperMainConeGaussianCoordinates)
     gives code points, each the code of a matrix of the section, chosen by
     classical choice. Codes of symmetric matrices are linear and their
     squared Gordon distance is the squared Frobenius distance, so these
     matrices B t (t < s) form a Frobenius eps-net of the section contained
     in it, with s = length (paper_main_gordon_entropy_grid D eps) > 0 and
     ln s <= C(eps) D. Conversely the codes of any such net form a Gordon
     eps-net of the code set.
   - Existence corollary. For every eps > 0 there are such nets, depending
     only on Y, W and eps, such that for every linear map V with the operator
     bound |sum_i y_i V_i|_F <= L |y|_2 and all beta, gamma > 0,
       soft_minimax - C(eps) D / gamma - L eps <= minimax
                    <= soft_minimax + C(eps) q / beta + L eps,
     where soft_minimax is the soft minimax of <sum_i (z a)_i V_i, B t> over
     a < r and t < s. So the nets are uniform in V. No measurable selection
     is claimed. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From EllipsoidFitting Require Import SoftDefinitions SoftExtrema GaussianCovarianceSums
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadFeature PaperMainGeometryHeadWidth
  PaperMainGordonProcessCovariance PaperMainGordonNets PaperMainGordonEntropy
  PaperMainGaussianFeatureCoordinates PaperMainConeGaussianCoordinates
  PaperMainConeGaussianCoordinatesSpheres
  PaperMainHeadSectionMeasurable PaperMainHeadSectionMinimax PaperMainHeadSectionApprox.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope R_scope.

Lemma paper_main_head_section_sq_le (x e : R) :
  0 <= x -> 0 <= e -> x ^ 2 <= e ^ 2 -> x <= e.
Proof. intros Hx He H; nra. Qed.

Lemma paper_main_head_section_sq_mono (x e : R) : 0 <= x -> x <= e -> x ^ 2 <= e ^ 2.
Proof. intros Hx H; nra. Qed.

Local Open Scope ring_scope.

(* Codes of symmetric matrices: linearity and distances. *)

Lemma paper_main_head_section_code_sub n (P1 P2 : 'M[R]_n.+1) k :
  paper_main_symmetric P1 -> paper_main_symmetric P2 ->
  paper_main_cone_code n (P1 - P2) k =
    paper_main_cone_code n P1 k - paper_main_cone_code n P2 k.
Proof.
move=> H1 H2.
have H12 : paper_main_symmetric (P1 - P2) by exact: pmh_symmetricB.
rewrite !paper_main_cone_code_basis //; exact: pmh_pairingBr.
Qed.

Lemma paper_main_head_section_code_distance n (P1 P2 : 'M[R]_n.+1) :
  paper_main_symmetric P1 -> paper_main_symmetric P2 ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun k => Rminus (paper_main_cone_code n P1 k) (paper_main_cone_code n P2 k))
    (fun k => Rminus (paper_main_cone_code n P1 k) (paper_main_cone_code n P2 k)) =
  pow (paper_main_frobenius (P1 - P2)) 2%N.
Proof.
move=> H1 H2.
have H12 : paper_main_symmetric (P1 - P2) by exact: pmh_symmetricB.
rewrite -(paper_main_cone_code_norm_squared n (P1 - P2) H12).
rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k _ /=.
by rewrite (paper_main_head_section_code_sub n P1 P2 k H1 H2) RminusE.
Qed.

Lemma paper_main_head_section_code_agree n (u w : nat -> R) (P : 'M[R]_n.+1) :
  (forall k, (k < paper_main_symmetric_dimension n)%coq_nat -> u k = paper_main_cone_code n P k) ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun i => Rminus (u i) (w i)) (fun i => Rminus (u i) (w i)) =
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun i => Rminus (paper_main_cone_code n P i) (w i))
    (fun i => Rminus (paper_main_cone_code n P i) (w i)).
Proof.
move=> Hu; rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk /=.
have Hk' := proj1 (List.in_seq _ _ _) Hk.
have HkD : (k < paper_main_symmetric_dimension n)%coq_nat by lia.
by rewrite (Hu k HkD).
Qed.

(* The codes of a Frobenius net of the section form a Gordon net of its code
   set. *)

Theorem paper_main_head_section_net_code n m (kappa : R) (W : 'I_m -> 'M[R]_n.+1)
    (B : nat -> 'M[R]_n.+1) (s : nat) (eps : R) :
  paper_main_head_section_net kappa W B s eps ->
  paper_main_gordon_finite_net (paper_main_symmetric_dimension n)
    (paper_main_cone_code_set n (paper_main_head_section kappa W))
    (fun t => paper_main_cone_code n (B t)) (List.seq 0 s) eps.
Proof.
move=> [HB Hcov]; split.
  move=> t Ht; exists (B t); split => //.
  by apply: HB; apply/paper_main_head_section_seq_lt.
move=> u [P [HP Hu]].
have [t [Ht HPt]] := Hcov P HP.
exists t; split; first exact/paper_main_head_section_seq_lt.
have Hsym := @paper_main_cone_section_symmetric n m kappa W.
rewrite /= (paper_main_head_section_code_agree n u _ P Hu).
rewrite (paper_main_head_section_code_distance n P (B t) (Hsym P HP) (Hsym (B t) (HB t Ht))).
apply: paper_main_head_section_sq_mono; last by apply/RleP.
by apply/RleP; exact: pmh_frobenius_ge0.
Qed.

(* The section net from the fixed entropy grid. *)

Theorem paper_main_head_section_entropy_net n m (kappa : R) (W : 'I_m -> 'M[R]_n.+1)
    (eps : R) :
  0 < eps -> (exists P, paper_main_head_section kappa W P) ->
  let s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps) in
  (0 < s)%N /\ exists B : nat -> 'M[R]_n.+1,
    paper_main_head_section_net kappa W B s eps /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR (paper_main_symmetric_dimension n).
Proof.
move=> He HA s.
have [HT HU] := paper_main_cone_section_code_set n m kappa W HA.
have He' : Rlt 0 eps by apply/RltP.
have [Hs [v [[Hin Hcov] Hln]]] := paper_main_gordon_entropy_net_fixed
  (paper_main_symmetric_dimension n)
  (paper_main_cone_code_set n (paper_main_head_section kappa W)) eps He' HT HU.
have Hs' : (0 < s)%N by apply/ssrnat.ltP.
have Hpick : forall t, exists P : 'M[R]_n.+1, (t < s)%N ->
    paper_main_head_section kappa W P /\
    forall k, (k < paper_main_symmetric_dimension n)%coq_nat ->
      v t k = paper_main_cone_code n P k.
  move=> t; have [Ht|Ht] := ltnP t s.
    have [P HP] := Hin t (proj2 (paper_main_head_section_seq_lt t s) Ht).
    by exists P.
  by case: HA => P0 HP0; exists P0.
have [B HB] := choice Hpick.
split => //; exists B; split; last by apply/RleP.
have Hsym := @paper_main_cone_section_symmetric n m kappa W.
split.
  by move=> t Ht; have [] := HB t Ht.
move=> P HP.
have [t [Ht Hd]] := Hcov (paper_main_cone_code n P)
  (ex_intro _ P (conj HP (fun k _ => erefl))).
have Ht' : (t < s)%N by apply/paper_main_head_section_seq_lt.
have [HBt HvB] := HB t Ht'.
exists t; split => //.
have Heq : paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun i => Rminus (paper_main_cone_code n P i) (v t i))
    (fun i => Rminus (paper_main_cone_code n P i) (v t i)) =
  paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun i => Rminus (paper_main_cone_code n P i) (paper_main_cone_code n (B t) i))
    (fun i => Rminus (paper_main_cone_code n P i) (paper_main_cone_code n (B t) i)).
  rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk /=.
  have Hk' := proj1 (List.in_seq _ _ _) Hk.
  have HkD : (k < paper_main_symmetric_dimension n)%coq_nat by lia.
  by rewrite (HvB k HkD).
rewrite Heq (paper_main_head_section_code_distance n P (B t) (Hsym P HP) (Hsym (B t) HBt)) in Hd.
apply/RleP; apply: paper_main_head_section_sq_le => //.
  by apply/RleP; exact: pmh_frobenius_ge0.
exact: Rlt_le.
Qed.

(* The existence corollary: no net or cardinality premise remains. *)

Theorem paper_main_head_section_approx_exists n m (kappa : R) q (Y : (nat -> R) -> Prop)
    (W : 'I_m -> 'M[R]_n.+1) (eps : R) :
  0 < eps -> (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot q y y = 1) ->
  (exists P, paper_main_head_section kappa W P) ->
  let r := List.length (paper_main_gordon_entropy_grid q eps) in
  let s := List.length (paper_main_gordon_entropy_grid (paper_main_symmetric_dimension n) eps) in
  (0 < r)%N /\ (0 < s)%N /\
  exists (z : nat -> nat -> R) (B : nat -> 'M[R]_n.+1),
    paper_main_gordon_finite_net q Y z (List.seq 0 r) eps /\
    paper_main_head_section_net kappa W B s eps /\
    ln (INR r) <= paper_main_gordon_entropy_constant eps * INR q /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR (paper_main_symmetric_dimension n) /\
    forall (V : nat -> 'M[R]_n.+1) (L beta gamma : R),
      paper_main_head_section_operator_bound q V L -> 0 < beta -> 0 < gamma ->
      soft_minimax beta gamma
          (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
          (List.seq 0 r) (List.seq 0 s) -
        paper_main_gordon_entropy_constant eps * INR (paper_main_symmetric_dimension n) / gamma -
        L * eps <= paper_main_head_section_minimax kappa q Y W V /\
      paper_main_head_section_minimax kappa q Y W V <=
        soft_minimax beta gamma
          (fun a t => paper_main_pairing (paper_main_head_section_combination q (z a) V) (B t))
          (List.seq 0 r) (List.seq 0 s) +
        paper_main_gordon_entropy_constant eps * INR q / beta + L * eps.
Proof.
move=> He HY HU HA r s.
have He' : Rlt 0 eps by apply/RltP.
have [Hr [z [Hz Hlr]]] := paper_main_gordon_entropy_net_fixed q Y eps He' HY HU.
have [Hs [B [HB Hls]]] := paper_main_head_section_entropy_net n m kappa W eps He HA.
have Hr' : (0 < r)%N by apply/ssrnat.ltP.
split => //; split => //.
exists z, B; split => //; split => //; split; first by apply/RleP.
split => // V L beta gamma HV Hb Hg.
have He0 : 0 <= eps by apply: ltW.
split.
- apply: le_trans (paper_main_head_section_soft_minimax_lower kappa q Y W V L eps beta gamma
    r s z B HY Hs He0 Hb Hg HV Hz (proj1 HB)).
  rewrite lerD2r lerD2l lerN2.
  apply: ler_wpM2r; [by rewrite invr_ge0 ltW | exact: Hls].
- apply: le_trans (paper_main_head_section_soft_minimax_upper kappa q Y W V L eps beta gamma
    r s z B HU Hr' Hs Hb Hg HV (proj1 Hz) HB) _.
  rewrite lerD2r lerD2l.
  apply: ler_wpM2r; [by rewrite invr_ge0 ltW | by apply/RleP].
Qed.
