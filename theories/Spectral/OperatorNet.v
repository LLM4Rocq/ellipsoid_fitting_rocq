(* A fixed net of the unit sphere of R^N, N = n + 1, for the Gaussian
   operator tail. unit_sphere_net (GaussianAnalysis.matrix.nets) gives a
   1/4-net v_0, ..., v_(s-1) of the unit sphere made of unit vectors, with
   s <= (18 e)^N <= 2^(20 N). If |v_i^T Z v_j| <= b for all i, j < s, then
   opnorm Z <= 2 b by opnorm_net_sphere, that is paper_main_cone_opnorm_le Z
   (2 b). paper_main_symmetric_operator_net_quarter_stdlib states the
   contrapositive with Stdlib's operators, in the form of the hypotheses of
   the Gaussian net tail. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct Rstruct_topology.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require sequences exp.
From GaussianAnalysis.matrix Require Import euclidean opnorm nets.
From EllipsoidFitting Require Import PaperMainDefinitions
  Gordon.ProcessCovariance Cone.ConditionOperator Spectral.SymmetricBilinear
  Spectral.SymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma paper_main_expR1_le4 : sequences.expR (1 : R) <= 4%:R.
Proof.
have i2 : (2%:R : R)^-1 = 1 - 2%:R^-1 by rewrite {2}(splitr 1) mul1r addrK.
have h := exp.expR_ge1Dx (- (2%:R : R)^-1).
rewrite exp.expRN -i2 in h.
have p : 0 < sequences.expR ((2%:R : R)^-1) := exp.expR_gt0 _.
have h2 : sequences.expR ((2%:R : R)^-1) <= 2%:R.
  by rewrite -[X in X <= _]invrK -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0 ?ltr0n.
have -> : (1 : R) = 2%:R * 2%:R^-1 by rewrite mulfV ?pnatr_eq0.
rewrite exp.expRM_natl.
apply: le_trans (lerXn2r 2 _ _ h2) _; rewrite ?nnegrE ?(ltW p) ?ler0n //.
by rewrite -natrX.
Qed.

Section OperatorNet.
Variable n : nat.
Local Notation N := (S n).

Corollary paper_main_symmetric_operator_net_quarter_stdlib :
  exists (s : nat) (v : nat -> nat -> R),
    [/\ Nat.lt 0 s,
      forall i, Nat.lt i s -> paper_main_gordon_dot N (v i) (v i) = IZR 1,
      Rle (ln (INR s)) (Rmult (Rmult 20 (ln 2)) (INR N)) &
      forall Z (b beta : R), beta = Rmult 2 b ->
        ~ paper_main_cone_opnorm_le Z beta ->
        exists i j, [/\ Nat.lt i s, Nat.lt j s &
          Rle b (Rabs (((paper_main_symmetric_column n (v i))^T *m Z *m
            paper_main_symmetric_column n (v j)) ord0 ord0))]].
Proof.
have e0 : 0 < (4%:R : R)^-1 by rewrite invr_gt0 ltr0n.
have [U [Uu UN Us]] := unit_sphere_net N e0.
pose v (i k : nat) : R := nth 0 U i (inord k) 0.
have vE i : paper_main_symmetric_column n (v i) = nth 0 U i.
  by apply/matrixP => k j; rewrite mxE /v inord_val [j]ord1.
have s0 : (0 < size U)%N.
  have d1 : unit_sphere (delta_mx 0 0 : 'cV[R]_N).
    rewrite /unit_sphere /= frobenius_colE trmx_delta mul_delta_mx mxE.
    by rewrite !eqxx sqrtr1.
  have [y yU _] := UN _ d1.
  by rewrite lt0n size_eq0; apply/eqP => U0; rewrite U0 in yU.
have I2 : IZR 2 = 2%:R :> R by rewrite -INRE INR_IZR_INZ.
exists (size U), v; split.
- exact/ssrnat.ltP.
- move=> i /ssrnat.ltP Hi; rewrite -paper_main_symmetric_column_norm vE.
  by rewrite -mxdot_colE -frobenius_sqr Uu ?mem_nth // expr1n.
- have I20 : IZR 20 = 20%:R :> R by rewrite -INRE INR_IZR_INZ.
  apply/RleP; rewrite !INRE !RlnE !RmultE I20 I2.
  set C := 2 * sequences.expR 1 * (1 + 2 / 4^-1) in Us.
  have e4 := paper_main_expR1_le4.
  have C72 : C <= 2%:R ^+ 7 by rewrite /C invrK; lra.
  have C0 : 0 < C by rewrite /C invrK; have := exp.expR_gt0 (1 : R); lra.
  have S0 : 0 < (size U)%:R :> R by rewrite ltr0n.
  apply: le_trans (_ : exp.ln (C ^+ N) <= _).
    by rewrite exp.ler_ln ?posrE ?exprn_gt0.
  have lC : exp.ln C <= exp.ln (2%:R ^+ 7 : R).
    by rewrite exp.ler_ln ?posrE ?exprn_gt0 ?ltr0n.
  rewrite exp.lnXn ?ltr0n // in lC.
  have l2 : 0 <= exp.ln (2%:R : R) by rewrite exp.ln_ge0 ?ler1n.
  rewrite exp.lnXn // -[exp.ln C *+ N]mulr_natr ler_wpM2r ?ler0n //; lra.
move=> Z b beta -> Hnot.
have [b0|b0] := leP 0 b; last first.
  exists 0%N, 0%N; split; [exact/ssrnat.ltP | exact/ssrnat.ltP |].
  by apply/RleP; rewrite RabsE (le_trans (ltW b0)).
apply: contrapT => Hno; apply: Hnot; apply/paper_main_cone_opnorm_leP.
have Hb u w : u \in U -> w \in U -> `|mxdot u (Z *m w)| <= b.
  move=> uU wU; rewrite leNgt; apply/negP => bl; apply: Hno.
  exists (index u U), (index w U); split.
  + by apply/ssrnat.ltP; rewrite index_mem.
  + by apply/ssrnat.ltP; rewrite index_mem.
  + apply/RleP; rewrite RabsE !vE !nth_index // -mulmxA -mxdot_colE.
    exact: ltW.
have U1 u : u \in U -> frobenius u <= 1 by move=> /Uu ->.
have e1 : 2 * (4%:R : R)^-1 < 1 by lra.
have := @opnorm_net_sphere _ N N Z U U (4%:R^-1) b (ltW e0) e1 b0 UN U1 UN Hb.
rewrite RmultE I2 ger0_norm ?mulr_ge0 ?ler0n // => H.
by apply: le_trans H _; rewrite ler_pdivrMr; lra.
Qed.

End OperatorNet.
