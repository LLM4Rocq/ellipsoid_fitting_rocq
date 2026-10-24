(* Scalar rates for sparse-shift interpolation targets. The logarithmic
   envelope and the sample union-bound remainder vanish along any cofinal
   dimension map. All constants and densities may be arbitrary reals;
   no positivity of K or alpha is needed for these limits. *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences realfun exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.analysis Require Import family_reindexing.
From EllipsoidUniversality.Shifted Require Import ReserveDensity SparseDimensions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation RR := (R : realType).

Lemma sparse_target_sqrt_ratio {F : realType} (h p : nat -> nat) :
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : F) 0 ->
  family_sequence_limit
    (fun d => Num.sqrt ((h d)%:R : F)/Num.sqrt (p d)%:R) 0.
Proof.
move=> /reserve_scalar_tends_cvg hh.
have hs : (fun d => Num.sqrt ((h d)%:R/(p d)%:R : F)) @ \oo --> 0.
  rewrite -[X in _ --> X](sqrtr0 F).
  apply: continuous_cvg hh; exact: sqrt_continuous.
apply/reserve_scalar_tends_cvg.
have he : (fun d => Num.sqrt ((h d)%:R/(p d)%:R : F)) =
    (fun d => Num.sqrt ((h d)%:R : F)/Num.sqrt (p d)%:R).
  by apply: funext => d; rewrite sqrtrM ?ler0n // sqrtrV ?ler0n.
by rewrite -he.
Qed.

Lemma sparse_target_inverse_sqrt_limit (p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit
    (fun d => 1 / Num.sqrt ((p d)%:R : RR)) 0.
Proof.
move=> hp eps eps0.
have [D hD] := sparse_log_sqrt_cofinal hp 0%N eps0.
exists D => d dD.
by have := hD d dD; rewrite expr0.
Qed.

Lemma sparse_target_inverse_limit (p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit (fun d => ((p d)%:R : RR)^-1) 0.
Proof.
move=> hp.
have h := sparse_square_limit (sparse_target_inverse_sqrt_limit hp).
rewrite expr0n in h.
apply: (reserve_scalar_tends_eventually_eq _ h).
exists 0%N => d _.
by rewrite div1r exprVn sqr_sqrtr ?ler0n.
Qed.

Lemma sparse_target_log_inverse_limit (p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit
    (fun d => ln (1 + ((p d)%:R : RR)^-1)) 0.
Proof.
move=> hp.
have hv := (reserve_scalar_tends_cvg _ _).1
  (sparse_target_inverse_limit hp).
have h1 : (fun d => 1 + ((p d)%:R : RR)^-1) @ \oo --> (1 : RR).
  have h : (fun d => 1 + ((p d)%:R : RR)^-1) @ \oo --> (1+0 : RR).
    apply: cvgD; [exact: cvg_cst | exact: hv].
  by rewrite addr0 in h.
have hl : (fun d => ln (1 + ((p d)%:R : RR)^-1)) @ \oo --> ln (1 : RR).
  apply: continuous_cvg h1.
  exact: continuous_ln.
apply/reserve_scalar_tends_cvg.
by rewrite ln1 in hl.
Qed.

Lemma sparse_target_log_shift (q : nat) : (0 < q)%N ->
  ln (q%:R + 1 : RR) = ln (q%:R : RR) + ln (1 + (q%:R : RR)^-1).
Proof.
move=> q0.
have qR0 : (0 : RR) < q%:R by rewrite ltr0n.
have qn : (q%:R : RR) != 0 by rewrite gt_eqF.
have u0 : (0 : RR) < 1 + (q%:R : RR)^-1.
  by rewrite addr_gt0 // invr_gt0.
have e : (q%:R + 1 : RR) = q%:R * (1 + (q%:R : RR)^-1).
  by rewrite mulrDr mulr1 mulfV.
by rewrite e lnM.
Qed.

Lemma sparse_target_log_sqrt_limit (p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit
    (fun d => ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R *
      (1 + 4 * ln ((p d)%:R + 1))) 0.
Proof.
move=> hp.
have h4 := (reserve_scalar_tends_cvg _ _).1 (sparse_log_sqrt_cofinal hp 4%N).
have h5 := (reserve_scalar_tends_cvg _ _).1 (sparse_log_sqrt_cofinal hp 5%N).
have hi := (reserve_scalar_tends_cvg _ _).1 (sparse_target_log_inverse_limit hp).
have ha : (fun d => ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R +
    4 * (ln ((p d)%:R : RR)^+5 / Num.sqrt (p d)%:R) +
    4 * (ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R) *
      ln (1 + ((p d)%:R : RR)^-1)) @ \oo --> (0 : RR).
  have h : (fun d => ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R +
      4 * (ln ((p d)%:R : RR)^+5 / Num.sqrt (p d)%:R) +
      4 * (ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R) *
        ln (1 + ((p d)%:R : RR)^-1)) @ \oo --> ((0+4*0)+4*0*0 : RR).
    apply: cvgD.
    - apply: cvgD; first exact: h4.
      apply: cvgM; [exact: cvg_cst | exact: h5].
    - apply: cvgM; last exact: hi.
      apply: cvgM; [exact: cvg_cst | exact: h4].
  by rewrite !mulr0 !addr0 in h.
have he : exists D : nat, forall d, (D <= d)%N ->
    ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R +
      4 * (ln ((p d)%:R : RR)^+5 / Num.sqrt (p d)%:R) +
      4 * (ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R) *
        ln (1 + ((p d)%:R : RR)^-1) =
    ln ((p d)%:R : RR)^+4 / Num.sqrt (p d)%:R *
      (1 + 4 * ln ((p d)%:R + 1)).
  have [D hD] := hp 1%N.
  exists D => d dD.
  rewrite (sparse_target_log_shift (hD d dD)).
  rewrite [ln _ ^+5]exprS.
  ring.
apply: (reserve_scalar_tends_eventually_eq he).
exact: (reserve_scalar_tends_cvg _ _).2 ha.
Qed.

Lemma sparse_target_scale_limit (K : R) (h p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit
    (fun d => (252*K^+2*(Num.sqrt (h d)%:R+1)+8*K) /
      Num.sqrt (p d)%:R : RR) 0.
Proof.
move=> hp hh.
have hs := sparse_target_sqrt_ratio hh.
have hi := sparse_log_sqrt_cofinal hp 0.
change (family_sequence_limit
  (fun d => 1/Num.sqrt ((p d)%:R : RR)) 0) in hi.
move/reserve_scalar_tends_cvg: hs => hs.
move/reserve_scalar_tends_cvg: hi => hi.
have hc : (fun d => 252*K^+2*
      (Num.sqrt (h d)%:R/Num.sqrt (p d)%:R+1/Num.sqrt (p d)%:R)+
      8*K*(1/Num.sqrt (p d)%:R)) @ \oo -->
    252*K^+2*(0+0)+8*K*0.
  apply: (@cvgD RR RR^o _ _ eventually_filter).
  - apply: cvgM; first exact: cvg_cst.
    exact: (@cvgD RR RR^o _ _ eventually_filter _ _ _ _ hs hi).
  - apply: cvgM; [exact: cvg_cst | exact: hi].
rewrite add0r !mulr0 add0r in hc.
apply/reserve_scalar_tends_cvg.
have he : (fun d => (252*K^+2*(Num.sqrt (h d)%:R+1)+8*K) /
      Num.sqrt (p d)%:R) =
    (fun d => 252*K^+2*
      (Num.sqrt (h d)%:R/Num.sqrt (p d)%:R+1/Num.sqrt (p d)%:R)+
      8*K*(1/Num.sqrt (p d)%:R)).
  by apply: funext => d; ring.
by rewrite he.
Qed.

Lemma sparse_target_union_rate (n p : nat -> nat) (alpha : RR) :
  family_cofinal p ->
  family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha ->
  family_sequence_limit (fun d => 4*(n d)%:R/((p d)%:R+1)^+4 : RR) 0.
Proof.
move=> hp hn.
have hlog := sparse_log_sqrt_cofinal hp 0%N.
have hsq := sparse_square_limit (sparse_square_limit hlog).
have he q : ((ln(q%:R : RR)^+0/Num.sqrt q%:R)^+2)^+2 = (q%:R^+2)^-1.
  by rewrite expr0 mul1r exprVn (sqr_sqrtr (ler0n RR q)) exprVn.
have hi : family_sequence_limit (fun d => ((p d)%:R^+2)^-1 : RR) 0.
  move=> eps eps0; have [D hD] := hsq eps eps0.
  exists D=>d dD; have := hD d dD.
  by rewrite he !expr0n.
have hm : family_sequence_limit
    (fun d => 4*((n d)%:R/(p d)%:R^+2)*((p d)%:R^+2)^-1 : RR) 0.
  apply/reserve_scalar_tends_cvg.
  have -> : (0 : RR) = (4*alpha)*0 by rewrite mulr0.
  apply: cvgM; last by apply/reserve_scalar_tends_cvg; exact: hi.
  apply: cvgM; first exact: cvg_cst.
  by apply/reserve_scalar_tends_cvg; exact: hn.
move=> eps eps0.
have [D hD] := hm eps eps0.
have [Q hQ] := hp 1%N.
exists (maxn D Q)=>d; rewrite geq_max=>/andP[dD dQ].
have p0 : (0 : RR) < (p d)%:R by rewrite ltr0n; exact: hQ.
have p40 : (0 : RR) < (p d)%:R^+4 by rewrite exprn_gt0.
have pp0 : (0 : RR) < (p d)%:R+1 by rewrite addr_gt0.
have pp40 : (0 : RR) < ((p d)%:R+1)^+4 by rewrite exprn_gt0.
have pp : ((p d)%:R)^+4 <= ((p d)%:R+1)^+4 :> RR.
  rewrite ler_pXn2r ?nnegrE ?ler0n ?addr_ge0 //.
  by rewrite lerDl.
have num0 : (0 : RR) <= 4*(n d)%:R by rewrite mulr_ge0 ?ler0n.
have lower0 : (0 : RR) <= 4*(n d)%:R/((p d)%:R+1)^+4.
  exact: divr_ge0 num0 (ltW pp40).
have bound : 4*(n d)%:R/((p d)%:R+1)^+4 <=
    4*((n d)%:R/(p d)%:R^+2)*((p d)%:R^+2)^-1 :> RR.
  have heq : 4*((n d)%:R/(p d)%:R^+2)*((p d)%:R^+2)^-1 =
      4*(n d)%:R/((p d)%:R)^+4 :> RR.
    have hh : 4*((n d)%:R/(p d)%:R^+2)*((p d)%:R^+2)^-1 =
      (4*(n d)%:R)*(((p d)%:R^+2)^-1*((p d)%:R^+2)^-1) :> RR by ring.
    by rewrite hh -invfM -exprD.
  rewrite heq.
  apply: ler_wpM2l; first exact: num0.
  by rewrite lef_pV2 ?posrE.
have upper := hD d dD.
rewrite subr0 (ger0_norm lower0).
apply: le_lt_trans bound _.
apply: le_lt_trans (ler_norm _) _.
by rewrite subr0 in upper.
Qed.


Theorem sparse_target_log_rate (K : R) (h p : nat -> nat) :
  family_cofinal p ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit
    (fun d => ln ((p d)%:R : RR)^+4/(p d)%:R *
      ((252*K^+2*(Num.sqrt (h d)%:R+1)+8*K) *
        (1+4*ln((p d)%:R+1)))) 0.
Proof.
move=> hp hh.
have hl := (reserve_scalar_tends_cvg _ _).1 (sparse_target_log_sqrt_limit hp).
have hs := (reserve_scalar_tends_cvg _ _).1 (sparse_target_scale_limit K hp hh).
have hc := @cvgM RR nat \oo eventually_filter _ _ _ _ hl hs.
rewrite mul0r in hc.
apply/reserve_scalar_tends_cvg.
have he : (fun d =>
    (ln ((p d)%:R : RR)^+4/Num.sqrt (p d)%:R * (1+4*ln((p d)%:R+1))) *
    ((252*K^+2*(Num.sqrt (h d)%:R+1)+8*K)/Num.sqrt (p d)%:R)) =
  (fun d => ln ((p d)%:R : RR)^+4/(p d)%:R *
    ((252*K^+2*(Num.sqrt (h d)%:R+1)+8*K) * (1+4*ln((p d)%:R+1)))).
  apply: funext => d.
  have ee :
      (ln ((p d)%:R : RR)^+4/Num.sqrt (p d)%:R * (1+4*ln((p d)%:R+1))) *
      ((252*K^+2*(Num.sqrt (h d)%:R+1)+8*K)/Num.sqrt (p d)%:R) =
      ln ((p d)%:R : RR)^+4 *
      ((252*K^+2*(Num.sqrt (h d)%:R+1)+8*K) * (1+4*ln((p d)%:R+1))) *
      ((Num.sqrt (p d)%:R)^-1*(Num.sqrt (p d)%:R)^-1) by ring.
  rewrite ee -invfM -expr2 sqr_sqrtr ?ler0n //.
  ring.
by rewrite -he.
Qed.

Theorem sparse_target_moment_rate (K : R) (n h p : nat -> nat) (alpha : RR) :
  family_cofinal p ->
  family_sequence_limit (fun d => (h d)%:R/(p d)%:R : RR) 0 ->
  family_sequence_limit (fun d => (n d)%:R/(p d)%:R^+2 : RR) alpha ->
  family_sequence_limit
    (fun d => (n d)%:R*(8*K^+4*(h d)%:R+8)/(p d)%:R^+3 : RR) 0.
Proof.
move=> hp hh hn.
have hi := (reserve_scalar_tends_cvg _ _).1 (sparse_target_inverse_limit hp).
move/reserve_scalar_tends_cvg: hh => hh.
move/reserve_scalar_tends_cvg: hn => hn.
have hc : (fun d => ((n d)%:R/(p d)%:R^+2)*
    (8*K^+4*((h d)%:R/(p d)%:R)+8*((p d)%:R)^-1)) @ \oo -->
    (alpha*(8*K^+4*0+8*0) : RR).
  apply: cvgM; first exact: hn.
  apply: cvgD.
  - apply: cvgM; [exact: cvg_cst | exact: hh].
  - apply: cvgM; [exact: cvg_cst | exact: hi].
rewrite !mulr0 add0r mulr0 in hc.
apply/reserve_scalar_tends_cvg.
have he : (fun d => (n d)%:R*(8*K^+4*(h d)%:R+8)/(p d)%:R^+3 : RR) =
    (fun d => ((n d)%:R/(p d)%:R^+2)*
      (8*K^+4*((h d)%:R/(p d)%:R)+8*((p d)%:R)^-1)).
  apply: funext => d.
  by rewrite [(p d)%:R^+3]exprS invfM; ring.
by rewrite he.
Qed.
