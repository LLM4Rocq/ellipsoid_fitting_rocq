(* Scalar normalization and small-tolerance bounds for column remainders. *)
From Stdlib Require Import Reals List Lia FunctionalExtensionality.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryHeadCoefficients
  PaperMainGeometryHeadFrobenius PaperMainSquarefreeEdgeLower PaperMainColumnRemainder
  PaperMainColumnRemainderBounds PaperMainColumnRemainderPowers PaperMainColumnRemainderCross.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma pmcr_tolerance_energy (U m r : R) :
  0 <= U -> 0 <= m -> 0 <= r -> r <= 1 -> m <= U*r^+2 ->
  [ /\ 0 <= U*r, m <= U*r, U*r <= U & m*U <= (U*r)^+2 ].
Proof.
move=>HU Hm Hr Hr1 Hmr.
have Hrr : r^+2 <= r.
{ rewrite expr2 -[leRHS]mulr1; exact: ler_wpM2l. }
have HUr : 0 <= U*r by exact: mulr_ge0.
have HmUr : m <= U*r := le_trans Hmr (ler_wpM2l HU Hrr).
have HUrU : U*r <= U by rewrite -[leRHS]mulr1; exact: ler_wpM2l.
have Hsquare : m*U <= (U*r)^+2.
{ have H := ler_wpM2r HU Hmr.
  have E : (U*r^+2)*U = (U*r)^+2 by ring.
  by rewrite E in H. }
by split.
Qed.

Lemma pmcr_normalization (n M : R) :
  0 < n -> 0 < M ->
  let kap := (Num.sqrt (n*M))^-1 in
  0 < kap /\ kap^+2*n*M = 1 /\ kap^+2*n = M^-1.
Proof.
move=>Hn HM /=.
have Hprod : 0 < n*M by exact: mulr_gt0.
have Hsqrt : 0 < Num.sqrt (n*M) by rewrite sqrtr_gt0.
have Hsq : ((Num.sqrt (n*M))^-1)^+2 = (n*M)^-1.
{ by rewrite exprVn sqr_sqrtr ?ltW. }
split; first by rewrite invr_gt0.
split.
- by rewrite Hsq -mulrA mulVf ?gt_eqF.
- by rewrite Hsq invfM mulrAC mulVf ?gt_eqF // mul1r.
Qed.

Lemma pmcr_normalized_count_bound (n M kap : R) :
  0 <= kap -> 0 < n -> 0 < M -> kap^+2*n*M = 1 -> n <= 4*M -> kap*n <= 2.
Proof.
move=>Hkap Hn HM HE HnM.
have Hsq : (kap*n)^+2 <= 2^+2.
{ have H := ler_wpM2l (mulr_ge0 (sqr_ge0 kap) (ltW Hn)) HnM.
  have E : kap^+2*n*(4*M) = 4*(kap^+2*n*M) by ring.
  rewrite E HE mulr1 in H.
  have E2 : kap^+2*n*n = (kap*n)^+2 by ring.
  rewrite E2 in H.
  have E4 : (2%:R : R)^+2 = 4 by rewrite -natrX.
  by rewrite E4. }
have Hkn : 0 <= kap*n by apply: mulr_ge0=>//; exact: ltW Hn.
move: Hsq; by rewrite ler_sqr ?nnegrE //.
Qed.

Lemma pmcr_cross_radius_identity (kap U r : R) p :
  kap^+p.+1 * ((p.+1)%:R*(2*U)^+p*(U*r)) =
  (p.+1)%:R * (2*(kap*U))^+p * (kap*U) * r.
Proof. rewrite !exprMn exprS; ring. Qed.

Lemma pmcr_cross_radius_bound (kap U r h : R) p :
  0 <= kap -> 0 <= U -> 0 <= r -> kap*U <= h ->
  kap^+p.+1 * ((p.+1)%:R*(2*U)^+p*(U*r)) <=
  (p.+1)%:R * (2*h)^+p.+1 * r.
Proof.
move=>Hkap HU Hr Hh.
have HkU : 0 <= kap*U by exact: mulr_ge0.
have Hh0 := le_trans HkU Hh.
have Htwo : kap*U <= 2*h.
{ apply: le_trans Hh _.
  have H12 : (1%:R <= 2%:R :> R) by rewrite ler_nat.
  have H := ler_wpM2r Hh0 H12; by rewrite mul1r in H. }
have Ha0 : 0 <= 2*(kap*U) by apply: mulr_ge0=>//.
have Hb0 : 0 <= 2*h by apply: mulr_ge0=>//.
have Hab : 2*(kap*U) <= 2*h by apply: ler_wpM2l=>//.
have Hpow : (2*(kap*U))^+p <= (2*h)^+p by apply: lerXn2r=>//.
have Hprod := ler_pM (exprn_ge0 p Ha0) HkU Hpow Htwo.
rewrite pmcr_cross_radius_identity exprSr.
apply: ler_wpM2r=>//.
rewrite -!mulrA; apply: ler_wpM2l; first exact: ler0n.
exact: Hprod.
Qed.

Lemma pmcr_coefficient_radius_identity (kap n U delta : R) p :
  kap^+p.+1 * (n^+p*(2^+p-1)*delta*U) =
  (kap*n)^+p*(kap*U)*(2^+p-1)*delta.
Proof. rewrite exprS exprMn; ring. Qed.

Lemma pmcr_coefficient_radius_bound (a b h delta : R) p :
  0 <= a -> a <= 2 -> 0 <= b -> b <= h -> 0 <= delta ->
  a^+p*b*(2^+p-1)*delta <= (4^+p*h)*delta.
Proof.
move=>Ha Ha2 Hb Hbh Hd.
have H20 : 0 <= (2%:R : R) by rewrite ler0n.
have Hpow : a^+p <= 2^+p by apply: lerXn2r=>//.
have He : (2%:R : R)^+p-1 <= 2^+p by rewrite lerBlDr lerDl.
have Hpa := ler_pM (exprn_ge0 p Ha) Hb Hpow Hbh.
have Hpa0 : 0 <= a^+p*b by apply: mulr_ge0=>//; exact: exprn_ge0.
have Hstep := ler_wpM2l Hpa0 He.
have Hstep2 := ler_wpM2r (exprn_ge0 p H20) Hpa.
have Hprod := le_trans Hstep Hstep2.
have E2 : (2%:R : R)*2 = 4 by rewrite -natrM.
have E : (2%:R : R)^+p*h*2^+p = 4^+p*h.
{ by rewrite mulrAC -exprMn E2. }
rewrite E in Hprod; exact (ler_wpM2r Hd Hprod).
Qed.

Lemma pmcr_diagonal_radius_bound (s delta : R) k :
  0 <= s -> s <= 2 -> 0 <= delta -> s^+k*delta <= 2^+k*delta.
Proof.
move=>Hs Hs2 Hd.
have H20 : 0 <= (2%:R : R) by rewrite ler0n.
have Hp : s^+k <= 2^+k by apply: lerXn2r=>//.
exact (ler_wpM2r Hd Hp).
Qed.
