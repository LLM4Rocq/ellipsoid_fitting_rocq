(* Telescoping of powers of noncommuting matrices, and operator bounds for
   sums over a finite family of matrices.

   pmcr_power_difference: A^p - R^p = sum_(j < p) A^j (A - R) R^(p-j-1).
   pmcr_family_power_difference: summed over a finite family,
     sum_c ((R_c - D_c)^p - R_c^p)
       = - sum_(j < p) sum_c (R_c - D_c)^j D_c R_c^(p-j-1).
   Here pmlo_opb M c says |M v| <= c |v| for every v, and the energy bound
   pmfc_energy_bound F b says sum_i |F_i u|^2 <= b^2 |u|^2 for every u.
   pmcr_mixed_powers: if the A_i and D_i are symmetric, every A_i and B_i
     has operator norm at most t, every D_i at most m, 0 <= m <= b, and the
     families A, B, D have energy bounds t, t, b, then for j + l > 0 the
     operator norm of sum_i A_i^j D_i B_i^l is at most t^(j+l) b. The proof
     splits each term into a product of two factors and applies the
     Cauchy-Schwarz bound pmfc_energy_product.
   pmcr_power_sum_error: under the same bounds for the families B - D, B
     and D, for p >= 2 the operator norm of sum_i ((B_i - D_i)^p - B_i^p)
     is at most p t^(p-1) b. *)
From Stdlib Require Import Reals List FunctionalExtensionality Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions
  Geometry.HeadCoefficients Geometry.HeadFrobenius Cone.ConditionOperator
  SquareFree.EdgeLower SquareFree.MatrixFamilyCauchy
  SquareFree.MatrixFamilyCauchyPowers.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma pmcr_power_difference n (A R : 'M[R]_n) p :
  A^+p-R^+p = \sum_(j<p) (A^+j *m (A-R) *m R^+(p-j.+1)).
Proof.
elim: p=>[|p IH]; first by rewrite !expr0 subrr big_ord0.
rewrite big_ord_recl /= subn1 /= expr0 mul1mx.
have ES : (\sum_(j<p) (A^+j.+1 *m (A-R) *m R^+(p.+1-j.+2))) =
  A *m (\sum_(j<p) (A^+j *m (A-R) *m R^+(p-j.+1))).
{ rewrite mulmx_sumr; apply: eq_bigr=>j _.
  by rewrite subSS (exprS A) -mulmxE !mulmxA. }
rewrite ES -IH mulmxBl mulmxBr.
have EA : A *m A^+p = A^+p.+1 by rewrite exprS mulmxE.
have ER : R *m R^+p = R^+p.+1 by rewrite exprS mulmxE.
rewrite EA ER.
by rewrite [in RHS]addrC addrA subrK.
Qed.

Lemma pmcr_family_power_difference (I : finType) n (R D : I -> 'M[R]_n) p :
  (\sum_c ((R c-D c)^+p-(R c)^+p)) =
  - (\sum_(j<p) \sum_c ((R c-D c)^+j *m D c *m (R c)^+(p-j.+1))).
Proof.
under eq_bigr do rewrite pmcr_power_difference.
rewrite exchange_big -sumrN; apply: eq_bigr=>j _.
rewrite -sumrN; apply: eq_bigr=>c _.
have E : R c-D c-R c = -D c by rewrite addrAC subrr add0r.
by rewrite E mulmxN mulNmx.
Qed.

Lemma pmcr_energy_bound_le (I : finType) n (F : I -> 'M[R]_n) a b :
  pmfc_energy_bound I n F a -> a <= b -> pmfc_energy_bound I n F b.
Proof.
move=>[Ha HF] Hab; have Hb := le_trans Ha Hab; split=>// u.
apply: le_trans (HF u) _; apply: ler_wpM2r; first exact: pmh_vec_sqr_ge0.
by rewrite ler_sqr ?nnegrE.
Qed.

Theorem pmcr_mixed_powers (I : finType) n (A B D : I -> 'M[R]_n) (t m b : R) :
  (forall i, (A i)^T = A i) -> (forall i, (D i)^T = D i) ->
  0 <= m -> m <= b ->
  (forall i, pmlo_opb n (A i) t) -> (forall i, pmlo_opb n (B i) t) ->
  (forall i, pmlo_opb n (D i) m) ->
  pmfc_energy_bound I n A t -> pmfc_energy_bound I n B t -> pmfc_energy_bound I n D b ->
  forall j ell, (0 < j+ell)%N ->
  pmlo_opb n (\sum_i ((A i)^+j *m D i *m (B i)^+ell)) (t^+(j+ell)*b)%R.
Proof.
move=>HA HD Hm Hmb OA OB OD EA EB ED j ell Hpos.
have Ht := proj1 EA.
have EDt : pmfc_energy_bound I n (fun i => (D i)^T) b.
{ have E : (fun i => (D i)^T) = D by apply: functional_extensionality=>i; exact: HD.
  by rewrite E. }
have EAt p : pmfc_energy_bound I n (fun i => ((A i)^+p.+1)^T) (t^+p.+1).
{ have E : (fun i => ((A i)^+p.+1)^T) = (fun i => (A i)^+p.+1).
  { apply: functional_extensionality=>i; exact: pmlo_trmx_exp. }
  rewrite E; exact: (pmfc_energy_bound_power I n A t OA EA p). }
case: j Hpos=>[|j] Hpos.
- case: ell Hpos=>[//|ell] _; rewrite add0n.
  under eq_bigr do rewrite expr0 mul1mx.
  have H := pmfc_energy_product I n D (fun i => (B i)^+ell.+1) b (t^+ell.+1)
    EDt (pmfc_energy_bound_power I n B t OB EB ell).
  by rewrite Rmult_comm in H.
- case: ell Hpos=>[|ell] _.
  + rewrite addn0; under eq_bigr do rewrite expr0 mulmx1.
    exact: (pmfc_energy_product I n (fun i => (A i)^+j.+1) D (t^+j.+1) b (EAt j) ED).
  + have EAj := pmfc_energy_bound_power I n A t OA EA j.
    have EBl := pmfc_energy_bound_power I n B t OB EB ell.
    have EF := pmfc_energy_bound_mul_left I n D (fun i => (A i)^+j.+1) m (t^+j.+1) Hm OD EAj.
    have EFt : pmfc_energy_bound I n (fun i => ((A i)^+j.+1 *m D i)^T) (m*t^+j.+1)%R.
    { have E : (fun i => ((A i)^+j.+1 *m D i)^T) = (fun i => D i *m (A i)^+j.+1).
      { apply: functional_extensionality=>i; by rewrite trmx_mul HD (pmlo_trmx_exp n _ _ (HA i)). }
      by rewrite E. }
    have HP := pmfc_energy_product I n (fun i => (A i)^+j.+1 *m D i)
      (fun i => (B i)^+ell.+1) (m*t^+j.+1)%R (t^+ell.+1) EFt EBl.
    apply: (pmlo_opb_le n _ _ _ HP).
    change (m*t^+j.+1*t^+ell.+1 <= t^+(j.+1+ell.+1)*b).
    rewrite exprD.
    have E : m*t^+j.+1*t^+ell.+1 = (t^+j.+1*t^+ell.+1) * m by ring.
    rewrite E; apply: ler_wpM2l=>//; by apply: mulr_ge0; exact: exprn_ge0.
Qed.

Theorem pmcr_power_sum_error (I : finType) n (B D : I -> 'M[R]_n) (t m b : R) :
  (forall i, (B i)^T = B i) -> (forall i, (D i)^T = D i) ->
  0 <= m -> m <= b ->
  (forall i, pmlo_opb n (B i-D i) t) -> (forall i, pmlo_opb n (B i) t) ->
  (forall i, pmlo_opb n (D i) m) ->
  pmfc_energy_bound I n (fun i => B i-D i) t ->
  pmfc_energy_bound I n B t -> pmfc_energy_bound I n D b ->
  forall p, (2 <= p)%N ->
  pmlo_opb n (\sum_i ((B i-D i)^+p-(B i)^+p)) (p%:R*t^+p.-1*b).
Proof.
move=>HB HD Hm Hmb OA OB OD EA EB ED p Hp.
have HA i : (B i-D i)^T = B i-D i by rewrite raddfB /= HB HD.
have Hj (j : 'I_p) : pmlo_opb n
  (\sum_i ((B i-D i)^+j *m D i *m (B i)^+(p-j.+1))) (t^+p.-1*b).
{ have Heq : (j+(p-j.+1) = p.-1)%N.
  { have Hj0 : Nat.lt j p by exact/ssrnat.ltP.
    have Hp0 : Nat.le 2 p by exact/ssrnat.leP.
    rewrite -plusE -minusE; lia. }
  have Hpos : (0 < j+(p-j.+1))%N by rewrite Heq -subn1 subn_gt0.
  have H := pmcr_mixed_powers I n (fun i => B i-D i) B D t m b HA HD Hm Hmb
    OA OB OD EA EB ED j (p-j.+1) Hpos.
  by rewrite Heq in H. }
have HS := pmlo_opb_sum n [the finType of 'I_p]
  (fun j => \sum_i ((B i-D i)^+j *m D i *m (B i)^+(p-j.+1)))
  (fun _ => (t^+p.-1*b)%R) Hj.
rewrite sumr_const card_ord in HS.
have HN := pmlo_opb_scale n _ _ (-1) HS.
rewrite normrN normr1 mul1r scaleN1r in HN.
rewrite pmcr_family_power_difference.
apply: (pmlo_opb_le n _ _ _ HN).
change ((t^+p.-1*b)*+p <= p%:R*t^+p.-1*b).
by rewrite -mulr_natl mulrA.
Qed.
