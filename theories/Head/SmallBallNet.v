(* The parameter net for the uniform head small ball. For a symmetric H of
   size n+1 and real b let
     sigma2(H, b) = 2 |H|_F^2 + b^2,
     A(g) = g g^T - I                      (paper_main_head_small_ball_feature),
     Y(H, b, g) = g^T H g - Tr H - b = <H, A(g)> - b.
   - Value difference: |Y(H, b, g) - Y(H', b', g)|
       <= sqrt (sigma2 (H - H', b - b')) * sqrt (|A(g)|_F^2 / 2 + 1),
     by Cauchy-Schwarz in R^2.
   - Net. With D = paper_main_symmetric_dimension n, the code
     u = (sqrt 2 * code(H), b) in R^(D+1) (public symmetric coordinates of
     Cone.GaussianCoordinates) has squared norm sigma2(H, b), and the
     squared distance of two codes is sigma2 of the difference. The fixed
     entropy grid of Gordon.Entropy on the coded unit parameter
     sphere gives, for every eps > 0, symmetric H_t and b_t (t < s) with
     sigma2 (H_t, b_t) = 1, covering the unit parameter sphere at sigma2
     distance eps^2, with s = length (paper_main_gordon_entropy_grid (D+1) eps)
     and ln s <= C(eps) (D + 1). *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From EllipsoidFitting Require Import Soft.Definitions Soft.Extrema
  Analysis.FiniteSumAlgebra PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadFeature
  Gordon.ProcessCovariance Gordon.Nets Gordon.Entropy
  Gaussian.FeatureCoordinates Cone.GaussianCoordinates Head.SectionApproxNets.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Open Scope R_scope.

Definition paper_main_head_small_ball_sigma2 {d : nat} (H : 'M[R]_d) (b : R) : R :=
  2 * paper_main_pairing H H + b ^ 2.

Definition paper_main_head_small_ball_feature {d : nat} (g : 'cV[R]_d) : 'M[R]_d :=
  (\matrix_(i, j) (g i 0 * g j 0 - (i == j)%:R))%R.

Definition paper_main_head_small_ball_value {d : nat} (H : 'M[R]_d) (b : R) (g : 'cV[R]_d) : R :=
  paper_main_quadratic_form H g - paper_main_trace H - b.

Lemma paper_main_head_small_ball_value_pairing {d : nat} (H : 'M[R]_d) (b : R) (g : 'cV[R]_d) :
  paper_main_head_small_ball_value H b g =
  paper_main_pairing H (paper_main_head_small_ball_feature g) - b.
Proof.
rewrite /paper_main_head_small_ball_value /paper_main_quadratic_form /paper_main_trace
  /paper_main_pairing /paper_main_head_small_ball_feature !RminusE.
congr (_ - _)%R.
rewrite -sumrB; apply: eq_bigr => i _.
rewrite [in RHS](bigD1 i) //= mxE eqxx.
rewrite [in LHS](bigD1 i) //=.
have -> : (\sum_(j < d | j != i)
    H i j * (\matrix_(i0, j0) (g i0 0 * g j0 0 - (i0 == j0)%:R)) i j =
    \sum_(j < d | j != i) g i 0 * H i j * g j 0)%R.
  by apply: eq_bigr => j Hj; rewrite mxE eq_sym (negbTE Hj) subr0 mulrCA mulrA.
rewrite /= -[in RHS](mulr1 (H i i)).
rewrite mulrBr addrAC.
congr (_ + _)%R.
by rewrite !mulr1 [in RHS]mulrCA mulrA.
Qed.

(* Cauchy-Schwarz in R^2 and the value difference. *)

Lemma paper_main_head_small_ball_cs2 (x y z : R) :
  0 <= x -> 0 <= y ->
  x * y + Rabs z <= sqrt (2 * x ^ 2 + z ^ 2) * sqrt (y ^ 2 / 2 + 1).
Proof.
move=> Hx Hy.
have Hz := Rabs_pos z.
have Hz2 : Rabs z ^ 2 = z ^ 2 by exact: pow2_abs.
have H1 : 0 <= 2 * x ^ 2 + z ^ 2 by have := pow2_ge_0 x; have := pow2_ge_0 z; lra.
have H2 : 0 <= y ^ 2 / 2 + 1 by have := pow2_ge_0 y; lra.
rewrite -sqrt_mult //.
have HL : 0 <= x * y + Rabs z by nra.
rewrite -(sqrt_pow2 (x * y + Rabs z) HL).
apply: sqrt_le_1_alt.
have Hsq := pow2_ge_0 (x - y * Rabs z / 2).
nra.
Qed.

Theorem paper_main_head_small_ball_value_diff {d : nat} (H H' : 'M[R]_d) (b b' : R)
    (g : 'cV[R]_d) :
  Rabs (paper_main_head_small_ball_value H b g - paper_main_head_small_ball_value H' b' g) <=
  sqrt (paper_main_head_small_ball_sigma2 (H - H')%R (b - b')) *
  sqrt (paper_main_frobenius (paper_main_head_small_ball_feature g) ^ 2 / 2 + 1).
Proof.
rewrite !paper_main_head_small_ball_value_pairing.
set A := paper_main_head_small_ball_feature g.
have E : paper_main_pairing H A - b - (paper_main_pairing H' A - b') =
    paper_main_pairing (H - H')%R A - (b - b').
  by rewrite pmh_pairingBl -RminusE; ring.
rewrite E.
have HB := pmh_pairing_frobenius_bound _ (H - H')%R A.
have HB' : Rabs (paper_main_pairing (H - H')%R A) <=
    paper_main_frobenius (H - H')%R * paper_main_frobenius A.
  by rewrite RabsE; apply/RleP.
have Hs : paper_main_head_small_ball_sigma2 (H - H')%R (b - b') =
    2 * paper_main_frobenius (H - H')%R ^ 2 + (b - b') ^ 2.
  by rewrite /paper_main_head_small_ball_sigma2 (RpowE (paper_main_frobenius (H - H')%R))
    pmh_frobenius_sqr.
rewrite Hs.
have Hx' : 0 <= paper_main_frobenius (H - H')%R by apply/RleP; exact: pmh_frobenius_ge0.
have Hy' : 0 <= paper_main_frobenius A by apply/RleP; exact: pmh_frobenius_ge0.
have Hcs := paper_main_head_small_ball_cs2 _ _ (b - b') Hx' Hy'.
have Htri : Rabs (paper_main_pairing (H - H')%R A - (b - b')) <=
    Rabs (paper_main_pairing (H - H')%R A) + Rabs (b - b').
  have H0 := Rabs_triang (paper_main_pairing (H - H')%R A) (- (b - b')).
  rewrite Rabs_Ropp in H0; exact: H0.
lra.
Qed.

(* The coded parameter sphere. *)

Definition paper_main_head_small_ball_pcode n (H : 'M[R]_n.+1) (b : R) : nat -> R :=
  fun k => if (k < paper_main_symmetric_dimension n)%N
    then sqrt 2 * paper_main_cone_code n H k else b.

Lemma paper_main_head_small_ball_sqrt2 : sqrt 2 * sqrt 2 = 2.
Proof. by apply: sqrt_sqrt; lra. Qed.

Lemma paper_main_head_small_ball_pcode_dist n (H H' : 'M[R]_n.+1) (b b' : R) :
  paper_main_symmetric H -> paper_main_symmetric H' ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n).+1
    (fun k => Rminus (paper_main_head_small_ball_pcode n H b k)
      (paper_main_head_small_ball_pcode n H' b' k))
    (fun k => Rminus (paper_main_head_small_ball_pcode n H b k)
      (paper_main_head_small_ball_pcode n H' b' k)) =
  paper_main_head_small_ball_sigma2 (H - H')%R (b - b').
Proof.
move=> HH HH'.
rewrite /paper_main_gordon_dot finite_sum_seq_S.
have E1 : finite_sum (fun k => Rminus (paper_main_head_small_ball_pcode n H b k)
      (paper_main_head_small_ball_pcode n H' b' k) *
    Rminus (paper_main_head_small_ball_pcode n H b k)
      (paper_main_head_small_ball_pcode n H' b' k))
    (List.seq 0 (paper_main_symmetric_dimension n)) =
  2 * paper_main_gordon_dot (paper_main_symmetric_dimension n)
    (fun k => Rminus (paper_main_cone_code n H k) (paper_main_cone_code n H' k))
    (fun k => Rminus (paper_main_cone_code n H k) (paper_main_cone_code n H' k)).
  rewrite /paper_main_gordon_dot -finite_sum_scale; apply: finite_sum_ext => k Hk.
  have Hk' : (k < paper_main_symmetric_dimension n)%N.
    by apply/ssrnat.ltP; have := proj1 (List.in_seq _ _ _) Hk; lia.
  rewrite /paper_main_head_small_ball_pcode Hk'.
  have Hs2 := paper_main_head_small_ball_sqrt2.
  transitivity ((sqrt 2 * sqrt 2) *
    ((paper_main_cone_code n H k - paper_main_cone_code n H' k) *
     (paper_main_cone_code n H k - paper_main_cone_code n H' k))); [ring | by rewrite Hs2].
rewrite E1 (paper_main_head_section_code_distance n H H' HH HH').
rewrite /paper_main_head_small_ball_pcode ltnn.
rewrite /paper_main_head_small_ball_sigma2 -(pmh_frobenius_sqr _ (H - H')%R) -RpowE; ring.
Qed.

Lemma paper_main_head_small_ball_pcode_norm n (H : 'M[R]_n.+1) (b : R) :
  paper_main_symmetric H ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n).+1
    (paper_main_head_small_ball_pcode n H b) (paper_main_head_small_ball_pcode n H b) =
  paper_main_head_small_ball_sigma2 H b.
Proof.
move=> HH.
have H0 : paper_main_symmetric (0 : 'M[R]_n.+1)%R by move=> i j; rewrite !mxE.
have E := paper_main_head_small_ball_pcode_dist n H 0%R b 0 HH H0.
have Ec : forall k, paper_main_head_small_ball_pcode n 0%R 0 k = 0.
  move=> k; rewrite /paper_main_head_small_ball_pcode.
  case: ifP => Hk //.
  by rewrite (paper_main_cone_code_basis n 0%R k H0) pmh_pairing0r Rmult_0_r.
rewrite subr0 Rminus_0_r in E.
rewrite -E /paper_main_gordon_dot; apply: finite_sum_ext => k _.
by rewrite Ec Rminus_0_r.
Qed.

Definition paper_main_head_small_ball_pset n : (nat -> R) -> Prop :=
  fun u => exists (H : 'M[R]_n.+1) (b : R), paper_main_symmetric H /\
    paper_main_head_small_ball_sigma2 H b = 1 /\
    forall k, (k < (paper_main_symmetric_dimension n).+1)%coq_nat ->
      u k = paper_main_head_small_ball_pcode n H b k.

Lemma paper_main_head_small_ball_pset_unit n u :
  paper_main_head_small_ball_pset n u ->
  paper_main_gordon_dot (paper_main_symmetric_dimension n).+1 u u = 1.
Proof.
move=> [H [b [HH [Hs Hu]]]].
rewrite -Hs -(paper_main_head_small_ball_pcode_norm n H b HH).
rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk.
have Hk' := proj1 (List.in_seq _ _ _) Hk.
have HkD : (k < (paper_main_symmetric_dimension n).+1)%coq_nat by lia.
by rewrite (Hu k HkD).
Qed.

Lemma paper_main_head_small_ball_pset_nonempty n :
  exists u, paper_main_head_small_ball_pset n u.
Proof.
exists (paper_main_head_small_ball_pcode n 0%R 1), 0%R, 1; split.
  by move=> i j; rewrite !mxE.
split => //.
by rewrite /paper_main_head_small_ball_sigma2 pmh_pairing0l Rmult_0_r Rplus_0_l pow1.
Qed.

(* The parameter net: s points of the unit parameter sphere covering it at
   sigma2 distance eps^2, with ln s <= C(eps) (D + 1). *)

Theorem paper_main_head_small_ball_param_net n (eps : R) : 0 < eps ->
  let s := List.length (paper_main_gordon_entropy_grid
    (paper_main_symmetric_dimension n).+1 eps) in
  (0 < s)%N /\ exists (Hn : nat -> 'M[R]_n.+1) (bn : nat -> R),
    (forall t, (t < s)%N -> paper_main_symmetric (Hn t) /\
       paper_main_head_small_ball_sigma2 (Hn t) (bn t) = 1) /\
    (forall (H : 'M[R]_n.+1) (b : R), paper_main_symmetric H ->
       paper_main_head_small_ball_sigma2 H b = 1 ->
       exists t, (t < s)%N /\
         paper_main_head_small_ball_sigma2 (H - Hn t)%R (b - bn t) <= eps ^ 2) /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps *
      INR (paper_main_symmetric_dimension n).+1.
Proof.
move=> He s.
have [Hs [v [[Hin Hcov] Hln]]] := paper_main_gordon_entropy_net_fixed
  (paper_main_symmetric_dimension n).+1 (paper_main_head_small_ball_pset n) eps He
  (paper_main_head_small_ball_pset_nonempty n) (@paper_main_head_small_ball_pset_unit n).
have Hseq : forall t, List.In t (List.seq 0 s) <-> (t < s)%N.
  move=> t; rewrite List.in_seq; split.
    by move=> [_ Ht]; apply/ssrnat.ltP; lia.
  by move=> /ssrnat.ltP Ht; lia.
have Hs' : (0 < s)%N by apply/ssrnat.ltP.
have Hpick : forall t, exists p : 'M[R]_n.+1 * R, (t < s)%N ->
    paper_main_symmetric p.1 /\ paper_main_head_small_ball_sigma2 p.1 p.2 = 1 /\
    forall k, (k < (paper_main_symmetric_dimension n).+1)%coq_nat ->
      v t k = paper_main_head_small_ball_pcode n p.1 p.2 k.
  move=> t; have [Ht|Ht] := ltnP t s.
    have [H [b HP]] := Hin t (proj2 (Hseq t) Ht).
    by exists (H, b).
  by exists (0%R, 1).
have [p Hp] := choice Hpick.
split => //; exists (fun t => (p t).1), (fun t => (p t).2); split.
  by move=> t Ht; have [? [? _]] := Hp t Ht.
split => //.
move=> H b HH Hsb.
have Hu : paper_main_head_small_ball_pset n (paper_main_head_small_ball_pcode n H b).
  by exists H, b; split => //; split => //.
have [t [Ht Hd]] := Hcov _ Hu.
have Ht' : (t < s)%N by apply/Hseq.
have [Hpt [_ Hvt]] := Hp t Ht'.
exists t; split => //.
have Heq : paper_main_gordon_dot (paper_main_symmetric_dimension n).+1
    (fun i => Rminus (paper_main_head_small_ball_pcode n H b i) (v t i))
    (fun i => Rminus (paper_main_head_small_ball_pcode n H b i) (v t i)) =
  paper_main_gordon_dot (paper_main_symmetric_dimension n).+1
    (fun i => Rminus (paper_main_head_small_ball_pcode n H b i)
      (paper_main_head_small_ball_pcode n (p t).1 (p t).2 i))
    (fun i => Rminus (paper_main_head_small_ball_pcode n H b i)
      (paper_main_head_small_ball_pcode n (p t).1 (p t).2 i)).
  rewrite /paper_main_gordon_dot; apply: finite_sum_ext => k Hk /=.
  have Hk' := proj1 (List.in_seq _ _ _) Hk.
  have HkD : (k < (paper_main_symmetric_dimension n).+1)%coq_nat by lia.
  by rewrite (Hvt k HkD).
by rewrite Heq (paper_main_head_small_ball_pcode_dist n H (p t).1 b (p t).2 HH Hpt) in Hd.
Qed.
