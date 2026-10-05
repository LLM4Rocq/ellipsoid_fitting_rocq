(* The hybrid gap is chosen before the soft-min parameters and comparison constant. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianProductDefinitions GaussianProduct
  GaussianCoordinateDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductContinuity PaperMainHeadSectionMeasurable
  PaperMainDefinitions PaperMainGeometryHomogeneous PaperMainConeConditionOperator
  PaperMainGaussianFeatureCoordinates
  PaperMainDataFeatureMomentsCoordinates PaperMainLossNormalizedArray
  PaperMainLossConcentrationRow PaperMainLossConcentrationTail PaperMainLossConcentrationSoftMin
  PaperMainHybridFiniteArray PaperMainHybridFiniteMean.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

From EllipsoidFitting Require Import PaperMainHybridFiniteTail.

Theorem paper_main_unsat_ordered_tail (gamma : R) :
  (1 / 4 < gamma)%Rcoq ->
  exists (kappa e c : R) (d0 : nat),
    (0 < kappa)%Rcoq /\ (kappa <= gamma / 2)%Rcoq /\
    (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
    forall beta eta, (0 < beta)%Rcoq -> (0 < eta)%Rcoq ->
    exists C, (0 <= C)%Rcoq /\
    forall (d N r mi : nat) (I : list nat) (Hs : nat -> 'M[R]_r) (bs : nat -> R)
      (Bs : nat -> 'M[R]_(S mi)) (eps Sf t : R),
      (d0 <= d)%N ->
      (Rabs (INR N - gamma * INR d ^ 2) <= kappa * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      I <> nil -> (0 <= eps)%Rcoq -> (0 <= Sf)%Rcoq -> (0 < t)%Rcoq ->
      (forall j, In j I -> paper_main_symmetric (Hs j)) ->
      (forall j, In j I -> paper_main_psd (Bs j)) ->
      (forall j, In j I ->
         (1 / 4 <= paper_main_frobenius (Hs j) ^ 2 + paper_main_frobenius (Bs j) ^ 2)%Rcoq) ->
      (forall j, In j I -> paper_main_cone_opnorm_le (Bs j) eps) ->
      (forall j, In j I -> (paper_main_frobenius (Bs j) ^ 2 <= Sf ^ 2)%Rcoq) ->
      measurable [set x : (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R) |
        (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
         (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) - t)%Rcoq)%R] /\
      (gaussian_product_law (N * (r + S mi)%coq_nat)
         [set x | (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
           (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) - t)%Rcoq)%R] <=
       ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> Hg.
have [kappa [e [c [d0 [Hk [Hk2 [He [Hc Hgoe]]]]]]]] := paper_main_hybrid_finite_goe_mean gamma Hg.
exists kappa,e,c,d0; do 4 (split => //).
move=> beta eta Hb Heta.
have [C [HC Hcomp]] := paper_main_hybrid_finite_mean_comparison beta eta Hb Heta.
exists C; split=> //.
move=> d N r mi I Hs bs Bs eps Sf t Hd HN Hr Hmi HI Heps HS Ht HHs HBs Hn HO HF.
have Hg0 : (0 < gamma)%Rcoq by lra.
have Hd1 : (0 < d)%N by apply: leq_trans Hmi; rewrite addn1.
have HNpos := paper_main_hybrid_finite_density_pos gamma kappa d N Hg0 Hk2 Hd1 HN.
have HN' : (0 < N)%N by apply/ssrnat.ltP.
have Hgm := Hgoe d N r mi beta I Hs bs Bs Hd HN Hr Hmi HI Hb HHs HBs Hn.
have Hcmp := Hcomp N r mi I Hs bs Bs eps Sf HNpos HI Heps HS
  (fun j Hj => proj1 (HBs j Hj)) HO HF.
have Hm : (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) <=
  gaussian_iterated_expectation (N * (r + S mi))%coq_nat
    (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs))%Rcoq.
{ have HA := Rle_abs (- (gaussian_iterated_expectation (N * (r + S mi))%coq_nat
      (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) -
    gaussian_iterated_expectation (N * (r + paper_main_symmetric_dimension mi))%coq_nat
      (paper_main_hybrid_finite_goe N r mi beta I Hs bs Bs))).
  rewrite Rabs_Ropp in HA; lra. }
have [mE PE] := paper_main_hybrid_finite_data_lower_tail N r mi beta I Hs bs Bs t HN' HI Hb Ht.
have mZ : measurable_fun [set: (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R)]
    ((fun x => paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x)) :
      _ -> measurableTypeR R).
  apply: gpp_joint_measurable.
  exact: (paper_main_hybrid_finite_data_regular N r mi beta I Hs bs Bs HI Hb).1.
have mE1 : measurable [set x : (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R) |
    (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
     (e * (1 - exp (- c * INR d ^ 2)) - (2 * eta + C * eps * Sf) - t)%Rcoq)%R].
  by apply: paper_main_head_section_le_measurable => //; exact: measurable_cst.
split => //.
apply: le_trans PE.
apply: le_measure; rewrite ?inE //.
move=> x Hx.
move/RleP: Hx => Hx; apply/RleP.
rewrite -RminusE.
have Hm' := Hm; rewrite (_ : (N * (r + mi.+1))%coq_nat = (N * (r + mi.+1)%coq_nat)%N) // in Hm'.
lra.
Qed.
