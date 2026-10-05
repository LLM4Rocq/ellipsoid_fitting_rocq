(* Concentration of the finite-prior data soft loss on full data rows.

   Z_data (PaperMainHybridFiniteArray) is the entropy-shifted normalized
   finite soft minimum of continuous row losses with values in [0, 1] on N
   full data rows (g, y) of r + (mi + 1) coordinates. The A25 tails apply
   with row oscillation 1/N:
     P (Z_data <= E Z_data - t) <= exp (- N t^2 / 2),
   and the same for the upper tail. With the mean bound of
   PaperMainHybridFiniteMean this gives, for t > 0, the measurable event
     Z_data <= e (1 - exp (- c d^2)) - (2 eta + C eps S) - t
   of probability at most exp (- N t^2 / 2). The constants do not depend on
   the prior, its size, the offsets or the dimensions; C depends only on
   beta and eta, and kappa, e, c, d0 only on gamma. *)
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

(* 1. The A25 tails for Z_data on full data rows. *)

Theorem paper_main_hybrid_finite_data_lower_tail N r mi beta (I : list nat) Hs bs
    (Bs : nat -> 'M[R]_(S mi)) (t : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq -> (0 < t)%Rcoq ->
  measurable [set x : (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R) |
    (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
     gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
       (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) - t)%R] /\
  (gaussian_product_law (N * (r + S mi)%coq_nat)
     [set x | (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x) <=
       gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
         (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) - t)%R] <=
   ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> HN HI Hb Ht.
exact: (paper_main_softmin_lower_tail (r + S mi)%coq_nat N beta I
  (paper_main_hybrid_finite_data_loss r mi Hs bs Bs) t HN HI Hb Ht
  (fun i j _ _ => paper_main_hybrid_finite_data_loss_continuous r mi Hs bs Bs i j)
  (fun i j xs _ _ _ => paper_main_hybrid_finite_data_loss_bounds r mi Hs bs Bs i j xs)).
Qed.

Theorem paper_main_hybrid_finite_data_upper_tail N r mi beta (I : list nat) Hs bs
    (Bs : nat -> 'M[R]_(S mi)) (t : R) :
  (0 < N)%N -> I <> nil -> (0 < beta)%Rcoq -> (0 < t)%Rcoq ->
  measurable [set x : (N * (r + S mi)%coq_nat).-tuple (measurableTypeR R) |
    (gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
       (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) + t <=
     paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x))%R] /\
  (gaussian_product_law (N * (r + S mi)%coq_nat)
     [set x | (gaussian_iterated_expectation (N * (r + S mi)%coq_nat)
         (paper_main_hybrid_finite_data N r mi beta I Hs bs Bs) + t <=
       paper_main_hybrid_finite_data N r mi beta I Hs bs Bs (tval x))%R] <=
   ((exp (- (INR N * t ^ 2) / 2))%Rcoq)%:E)%E.
Proof.
move=> HN HI Hb Ht.
exact: (paper_main_softmin_upper_tail (r + S mi)%coq_nat N beta I
  (paper_main_hybrid_finite_data_loss r mi Hs bs Bs) t HN HI Hb Ht
  (fun i j _ _ => paper_main_hybrid_finite_data_loss_continuous r mi Hs bs Bs i j)
  (fun i j xs _ _ _ => paper_main_hybrid_finite_data_loss_bounds r mi Hs bs Bs i j xs)).
Qed.

(* 2. The finite-prior data tail below the mean bound. *)

Theorem paper_main_hybrid_finite_data_tail (gamma beta eta : R) :
  (1 / 4 < gamma)%Rcoq -> (0 < beta)%Rcoq -> (0 < eta)%Rcoq ->
  exists (C kappa e c : R) (d0 : nat),
    (0 <= C)%Rcoq /\ (0 < kappa)%Rcoq /\ (kappa <= gamma / 2)%Rcoq /\
    (0 < e)%Rcoq /\ (0 < c)%Rcoq /\
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
move=> Hg Hb He.
have [C [kappa [e [c [d0 [HC [Hk [Hk2 [He' [Hc Hmean]]]]]]]]]] :=
  paper_main_hybrid_finite_data_mean gamma beta eta Hg Hb He.
exists C, kappa, e, c, d0; do 5 (split => //).
move=> d N r mi I Hs bs Bs eps Sf t Hd HN Hr Hmi HI Heps HS Ht HHs HBs Hn HO HF.
have Hg0 : (0 < gamma)%Rcoq by lra.
have Hd1 : (0 < d)%N by apply: leq_trans Hmi; rewrite addn1.
have HNpos := paper_main_hybrid_finite_density_pos gamma kappa d N Hg0 Hk2 Hd1 HN.
have HN' : (0 < N)%N by apply/ssrnat.ltP.
have Hm := Hmean d N r mi I Hs bs Bs eps Sf Hd HN Hr Hmi HI Heps HS HHs HBs Hn HO HF.
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
