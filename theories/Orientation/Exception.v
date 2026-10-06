(* For a fixed orientation, a small measurable event contains every sample
   with a low-risk admissible candidate.
   paper_main_orientation_exception: let O be orthogonal of size
   d = r + S mi, let N > 0 with c d^2 <= N, and assume the margin condition
   a + 4 (L + 1) delta + 3 C / (c beta) <= z, where C is the entropy
   constant paper_main_gordon_entropy_constant (delta / (L + 3)). Assume
   also that, for every finite family of states (H_j, b_j, B_j) with H_j and
   B_j PSD, |H_j|_F^2 + |B_j|_F^2 in [1/4, 4] and B_j of operator norm at
   most eps, the event that the finite hybrid functional
   paper_main_hybrid_finite_data is at most z is measurable with
   probability at most p. Then there is a measurable event E of
   probability at most p that contains every sample whose feature Gram
   matrix is at most K I with K <= N L^2 and which has an admissible
   candidate (A, b) for O (paper_main_orientation_admissible) of quadratic
   risk at most a. The proof takes the finite family of states of
   paper_main_orientation_prior and lets E be the preimage of that event
   under the rotation by O, which preserves the Gaussian law;
   paper_main_entropy_density_bound bounds the entropy term ln s / (beta N)
   by 3 C / (c beta). *)
From Stdlib Require Import Reals List Lia Lra Psatz Classical_Prop.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions
  Geometry.Homogeneous Feature.GramBlocks Feature.LossControl
  Cone.ConditionOperator Gordon.Entropy Gordon.EntropyMargin
  Unsat.SupercriticalParameters Orientation.Witness Orientation.Prior
  Orientation.Rotation Hybrid.FiniteArray.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma paper_main_entropy_density_bound d N s E beta c :
  (0<N)%coq_nat -> (0<=E)%Rcoq -> (0<beta)%Rcoq -> (0<c)%Rcoq ->
  (c*(INR d)^2<=INR N)%Rcoq -> (Rpower.ln(INR s)<=3*E*(INR d)^2)%Rcoq ->
  (Rpower.ln(INR s)/(beta*INR N)<=3*E/(c*beta))%Rcoq.
Proof.
move=> HN HE Hb Hc Hdensity Hcard.
have HNpos : (0<INR N)%Rcoq by apply lt_0_INR.
have Hq : (0<=3*E/c)%Rcoq.
{ apply Rmult_le_pos; [lra|apply Rlt_le,Rinv_0_lt_compat; exact Hc]. }
have HH := Rmult_le_compat_l _ _ _ Hq Hdensity.
replace (3*E/c*(c*(INR d)^2))%Rcoq with (3*E*(INR d)^2)%Rcoq in HH by (field; lra).
apply paper_main_unsat_div_le; [apply Rmult_lt_0_compat; assumption|].
replace (3*E/(c*beta)*(beta*INR N))%Rcoq with (3*E/c*INR N)%Rcoq by (field; lra).
lra.
Qed.

Theorem paper_main_orientation_exception N r mi (O : 'M[R]_(r+S mi)) eps L delta beta c a z p :
  O^T *m O = 1%:M -> (0<N)%coq_nat ->
  (0<=L)%Rcoq -> (0<delta)%Rcoq -> (0<beta)%Rcoq -> (0<c)%Rcoq -> (0<=p)%Rcoq ->
  (c*(INR(r+S mi))^2<=INR N)%Rcoq ->
  (a+4*(L+1)*delta+3*paper_main_gordon_entropy_constant(delta/(L+3))/(c*beta)<=z)%Rcoq ->
  (forall s (Hs : nat -> 'M[R]_r) bs (Bs : nat -> 'M[R]_(S mi)),
    (0<s)%coq_nat ->
    (forall j, (j<s)%coq_nat -> paper_main_psd(Hs j) /\ paper_main_psd(Bs j) /\
      1/4<=paper_main_frobenius(Hs j)^+2+paper_main_frobenius(Bs j)^+2<=4 /\
      paper_main_cone_opnorm_le (Bs j) eps) ->
    measurable [set x : paper_main_sample N (r+S mi) |
      (paper_main_hybrid_finite_data N r mi beta (List.seq 0 s) Hs bs Bs (tval x)<=z)%R] /\
    (gaussian_product_law (N*(r+S mi))
      [set x | (paper_main_hybrid_finite_data N r mi beta (List.seq 0 s) Hs bs Bs (tval x)<=z)%R]<=p%:E)%E) ->
  exists E : set (paper_main_sample N (r+S mi)), measurable E /\
    (paper_main_probability N (r+S mi) E<=p%:E)%E /\
    forall (x : paper_main_sample N (r+S mi)) K,
      0<=K -> paper_main_loewner_le (paper_main_feature_gram N (r+S mi) x) (K *: 1%:M) ->
      (K<=INR N*L^2)%Rcoq ->
      (exists A b, paper_main_orientation_admissible r O eps L A b /\
        (paper_main_quadratic_risk N (r+S mi) x A b<=a)%Rcoq) -> E x.
Proof.
move=> HO HN HL Hdelta Hbeta Hc Hp Hdensity Hgap Htail.
case: (Classical_Prop.classic (exists A b, paper_main_orientation_admissible r O eps L A b)) => [HT|Hempty].
- have [s [Hs [bs [Bs [Hspos [Hstates [Hcard Hcover]]]]]]] :=
    paper_main_orientation_prior r mi O eps L delta HO HL Hdelta HT.
  have [mF PF] := Htail s Hs bs Bs Hspos Hstates.
  pose F : set (paper_main_sample N (r+S mi)) := [set x |
    (paper_main_hybrid_finite_data N r mi beta (List.seq 0 s) Hs bs Bs (tval x)<=z)%R].
  pose E := paper_main_orientation_rotate N (r+S mi) O @^-1` F.
  have mE : measurable E.
  { have H := paper_main_orientation_rotate_measurable N (r+S mi) O measurableT F mF.
    by rewrite setTI in H. }
  have PE : (paper_main_probability N (r+S mi) E<=p%:E)%E.
  { rewrite /paper_main_probability /E (paper_main_orientation_rotate_law N (r+S mi) O F HO mF).
    exact PF. }
  exists E; split=> //; split=> // x K HK HG Hscale HW.
  have HZ := Hcover N x K beta a HN HK Hbeta HG Hscale HW.
  have HE : (0<=paper_main_gordon_entropy_constant(delta/(L+3)))%Rcoq.
  { left; apply paper_main_gordon_entropy_constant_positive; apply Rdiv_lt_0_compat; lra. }
  have Hentropy := paper_main_entropy_density_bound (r+S mi) N s _ beta c
    HN HE Hbeta Hc Hdensity Hcard.
  apply/RleP.
  change (paper_main_hybrid_finite_data N r mi beta (List.seq 0 s) Hs bs Bs
    (tval(paper_main_orientation_rotate N (r+S mi) O x))<=z)%Rcoq.
  lra.
- exists set0; split; first exact: measurable0.
  split.
  + rewrite /paper_main_probability measure0; apply/RleP; exact Hp.
  + move=> x K HK HG Hscale [A [b [HA _]]]; exfalso; apply Hempty; by exists A,b.
Qed.
