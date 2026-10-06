(* Small exceptional events for every fixed orientation, with all the
   parameters chosen in order.
   paper_main_unsat_orientation_constants: for gamma > 1/4 there are
   positive constants kappa <= gamma/2, e, c, L with (gamma/2) L^2 = 109,
   eps, and tau <= 1/8 with eps/2 + tau^2 <= eps, and a dimension d0, with
   the following property. Let d >= d0, O orthogonal of size d and r < d
   with r <= sqrt d + 1, and let |N - gamma d^2| <= kappa d^2 and
   exp (- c d^2) <= 1/4. Then a measurable event E of probability at most
   exp (- N (e/4)^2 / 2) contains every sample whose feature Gram matrix
   is at most K I with K <= N L^2 and which has an admissible candidate
   (A, b) for O (paper_main_orientation_admissible) of quadratic risk at
   most 16 L tau. The constants come from paper_main_unsat_ordered_tail,
   paper_main_loss_feature_constant, paper_main_unsat_net_parameters and
   paper_main_unsat_cutoff_parameters, in this order. The event E is given
   by paper_main_orientation_exception, with the tail bound of
   paper_main_unsat_ordered_tail for the finite hybrid functional. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability PaperMainDefinitions
  Geometry.Homogeneous Feature.GramBlocks Feature.LossControl
  Cone.ConditionOperator Gordon.Entropy Unsat.SupercriticalParameters
  Loss.EntropyBudget Orientation.Witness Orientation.Exception Unsat.FiniteTail
  Hybrid.FiniteArray Hybrid.FiniteMean.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_unsat_orientation_constants gamma : (1/4<gamma)%Rcoq ->
  exists (kappa e c L eps tau : R) (d0 : nat),
    (0<kappa)%Rcoq /\ (kappa<=gamma/2)%Rcoq /\
    (0<e)%Rcoq /\ (0<c)%Rcoq /\ (0<L)%Rcoq /\ (gamma/2*L^2 = 109)%Rcoq /\
    (0<eps)%Rcoq /\ (0<tau)%Rcoq /\ (tau<=1/8)%Rcoq /\ (eps/2+tau^2<=eps)%Rcoq /\
    forall N d r (O : 'M[R]_d), O^T *m O = 1%:M -> (d0<=d)%N -> (r<d)%N ->
      (INR r<=sqrt(INR d)+1)%Rcoq ->
      (Rabs(INR N-gamma*(INR d)^2)<=kappa*(INR d)^2)%Rcoq ->
      (exp(-c*(INR d)^2)<=1/4)%Rcoq ->
      exists E : set(paper_main_sample N d), measurable E /\
        (paper_main_probability N d E<=((exp(-(INR N*(e/4)^2)/2))%Rcoq)%:E)%E /\
        forall (x : paper_main_sample N d) K,
          0<=K -> paper_main_loewner_le (paper_main_feature_gram N d x) (K *: 1%:M) ->
          (K<=INR N*L^2)%Rcoq ->
          (exists A b, paper_main_orientation_admissible r O eps L A b /\
            (paper_main_quadratic_risk N d x A b<=16*L*tau)%Rcoq) -> E x.
Proof.
move=> Hgamma.
have Hgamma0 : (0<gamma)%Rcoq by Stdlib.micromega.Lra.lra.
have Hlow : (0<gamma/2)%Rcoq by Stdlib.micromega.Lra.lra.
have [kappa [e [c [d0 [Hk [Hk2 [He [Hc Htail]]]]]]]] := paper_main_unsat_ordered_tail gamma Hgamma.
have [L [HL [HLscale _]]] := paper_main_loss_feature_constant (gamma/2)%Rcoq Hlow.
have HL0 : (0<=L)%Rcoq by Stdlib.micromega.Lra.lra.
have [delta [beta [eta [Hdelta [Hbeta [Heta [Hnet [Hetaeq Hent]]]]]]]] :=
  paper_main_unsat_net_parameters e L (gamma/2)%Rcoq He HL0 Hlow.
have [C [HC Hfinite]] := Htail beta eta Hbeta Heta.
have [eps [tau [Heps [Htau [Htau8 [Hbulk [Hcomp Hpin]]]]]]] :=
  paper_main_unsat_cutoff_parameters e L C He HL0 HC.
exists kappa,e,c,L,eps,tau,d0; do 10 (split=> //).
move=> N d r O HO Hd Hrd Hr Hnear Hsmall.
have HrdN : Nat.lt r d by exact/ssrnat.ltP.
have [mi Ed] : exists mi, d=(r+S mi)%N.
{ exists (Nat.sub d (S r)); rewrite -plusE; lia. }
subst d.
have Hdpos : (0<r+S mi)%N by rewrite addnS.
have HN := paper_main_hybrid_finite_density_pos gamma kappa (r+S mi) N Hgamma0 Hk2 Hdpos Hnear.
have Hdensity : (gamma/2*(INR(r+S mi))^2<=INR N)%Rcoq.
{ have HA := Rle_abs (-(INR N-gamma*(INR(r+S mi))^2)).
  rewrite Rabs_Ropp in HA.
  have Hsq := pow2_ge_0 (INR(r+S mi)).
  have HM := Rmult_le_compat_r _ _ _ Hsq Hk2; Stdlib.micromega.Lra.nra. }
pose z := (e*(1-exp(-c*(INR(r+S mi))^2))-(2*eta+2*C*eps)-e/4)%Rcoq.
have Hgap : (16*L*tau+4*(L+1)*delta+
  3*paper_main_gordon_entropy_constant(delta/(L+3))/((gamma/2)*beta)<=z)%Rcoq.
{ left; exact: (paper_main_unsat_error_budget e L delta beta eta C eps tau _ (gamma/2)%Rcoq _
    He Hnet Hent Hetaeq Hcomp Hpin Hsmall). }
apply: (paper_main_orientation_exception N r mi O eps L delta beta (gamma/2)%Rcoq
  (16*L*tau)%Rcoq z (exp(-(INR N*(e/4)^2)/2))%Rcoq HO HN HL0 Hdelta Hbeta Hlow _ Hdensity Hgap).
- left; exact: exp_pos.
- move=> s Hs bs Bs Hspos Hstates.
  have HI : List.seq 0 s <> nil.
  { move=> H; have HH := f_equal (@List.length nat) H.
    rewrite List.length_seq in HH; simpl in HH; lia. }
  have Hin j (Hj : In j (List.seq 0 s)) : (j<s)%coq_nat by apply in_seq in Hj; lia.
  have Hhead j (Hj : In j (List.seq 0 s)) : paper_main_symmetric(Hs j).
  { have [HH _] := Hstates j (Hin j Hj); exact: (proj1 HH). }
  have Hbulkpsd j (Hj : In j (List.seq 0 s)) : paper_main_psd(Bs j).
  { have [_ [HB _]] := Hstates j (Hin j Hj); exact HB. }
  have E4 : IZR 4 = (4%:R : R) by rewrite -INRE INR_IZR_INZ.
  have Hnormlo j (Hj : In j (List.seq 0 s)) :
    (1/4<=paper_main_frobenius(Hs j)^2+paper_main_frobenius(Bs j)^2)%Rcoq.
  { have [_ [_ [/andP[Hlo Hhi] _]]] := Hstates j (Hin j Hj).
    apply/RleP; rewrite RdivE E4 RplusE !RpowE; exact Hlo. }
  have Hop j (Hj : In j (List.seq 0 s)) : paper_main_cone_opnorm_le (Bs j) eps.
  { have [_ [_ [_ HB]]] := Hstates j (Hin j Hj); exact HB. }
  have Hnormhi j (Hj : In j (List.seq 0 s)) : (paper_main_frobenius(Bs j)^2<=2^2)%Rcoq.
  { have [_ [_ [/andP[Hlo Hhi] _]]] := Hstates j (Hin j Hj).
    have HhiR : (paper_main_frobenius(Hs j)^2+paper_main_frobenius(Bs j)^2<=4)%Rcoq.
    { apply/RleP; rewrite RplusE !RpowE E4; exact Hhi. }
    have HH0 := pow2_ge_0 (paper_main_frobenius(Hs j)).
    clear -HhiR HH0. Stdlib.micromega.Lra.nra. }
  have Hdim : (r+mi+1<=r+S mi)%N by rewrite addn1 addnS.
  have H := Hfinite (r+S mi) N r mi (List.seq 0 s) Hs bs Bs eps 2%Rcoq (e/4)%Rcoq
    Hd Hnear Hr Hdim HI ltac:(Stdlib.micromega.Lra.lra) ltac:(Stdlib.micromega.Lra.lra) ltac:(Stdlib.micromega.Lra.lra) Hhead Hbulkpsd Hnormlo Hop Hnormhi.
  have EZ : (e*(1-exp(-c*(INR(r+S mi))^2))-(2*eta+C*eps*2)-e/4=z)%Rcoq by rewrite /z; ring.
  by rewrite EZ in H.
Qed.
