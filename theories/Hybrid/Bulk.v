(* The projected bulk lower bound at the density margin.

   For gamma > 1/4, the constants eta, delta, t, c, c2 and d0 of
   Hybrid.Density are fixed from gamma. For d >= d0,
   |N - gamma d^2| <= eta d^2, a head dimension r <= sqrt d + 1, a bulk
   index mi with r + mi + 1 <= d, a head range dimension
   q <= r^2 + 1, k = floor (delta N), and any head-feature map Fh
   with measurable entries on kk head coordinates, the joint bad event of
   Projected.BulkConditional (PSD sphere of size mi + 1, offset
   sqrt (D / 2) + t d) is measurable and has probability at most
   exp (- c2 d^2), under the split (kk + N * D) Gaussian law and under the
   product law. Off this event every J with |J| >= N - k keeps at least
   (1 - 1/1216) N rows, and the residual S_J G v + F_J c has norm > c d
   for every v in the PSD sphere and every head coefficient vector c. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix finset binomial.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Analysis.ContinuousTupleMeasurability Gaussian.FeatureCoordinates Head.Law
  Projected.BulkEscape Projected.BulkComplement Projected.BulkConditional
  Hybrid.Density.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_hybrid_bulk_event (gamma : R) :
  (1 / 4 < gamma)%Rcoq ->
  exists (eta delta t c c2 : R) (d0 : nat),
    (0 < eta)%Rcoq /\ (0 < delta)%Rcoq /\ (delta < 1 / 1216)%Rcoq /\ (0 < t)%Rcoq /\
    (0 < c)%Rcoq /\ (0 < c2)%Rcoq /\
    forall (kk d N r mi q k : nat)
      (Fh : kk.-tuple (measurableTypeR R) -> 'M[R]_(N, q)),
      (d0 <= d)%N -> (Rabs (INR N - gamma * INR d ^ 2) <= eta * INR d ^ 2)%Rcoq ->
      (INR r <= sqrt (INR d) + 1)%Rcoq -> (r + mi + 1 <= d)%N ->
      (INR q <= INR r * INR r + 1)%Rcoq ->
      (INR k <= delta * INR N)%Rcoq -> (delta * INR N < INR k + 1)%Rcoq ->
      (forall a i, measurable_fun [set: kk.-tuple (measurableTypeR R)]
         ((fun h => Fh h a i) : _ -> measurableTypeR R)) ->
      measurable [set p : kk.-tuple (measurableTypeR R) *
          (N * paper_main_symmetric_dimension mi).-tuple (measurableTypeR R) |
        paper_main_projected_bad N (paper_main_symmetric_dimension mi) q k (Fh p.1) p.2
          (paper_main_projected_psd_set mi)
          (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d)%Rcoq] /\
      (gaussian_product_law (Nat.add kk (N * paper_main_symmetric_dimension mi))
        (paper_main_split_coordinates kk (N * paper_main_symmetric_dimension mi) @^-1`
          [set p | paper_main_projected_bad N (paper_main_symmetric_dimension mi) q k
            (Fh p.1) p.2 (paper_main_projected_psd_set mi)
            (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d)%Rcoq]) <=
       ((exp (- c2 * INR d ^ 2))%Rcoq)%:E)%E /\
      ((gaussian_product_law kk \x
          gaussian_product_law (N * paper_main_symmetric_dimension mi))%E
        [set p | paper_main_projected_bad N (paper_main_symmetric_dimension mi) q k
          (Fh p.1) p.2 (paper_main_projected_psd_set mi)
          (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d)%Rcoq] <=
       ((exp (- c2 * INR d ^ 2))%Rcoq)%:E)%E /\
      forall p, ~ paper_main_projected_bad N (paper_main_symmetric_dimension mi) q k
          (Fh p.1) p.2 (paper_main_projected_psd_set mi)
          (sqrt (INR (paper_main_symmetric_dimension mi) / 2) + t * INR d)%Rcoq ->
        forall J : {set 'I_N}, (N - k <= #|J|)%N ->
          ((1 - 1 / 1216) * INR N <= INR #|J|)%Rcoq /\
          forall (v : nat -> R) (b : 'cV[R]_q), paper_main_projected_psd_set mi v ->
            (c * INR d < paper_main_projected_norm (paper_main_projected_residual N
              (paper_main_symmetric_dimension mi) q J
              (paper_main_projected_selector J *m Fh p.1) p.2 v b))%Rcoq.
Proof.
move=> Hg.
have [eta [delta [t [c [c2 [d0 [Heta [Hd [Hd' [Ht [Hc [Hc2 Hall]]]]]]]]]]]] :=
  paper_main_hybrid_density_margin_gamma gamma Hg.
exists eta, delta, t, c, c2, d0.
do 6 (split; first by []).
move=> kk d N r mi q k Fh Hdd HN Hr Hmi Hq Hk1 Hk2 HF.
have [Hk0 [HkN [Hent Hthr]]] := Hall d N r mi q k Hdd HN Hr Hmi Hq Hk1 Hk2.
have Hd0 : (0 < INR d)%Rcoq.
  apply: lt_0_INR; apply/ssrnat.ltP.
  by apply: leq_trans Hmi; rewrite addn1.
have Hu : (0 < t * INR d)%Rcoq by apply: Rmult_lt_0_compat.
have [mE [PE PP]] := paper_main_projected_psd_conditional_tail kk N mi q k Fh (t * INR d)
  Hk0 HkN Hu HF.
have Hexp : (((exp (INR k * (1 + ln (INR N / INR k)) - (t * INR d) ^ 2 / 2))%Rcoq)%:E <=
    ((exp (- c2 * INR d ^ 2))%Rcoq)%:E)%E.
  rewrite lee_fin; apply/RleP.
  case: Hent => H; last by rewrite H; lra.
  by apply: Rlt_le; apply: exp_increasing.
split => //; split; first exact: le_trans PE Hexp.
split; first exact: le_trans PP Hexp.
move=> p Hp J HJ.
have [HJ1 HJ2] := Hthr #|J| HJ.
split => //.
move=> v b Hv.
have [eps [He Heps]] := paper_main_projected_not_bad_margin N
  (paper_main_symmetric_dimension mi) q k (Fh p.1) p.2 (paper_main_projected_psd_set mi) _ Hp
  J HJ.
have := Heps v b Hv.
lra.
Qed.
