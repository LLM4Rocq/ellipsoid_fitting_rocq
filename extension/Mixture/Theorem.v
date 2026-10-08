(* Theorem 1.2 of Koehler and Sohn, "Universality and sharp thresholds for
   ellipsoid fitting" (arXiv 2608.27372, lines 164-190), for finite
   mixtures of product laws, at Stdlib's R: mixture_statement of
   MixtureStatement. Item X7 of phase 6, final assembly (lane A). Theorem
   is a keyword, so this module is required by its full name,
   Require Import EllipsoidUniversality.Mixture.Theorem, not by the From
   form.

   Main results.
   - mixture_points_nonzero_holds: the hypothesis mixture_points_nonzero K
     of Sat/Universality, by mixture_points_zero (Mixture/Points) with
     q = 1 - 1 / (4 K^4). Then q < 1 since K > 0, and q >= 0 since, for
     one point, the event of mixture_points_zero has a probability
     between 0 and q.
   - mixture_sat: the first conjunct of mixture_statement, Theorem 1.2 (i)
     for mixtures, by mixture_sat_of_interpolation (Sat/Universality) with
     mixture_small_residual (Mixture/Interpolation), Theorem 1.9 for
     mixture samples. The latter asks alpha < 1/2, which holds since
     alpha < alpha*(kappa) < 1/2 (universality_alpha_star_lt of
     Gaussian/Threshold). *)

From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ereal measure lebesgue_measure probability.
From EllipsoidFitting Require Import PaperMainDefinitions.
From EllipsoidUniversality Require Import UniversalityDefinitions.
From EllipsoidUniversality Require Import MixtureDefinitions MixtureStatement.
From EllipsoidUniversality.Gaussian Require Import Threshold.
From EllipsoidUniversality.Mixture Require Import Points Interpolation.
From EllipsoidUniversality.Sat Require Import Universality.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* For a mixture family of class K, all the points of a sample are zero
   with probability at most (1 - 1 / (4 K^4))^n. *)
Lemma mixture_points_nonzero_holds (K : R) :
  0 < K -> mixture_points_nonzero K.
Proof.
move=> K0 N w mu hfam.
pose q : R := 1 - (4%:R * K ^+ 4)^-1.
have hz n d : (0 < d)%N -> exists G : set (paper_main_sample n d),
    [/\ measurable G,
      (mixture_probability (N d) (w d) (mu d) n d G <= (q ^+ n)%:E)%E &
      forall x, ~ G x -> exists i : 'I_n, paper_main_point x i != 0].
  move=> d0; have [w0 [w1 hmu]] := hfam d.
  exact: mixture_points_zero K (N d) (w d) (mu d) n d d0 w0 w1 hmu.
exists q; split => //.
have k0 : 0 < (4%:R * K ^+ 4)^-1 :> R.
  by rewrite invr_gt0 mulr_gt0 ?exprn_gt0.
have q0 : 0 <= q.
  have [G [_ PG _]] := hz 1%N 1%N isT.
  have [w0 _] := hfam 1%N.
  rewrite -lee_fin -[q]expr1; apply: le_trans PG.
  apply: sume_ge0 => s _; apply: mule_ge0; last exact: measure_ge0.
  by rewrite lee_fin; apply: prodr_ge0 => i _; exact: w0.
by rewrite ger0_norm // /q gtrBl.
Qed.

(* Theorem 1.2 (i) for finite mixtures of product laws: below the
   threshold, a positive definite fit, and one of condition number at most
   c, with probability tending to one. *)
Theorem mixture_sat (kappa K alpha : R) :
  1 < kappa -> 0 < K -> 0 < alpha -> alpha < universality_alpha_star kappa ->
  exists c : R, 1 <= c /\
  (forall n d : nat, measurable (universality_pd_fit_event n d)) /\
  (forall n d : nat, measurable (universality_conditioned_fit_event n d c)) /\
  (forall (N : nat -> nat) (w : nat -> nat -> R)
          (mu : nat -> nat -> nat -> probability (measurableTypeR R) R),
    mixture_family K N w mu -> mixture_fourth_moment kappa N w mu ->
    forall n : nat -> nat, universality_density_tends_to n alpha ->
      paper_main_tends_to
        (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                    (universality_pd_fit_event (n d) d)) 1 /\
      paper_main_tends_to
        (fun d => mixture_probability (N d) (w d) (mu d) (n d) d
                    (universality_conditioned_fit_event (n d) d c)) 1).
Proof.
move=> k1 K0 a0 ha.
have /andP[_ h] := universality_alpha_star_lt _ k1.
exact: (mixture_sat_of_interpolation kappa K alpha k1 K0 a0 ha
  (mixture_small_residual K alpha K0 a0 (lt_trans ha h))
  (mixture_points_nonzero_holds K K0)).
Qed.
