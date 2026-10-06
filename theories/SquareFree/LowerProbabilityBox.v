(* Coercivity of the raw feature Gram matrix from operator bounds on the
   non-backtracking remainders. Deterministic.

   paper_main_squarefree_coercivity_from_remainders: let
   kap = (sqrt (N 'C(d, 2)))^-1 and s = kap N, with 0 < N, d >= 9 and
   4 N <= d^2, so that 0 <= s <= 3/4 <= 1
   (paper_main_squarefree_coercivity_scale). Let a sample lie outside the
   non-backtracking union event pmnbv_union N d kap (2^(k+1)) (2^(j+2)) t
   with t >= 1, let every remainder E_m with m < 2^(k+1) have operator norm
   at most eta >= 0, let the gap condition
     2^(2^(k+1)) t + pmlo_rho (t + 1) (3 2^(k+1) eta t) (2^(k+1))
       <= (49/24)^(2^(k+1))
   hold, and let every row sum satisfy |D_i / 'C(d, 2) - 1| <= 1/64. Then
   paper_main_squarefree_box_from_remainders gives the box
   -(49/24) I <= pmlo_T 1 - s I, and paper_main_squarefree_coercivity_from_box
   shows that the Gram matrix of the raw features is at least (d^2 / 128) I. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions Geometry.HeadCoefficients Feature.GramBlocks
  SquareFree.EdgeLower SquareFree.WalkNB SquareFree.WalkNBEvent SquareFree.Box
  SquareFree.Coercivity SquareFree.LowerProbabilityBase.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Theorem paper_main_squarefree_coercivity_from_remainders N d (x : paper_main_sample N d)
    (k j : nat) (t eta : R) :
  (0 < N)%N -> (9 <= d)%N -> (4 * N <= d ^ 2)%N -> 1 <= t -> 0 <= eta ->
  ~ pmnbv_union N d ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) (2 ^ k.+1) (2 ^ j.+2) t x ->
  (forall m, (m < 2 ^ k.+1)%N ->
     pmlo_opb N (pmlo_E N ('I_d * 'I_d)%type (@pmnb_X R d (tval x) N)
       ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 * N%:R) m) eta) ->
  2 ^+ (2 ^ k.+1) * t + pmlo_rho (t + 1) (3 * (2 ^ k.+1)%:R * eta * t) (2 ^ k.+1) <=
    (49 / 24) ^+ (2 ^ k.+1) ->
  (forall i : 'I_N,
     `|(\sum_(q : 'I_d * 'I_d) (@pmnb_X R d (tval x) N i q) ^+ 2) / ('C(d, 2))%:R - 1| <= 1 / 64) ->
  paper_main_head_coercive (paper_main_feature_gram N d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> HN Hd9 HN4 Ht Heta Hx HE Hgap Hrow.
have [Hs0 Hs1] := paper_main_squarefree_coercivity_scale N d HN Hd9 HN4.
have Hs1' : (Num.sqrt ((N%:R : R) * ('C(d, 2))%:R))^-1 * N%:R <= 1 by apply: le_trans Hs1 _; lra.
have Htheta : (0 : R) <= (49 / 24)%R by rewrite divr_ge0 // ler0n.
have [Hlo _] := paper_main_squarefree_box_from_remainders N d
  ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1) ((Num.sqrt (N%:R * ('C(d, 2))%:R))^-1 * N%:R)
  k j t eta (49 / 24)%R x Hs0 Hs1' Ht Heta Htheta Hx HE Hgap.
exact (paper_main_squarefree_coercivity_from_box N d x HN Hd9 HN4 Hrow Hlo).
Qed.
