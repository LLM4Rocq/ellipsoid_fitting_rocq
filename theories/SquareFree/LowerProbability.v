(* The lower spectral bound of the raw features, outside events of
   vanishing probability.

   paper_main_squarefree_lower_probability: let N : nat -> nat, c > 0 and
   c1 with eventual density N(d) / d^2 >= c and, eventually, 0 < N(d),
   4 N(d) <= d^2 and d^2 <= c1 N(d). There are measurable events E_d with
   probability tending to 0 such that for all large d every sample outside
   E_d has raw-feature coercivity with constant d^2 / 128.
   The scalar parameters are chosen before the data by the Chebyshev edge
   lemma paper_main_chebyshev_edge_parameters_exact at theta = 49/24 and
   A = 12: some k, and for beta = tau + 1 some eta > 0, with K = 2^(k+1)
   and tau = 12 (K + 1) = pmnbr_t k, satisfy the gap of
   paper_main_squarefree_lower_probability_at. The value of k is not
   computed. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct ereal measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral probability.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions Asymptotics Geometry.Psd Geometry.HeadCoefficients
  Feature.GramBlocks SquareFree.EdgeUpperLimit SquareFree.EdgeLower
  SquareFree.WalkNBRate SquareFree.ChebyshevParametersEdge
  Feature.UpperProbability SquareFree.LowerProbabilityAssembly.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* tau = 12 (K + 1) in the form of the Chebyshev edge parameters. *)
Lemma paper_main_squarefree_lower_tau (k : nat) : pmnbr_t k = 12 * ((2 ^ k.+1)%:R + 1).
Proof.
by rewrite /pmnbr_t natrM; congr (_ * _); exact: mulrSr.
Qed.

Theorem paper_main_squarefree_lower_probability (N : nat -> nat) (c : R) (c1 : nat) :
  0 < c -> paper_main_eventually_ge (paper_main_density N) c ->
  (exists D, forall d, (D <= d)%N ->
     (0 < N d)%N /\ (4 * N d <= d ^ 2)%N /\ (d ^ 2 <= c1 * N d)%N) ->
  exists E : forall d, set (paper_main_sample (N d) d),
    (forall d, measurable (E d)) /\
    paper_main_tends_to (fun d => paper_main_probability (N d) d (E d)) 0 /\
    exists D : nat, forall d, (D <= d)%N -> forall x : paper_main_sample (N d) d, ~ E d x ->
      paper_main_head_coercive (paper_main_feature_gram (N d) d x) ((1 / 128) * d%:R ^+ 2)%R.
Proof.
move=> Hc Hlow Hcount.
have Hcheb := paper_main_chebyshev_edge_parameters_exact (49 / 24)%R 12%R.
have [k Hk] := Hcheb ltac:(lra) ltac:(lra).
have Hb : 0 <= pmnbr_t k + 1 by rewrite /pmnbr_t addr_ge0.
have [eta [Heta Hgap]] := Hk (pmnbr_t k + 1) Hb.
apply: (paper_main_squarefree_lower_probability_at N c c1 k eta Hc Hlow Hcount Heta).
rewrite paper_main_squarefree_lower_tau in Hgap *.
exact Hgap.
Qed.
