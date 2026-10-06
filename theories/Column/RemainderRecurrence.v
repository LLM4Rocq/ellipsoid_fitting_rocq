(* Operator bounds for the remainder sums of the non-backtracking
   recursion of SquareFree.EdgeLower:
   Psi_L = sum_(k < L) (-1)^k E_k T_(L-k-1) (pmlo_Psi), with the errors E_k
   (pmlo_E) and the non-backtracking matrices T_j (pmlo_T). Operator
   bounds are pmlo_opb.
   - pmcr_psi_opbound: if |E_k| <= eta and |T_j| <= t for k, j < L, then
     |Psi_L| <= L eta t.
   - pmcr_psi_uniform: if these bounds hold for k, j < K, then
     |Psi_L| <= K eta t for every L <= K.
   - pmcr_recurrence_opbound: for 0 <= s <= 2 and m <= K,
     |Psi_m + s Psi_(m-1)| <= 3 K eta t. This sum is the remainder of the
     three-term recurrence pmlo_knh.
   Deterministic. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions SquareFree.EdgeLower.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Theorem pmcr_psi_opbound N (C : finType) (X : 'I_N -> C -> R) kap s L eta t :
  (forall k, (k < L)%N -> pmlo_opb N (pmlo_E N C X kap s k) eta) ->
  (forall j, (j < L)%N -> pmlo_opb N (pmlo_T N C X kap j) t) ->
  pmlo_opb N (pmlo_Psi N C X kap s L) (L%:R*(eta*t)).
Proof.
move=>HE HT.
have Hterm (k : 'I_L) : pmlo_opb N
  ((-1)^+k *: (pmlo_E N C X kap s k *m pmlo_T N C X kap (L-k.+1))) (eta*t).
{ have Hindex : (L-k.+1 < L)%N.
  { have Hk : Nat.lt k L by exact/ssrnat.ltP.
    apply/ssrnat.ltP; rewrite -minusE; lia. }
  have Hprod := pmlo_opb_mul N _ _ _ _ (HE k (ltn_ord k)) (HT _ Hindex).
  have H := pmlo_opb_scale N _ _ ((-1)^+k) Hprod.
  by rewrite normrX normrN normr1 expr1n mul1r in H. }
have H := pmlo_opb_sum N [the finType of 'I_L]
  (fun k => (-1)^+k *: (pmlo_E N C X kap s k *m pmlo_T N C X kap (L-k.+1)))
  (fun _ => (eta*t)%R) Hterm.
rewrite sumr_const card_ord -mulr_natl in H.
exact H.
Qed.

Theorem pmcr_psi_uniform N (C : finType) (X : 'I_N -> C -> R) kap s K eta t :
  0 <= eta -> 0 <= t ->
  (forall k, (k < K)%N -> pmlo_opb N (pmlo_E N C X kap s k) eta) ->
  (forall j, (j < K)%N -> pmlo_opb N (pmlo_T N C X kap j) t) ->
  forall L, (L <= K)%N -> pmlo_opb N (pmlo_Psi N C X kap s L) (K%:R*(eta*t)).
Proof.
move=>Heta Ht HE HT L HL.
have HE' k (Hk : (k<L)%N) := HE k (ltn_leq_trans Hk HL).
have HT' j (Hj : (j<L)%N) := HT j (ltn_leq_trans Hj HL).
have H := pmcr_psi_opbound N C X kap s L eta t HE' HT'.
apply: (pmlo_opb_le N _ _ _ H).
change (L%:R*(eta*t) <= K%:R*(eta*t)).
apply: ler_wpM2r; first exact: mulr_ge0.
by rewrite ler_nat.
Qed.

Theorem pmcr_recurrence_opbound N (C : finType) (X : 'I_N -> C -> R) kap s K eta t :
  0 <= s -> s <= 2 -> 0 <= eta -> 0 <= t ->
  (forall k, (k < K)%N -> pmlo_opb N (pmlo_E N C X kap s k) eta) ->
  (forall j, (j < K)%N -> pmlo_opb N (pmlo_T N C X kap j) t) ->
  forall m, (m <= K)%N ->
  pmlo_opb N (pmlo_Psi N C X kap s m + s *: pmlo_Psi N C X kap s m.-1)
    (3*K%:R*eta*t).
Proof.
move=>Hs Hs2 Heta Ht HE HT m Hm.
have Hm' : (m.-1 <= K)%N := leq_trans (leq_pred m) Hm.
have H1 := pmcr_psi_uniform N C X kap s K eta t Heta Ht HE HT m Hm.
have H2 := pmcr_psi_uniform N C X kap s K eta t Heta Ht HE HT m.-1 Hm'.
have HS := pmlo_opb_scale N _ _ s H2.
rewrite ger0_norm // in HS.
have HA := pmlo_opb_add N _ _ _ _ H1 HS.
apply: (pmlo_opb_le N _ _ _ HA).
change (K%:R*(eta*t)+s*(K%:R*(eta*t)) <= 3*K%:R*eta*t).
have Hq : 0 <= K%:R*(eta*t) by apply: mulr_ge0; [exact: ler0n | exact: mulr_ge0].
have Hscale := ler_wpM2r Hq Hs2.
have HEq : 3*K%:R*eta*t = K%:R*(eta*t)+2*(K%:R*(eta*t)) by ring.
rewrite HEq lerD2l; exact Hscale.
Qed.
