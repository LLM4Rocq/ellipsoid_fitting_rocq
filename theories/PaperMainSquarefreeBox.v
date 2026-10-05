(* A Loewner box for the first non-backtracking matrix, from operator bounds
   on the column remainders, outside the trace events. Deterministic.

   Let T m = pmlo_T N ('I_d * 'I_d) (pmnb_X d xs) kap m be the
   non-backtracking matrices of the square-free columns of the sample, and
   E m the column remainders pmlo_E.
   - pmsb_out_opb: outside the trace union event
     pmnbv_union N d kap K (2^(j+2)) t, with t >= 1, every T m with m <= K
     has operator norm at most t.
   - pmsb_shift_opb: if T has operator norm at most t and 0 <= s <= 1, then
     T - s I has operator norm at most t + 1.
   - paper_main_squarefree_box_from_remainders: let 0 <= s <= 1, t >= 1 and
     eta, theta >= 0. Outside pmnbv_union N d kap (2^(k+1)) (2^(j+2)) t, if
     every E m with m < 2^(k+1) has operator norm at most eta and
       2^(2^(k+1)) t + pmlo_rho (t + 1) (3 2^(k+1) eta t) (2^(k+1))
         <= theta^(2^(k+1)),
     then -theta I <= T 1 - s I <= theta I. The remainders of the recurrence
     are bounded by pmcr_recurrence_opbound, and the box comes from
     pmnbv_box. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainSquarefreeEdgeLower
 PaperMainSquarefreeWalkNB PaperMainSquarefreeWalkNBEvent
 PaperMainColumnRemainderRecurrence PaperMainMatrixFamilyCauchyPowers.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Lemma pmsb_out_opb N d kap K j t (x : paper_main_sample N d) :
  1 <= t -> ~ pmnbv_union N d kap K (2 ^ j.+2) t x ->
  forall m, (m <= K)%N ->
  pmlo_opb N (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap m) t.
Proof.
move=>Ht Hx [|m] Hm.
- rewrite pmlo_T0; exact: pmlo_opb_le (pmfc_opb_identity N) Ht.
- apply: (pmnbv_out_opb N d kap K j t x (le_trans ler01 Ht) Hx).
  by rewrite ltn0Sn Hm.
Qed.

Lemma pmsb_shift_opb N (T : 'M[R]_N) s t :
  0 <= s -> s <= 1 -> pmlo_opb N T t -> pmlo_opb N (T - s *: 1%:M) (t+1).
Proof.
move=>Hs Hs1 HT.
have HI := pmlo_opb_scale N _ _ (-s) (pmfc_opb_identity N).
rewrite normrN ger0_norm // mulr1 in HI.
have HH := pmlo_opb_add N _ _ _ _ HT HI.
rewrite scaleNr in HH.
apply: (pmlo_opb_le N _ _ _ HH).
change (t+s <= t+1); by rewrite lerD2l.
Qed.

Theorem paper_main_squarefree_box_from_remainders N d kap s k j t eta theta
    (x : paper_main_sample N d) :
  0 <= s -> s <= 1 -> 1 <= t -> 0 <= eta -> 0 <= theta ->
  ~ pmnbv_union N d kap (2 ^ k.+1) (2 ^ j.+2) t x ->
  (forall m, (m < 2 ^ k.+1)%N ->
    pmlo_opb N (pmlo_E N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap s m) eta) ->
  2 ^+ (2 ^ k.+1) * t + pmlo_rho (t+1) (3 * (2 ^ k.+1)%:R * eta * t) (2 ^ k.+1)
    <= theta ^+ (2 ^ k.+1) ->
  paper_main_loewner_le ((-theta) *: 1%:M)
    (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap 1 - s *: 1%:M) /\
  paper_main_loewner_le
    (pmlo_T N ('I_d * 'I_d)%type (pmnb_X d (tval x)) kap 1 - s *: 1%:M)
    (theta *: 1%:M).
Proof.
move=>Hs Hs1 Ht Heta Htheta Hx HE Hgap.
have Ht0 := le_trans ler01 Ht.
have HK : (0 < 2 ^ k.+1)%N by rewrite expn_gt0.
have HT := pmsb_out_opb N d kap (2 ^ k.+1) j t x Ht Hx.
have HB := pmsb_shift_opb N _ s t Hs Hs1 (HT 1 HK).
have Hr : 0 <= 3 * (2 ^ k.+1)%:R * eta * t by rewrite !mulr_ge0 // ?ler0n.
have Hs2 : s <= 2 by apply: le_trans Hs1 _; rewrite ler1n.
apply: (pmnbv_box N d kap s k j.+1 t (t+1)
  (3 * (2 ^ k.+1)%:R * eta * t) theta x) => //.
- by apply/andP; split.
- move=>m /andP [_ Hm].
  apply: (pmcr_recurrence_opbound N _ _ kap s (2 ^ k.+1) eta t) => //.
  + move=>q Hq; exact: HT q (ltnW Hq).
  + exact: ltnW Hm.
Qed.
