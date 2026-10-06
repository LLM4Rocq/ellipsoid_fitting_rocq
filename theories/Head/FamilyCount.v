(* A finite list of index lists that contains every ordered head of
   bounded size, and its cardinality.
   - paper_main_head_families N K lists sequences of at most K indices
     below N, and paper_main_head_families_complete shows that every such
     sequence is in it.
   - paper_main_head_families_cardinality: it has at most (N + 1)^K
     elements, so the log of its length is at most K ln(N + 1)
     (paper_main_head_families_log).
   - paper_main_head_families_entropy, paper_main_head_families_exp: if
     N <= C d^2 and K <= B d ln d with d >= 1 and ln d >= 1, the log of its
     length is at most B (ln(C + 1) + 2) d (ln d)^2. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import ssreflect.
From EllipsoidFitting Require Import Head.DataRates.
Import ListNotations.
Open Scope R_scope.

Fixpoint paper_main_head_families (N K : nat) : list (list nat) :=
  match K with
  | O => [[]]
  | S k => [] :: List.flat_map
      (fun i => List.map (fun J => i :: J) (paper_main_head_families N k)) (List.seq 0 N)
  end.

Lemma paper_main_head_families_empty N K : In [] (paper_main_head_families N K).
Proof. destruct K; simpl; auto. Qed.

Theorem paper_main_head_families_complete N K J :
  (List.length J <= K)%nat ->
  (forall i, In i J -> (i < N)%nat) -> In J (paper_main_head_families N K).
Proof.
revert J; induction K as [|K IH]; intros J Hlen HJ.
- destruct J; simpl in *; [auto|lia].
- destruct J as [|i J]; [apply paper_main_head_families_empty|].
  simpl; right; apply List.in_flat_map.
  exists i; split.
  + apply List.in_seq; split; [lia|apply HJ; simpl; auto].
  + apply List.in_map; apply IH; [simpl in Hlen; lia|].
    intros j Hj; apply HJ; simpl; auto.
Qed.

Lemma paper_main_head_families_positive N K :
  (0 < List.length (paper_main_head_families N K))%nat.
Proof. destruct K; simpl; lia. Qed.

Lemma paper_main_head_flat_length (I : list nat) (H : list (list nat)) :
  List.length (List.flat_map (fun i => List.map (fun J => i::J) H) I) =
    (List.length I*List.length H)%nat.
Proof.
induction I as [|i I IH]; simpl; [reflexivity|].
rewrite List.length_app List.length_map IH; lia.
Qed.

Theorem paper_main_head_families_cardinality N K :
  (List.length (paper_main_head_families N K) <= (S N)^K)%nat.
Proof.
induction K as [|K IH]; [simpl; lia|].
change (S (List.length (List.flat_map
  (fun i => List.map (fun J => i::J) (paper_main_head_families N K)) (List.seq 0 N))) <= (S N)^(S K))%nat.
rewrite paper_main_head_flat_length List.length_seq.
pose proof (paper_main_head_families_positive N K) as HP.
rewrite Nat.pow_succ_r'; nia.
Qed.

Lemma paper_main_head_families_log N K :
  ln(INR (List.length (paper_main_head_families N K))) <= INR K*ln(INR N+1).
Proof.
pose proof (paper_main_head_families_cardinality N K) as HC.
pose proof (paper_main_head_families_positive N K) as HP.
assert (HL : 0 < INR (List.length (paper_main_head_families N K))) by (apply lt_0_INR; exact HP).
assert (HN : 0 < INR (S N)) by (apply lt_0_INR; lia).
pose proof (le_INR _ _ HC) as HR.
rewrite pow_INR in HR.
assert (HB : ln(INR (List.length (paper_main_head_families N K))) <= ln((INR (S N))^K)).
{ destruct (Rle_lt_or_eq_dec _ _ HR) as [Hlt|Heq].
  - left; apply ln_increasing; assumption.
  - rewrite Heq; right; reflexivity. }
rewrite (ln_pow (INR (S N)) HN K) S_INR in HB; exact HB.
Qed.

Theorem paper_main_head_families_entropy N K C B d :
  0 <= C -> 0 <= B -> 1 <= d -> 1 <= ln d ->
  INR N <= C*d^2 -> INR K <= B*d*ln d ->
  ln(INR (List.length (paper_main_head_families N K))) <=
    (B*(ln(C+1)+2))*d*(ln d)^2.
Proof.
intros HC HB Hd Hlog HN HK.
pose proof (paper_main_head_families_log N K) as HF.
pose proof (paper_main_log_quadratic_count_coarse C (INR N) d HC (pos_INR N) Hd Hlog HN) as HL.
pose proof (paper_main_log_successor_bound (INR N) (pos_INR N)) as [HL0 _].
pose proof (paper_main_log_successor_bound C HC) as [HC0 _].
assert (HDK : 0 <= B*d*ln d) by (repeat apply Rmult_le_pos; lra).
pose proof (Rmult_le_compat (INR K) (B*d*ln d) (ln(INR N+1))
  ((ln(C+1)+2)*ln d) (pos_INR K) HL0 HK HL) as HM.
nra.
Qed.

Corollary paper_main_head_families_exp N K C B d :
  0 <= C -> 0 <= B -> 1 <= d -> 1 <= ln d ->
  INR N <= C*d^2 -> INR K <= B*d*ln d ->
  INR (List.length (paper_main_head_families N K)) <=
    exp((B*(ln(C+1)+2))*d*(ln d)^2).
Proof.
intros HC HB Hd Hlog HN HK.
pose proof (paper_main_head_families_entropy N K C B d HC HB Hd Hlog HN HK) as HL.
assert (HP : 0 < INR (List.length (paper_main_head_families N K))).
{ apply lt_0_INR; apply paper_main_head_families_positive. }
rewrite <- (exp_ln _ HP).
destruct (Rle_lt_or_eq_dec _ _ HL) as [Hlt|Heq].
- left; apply exp_increasing; exact Hlt.
- rewrite Heq; right; reflexivity.
Qed.
