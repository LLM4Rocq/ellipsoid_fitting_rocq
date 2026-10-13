From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: solution sets and the lifetime of a clause sequence        *)
(*                                                                            *)
(* Part of target T7 of phase 12, the capped variance bound for random k-SAT  *)
(* of SatVarianceStatement.v. A Rocq formalization of the credited argument   *)
(* of the proposition 'Polynomial concentration' of 'A limiting               *)
(* satisfiability threshold for every fixed clause size' (family 235 of the   *)
(* OpenAI math collection, revision 1581d4cbd,                                *)
(* source/sections/concentration.tex and forcing.tex). The files of RandomSAT *)
(* follow the route of the Lean development of the collection                 *)
(* (lean/OAI/Probability/RandomSAT, paths below relative to it): the variance *)
(* by a recursion over the clauses, and the forced variables by the erasure   *)
(* of one variable. This file follows:                                        *)
(* Lean: addClause (ClauseProcess.lean, line 76)                              *)
(* Lean: restrictSolutions (ClauseProcess.lean, line 91)                      *)
(* Lean: alive (ClauseProcess.lean, line 129)                                 *)
(* Lean: lifetime (Variance.lean, line 37)                                    *)
(* Lean: clauseHeadEquiv (ClauseProcess.lean, line 50)                        *)
(* Lean: clauseHead_mean (ClauseProcess.lean, line 394)                       *)
(*                                                                            *)
(* The clauses, the cap and the statistic V_n are those of                    *)
(* SatVarianceDefinitions.v. The assignments on n variables are {ffun 'I_n -> *)
(* bool}, and S is a set of assignments.                                      *)
(*                                                                            *)
(* - add_clause S c is the set of the elements of S that satisfy the clause   *)
(*   c, restrict S s the set of those that satisfy every clause of the        *)
(*   sequence s, and alive S is 1 if S is not empty and 0 otherwise.          *)
(* - life S s, the lifetime, is the number of nonempty sets among the         *)
(*   solution sets of the nonempty prefixes of s (life_sum).                  *)
(* - sat_prefix_lenE: for every tuple t of M clauses, sat_prefix_len t is     *)
(*   life [set: _] t. The statistic of the statement, the largest satisfiable *)
(*   prefix length up to the cap, is the lifetime of the set of all           *)
(*   assignments. The Lean development states its variance bound for the      *)
(*   lifetime; this identity transfers it to the statistic of the statement.  *)
(* - The first variable of a clause: a clause of size k.+1 on n.+1 variables  *)
(*   either does not contain the first variable, and is cabsent c for a       *)
(*   clause c of size k.+1 on the other n variables, or contains it with a    *)
(*   sign b, and is cpresent c b for a clause c of size k. The map cjoin of   *)
(*   the two cases is a bijection (cjoin_bij). Hence #|clause n k| = 'C(n, k) *)
(*   2^k (card_clause), and the uniform mean over clause n.+1 k.+1 is the     *)
(*   mixture of the two cases with weights 1 - k.+1/n.+1 and k.+1/n.+1        *)
(*   (unif_mean_clause_split).                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section solutions.
Context {R : realType}.

(* The assignments of a formula on n variables that satisfy a clause. *)
Definition add_clause n k (S : {set {ffun 'I_n -> bool}}) (c : clause n k) :
    {set {ffun 'I_n -> bool}} :=
  [set s in S | clause_sat s c].

Definition alive n (S : {set {ffun 'I_n -> bool}}) : R := (S != set0)%:R.

(* The solutions in S of a sequence of clauses. *)
Fixpoint restrict n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
    {set {ffun 'I_n -> bool}} :=
  if s is c :: s' then restrict (add_clause S c) s' else S.

(* The number of nonempty solution sets along the sequence: the lifetime. *)
Fixpoint life n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) : R :=
  if s is c :: s' then alive (add_clause S c) + life (add_clause S c) s' else 0.

Lemma add_clause_sub n k (S : {set {ffun 'I_n -> bool}}) (c : clause n k) :
  add_clause S c \subset S.
Proof. by apply/subsetP => s; rewrite inE => /andP[]. Qed.

Lemma add_clause_mono n k (S T : {set {ffun 'I_n -> bool}}) (c : clause n k) :
  S \subset T -> add_clause S c \subset add_clause T c.
Proof.
move=> /subsetP ST; apply/subsetP => s; rewrite !inE => /andP[/ST -> ->].
by [].
Qed.

Lemma add_clauseC n k r (S : {set {ffun 'I_n -> bool}}) (c : clause n k)
    (d : clause n r) :
  add_clause (add_clause S c) d = add_clause (add_clause S d) c.
Proof. by apply/setP => s; rewrite !inE -!andbA [clause_sat _ c && _]andbC. Qed.

Lemma add_clause0 n k (c : clause n k) : add_clause set0 c = set0.
Proof. by apply/setP => s; rewrite !inE. Qed.

Lemma restrictE n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  restrict S s = [set x in S | all (clause_sat x) s].
Proof.
elim: s S => [|c s IH] S /=; first by apply/setP => x; rewrite inE andbT.
by rewrite IH; apply/setP => x; rewrite !inE andbA.
Qed.

Lemma restrict_sub n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  restrict S s \subset S.
Proof. by rewrite restrictE; apply/subsetP => x; rewrite inE => /andP[]. Qed.

Lemma restrict_mono n k (S T : {set {ffun 'I_n -> bool}})
    (s : seq (clause n k)) :
  S \subset T -> restrict S s \subset restrict T s.
Proof.
move=> /subsetP ST; rewrite !restrictE; apply/subsetP => x.
by rewrite !inE => /andP[/ST -> ->].
Qed.

Lemma alive_ge0 n (S : {set {ffun 'I_n -> bool}}) : 0 <= alive S.
Proof. exact: ler0n. Qed.

Lemma alive_le1 n (S : {set {ffun 'I_n -> bool}}) : alive S <= 1.
Proof. by rewrite /alive; case: (S != set0). Qed.

Lemma alive_mono n (S T : {set {ffun 'I_n -> bool}}) :
  S \subset T -> alive S <= alive T.
Proof.
move=> ST; rewrite /alive; case: (eqVneq S set0) => [_|S0] /=.
  exact: ler0n.
have -> : T != set0.
  by apply: contra_neq S0 => T0; apply/eqP; rewrite -subset0 -T0.
by [].
Qed.

Lemma alive0 n : alive (set0 : {set {ffun 'I_n -> bool}}) = 0.
Proof. by rewrite /alive eqxx. Qed.

Lemma alive_sqr n (S : {set {ffun 'I_n -> bool}}) : alive S ^+ 2 = alive S.
Proof. by rewrite /alive; case: (S != set0); rewrite ?expr0n ?expr1n. Qed.

Lemma life0 n k (s : seq (clause n k)) : life set0 s = 0.
Proof. by elim: s => //= c s IH; rewrite add_clause0 IH alive0 addr0. Qed.

Lemma life_ge0 n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  0 <= life S s.
Proof. by elim: s S => //= c s IH S; rewrite addr_ge0 ?alive_ge0. Qed.

Lemma life_le n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  life S s <= (size s)%:R.
Proof.
elim: s S => [|c s IH] S /=; first by rewrite lexx.
by rewrite -addn1 natrD addrC lerD ?alive_le1.
Qed.

Lemma life_mono n k (S T : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  S \subset T -> life S s <= life T s.
Proof.
elim: s S T => [|c s IH] S T ST //=.
by rewrite lerD ?alive_mono ?IH ?add_clause_mono.
Qed.

(* The lifetime counts the nonempty solution sets of the prefixes. *)
Lemma life_sum n k (S : {set {ffun 'I_n -> bool}}) (s : seq (clause n k)) :
  life S s = \sum_(j < size s) alive (restrict S (take j.+1 s)).
Proof.
elim: s S => [|c s IH] S /=; first by rewrite big_ord0.
by rewrite big_ord_recl IH; congr (_ + _); rewrite take0.
Qed.

End solutions.

Arguments add_clause {n k} S c.
Arguments alive {R n} S.
Arguments restrict {n k} S s.
Arguments life {R n k} S s.

Section prefix.
Context {R : realType}.

Lemma all_take_tnth (T : Type) M (t : M.-tuple T) (p : pred T) m :
  all p (take m t) = [forall i : 'I_M, (i < m)%N ==> p (tnth t i)].
Proof.
case: M t => [|M] t.
  by rewrite tuple0 /=; apply/esym/forallP => -[].
apply/(all_nthP (tnth t ord0))/forallP => [h i|h j].
  apply/implyP => im; have := h i; rewrite nth_take // -tnth_nth; apply.
  by rewrite size_take size_tuple; case: ifP => // _; rewrite (ltn_ord i).
rewrite size_take size_tuple => jlt.
have jM : (j < M.+1)%N.
  by move: jlt; case: ifP => // mM jm'; exact: ltn_trans jm' mM.
have jm : (j < m)%N.
  move: jlt; case: ifP => // /negbT; rewrite -leqNgt => Mm jM'.
  exact: leq_trans jM' Mm.
have := h (Ordinal jM); rewrite /= jm /= (tnth_nth (tnth t ord0)) /=.
by rewrite nth_take.
Qed.

Lemma prefix_satE n k M (t : M.-tuple (clause n k)) m :
  prefix_sat t m = (restrict [set: {ffun 'I_n -> bool}] (take m t) != set0).
Proof.
rewrite /prefix_sat restrictE; apply/existsP/set0Pn => [[s hs]|[s]].
  by exists s; rewrite !inE /= all_take_tnth.
by rewrite !inE /= all_take_tnth => hs; exists s.
Qed.

Lemma prefix_sat0 n k M (t : M.-tuple (clause n k)) : prefix_sat t 0.
Proof. by rewrite prefix_satE take0 /=; apply/set0Pn; exists [ffun=> true]. Qed.

Lemma prefix_sat_le n k M (t : M.-tuple (clause n k)) m m' :
  (m' <= m)%N -> prefix_sat t m -> prefix_sat t m'.
Proof.
move=> mm; rewrite !prefix_satE; apply: contra_neq => h; apply/eqP.
rewrite -subset0 -h -(cat_take_drop m' (take m t)) take_takel //.
by rewrite !restrictE; apply/subsetP => x; rewrite !inE /= all_cat => /andP[->].
Qed.

Lemma sum_ltn_ord M V : (V <= M)%N -> (\sum_(j < M) (j < V)%N)%N = V.
Proof.
elim: M V => [|M IH] V VM; first by rewrite big_ord0; move: VM;
  rewrite leqn0 => /eqP.
rewrite big_ord_recr /=; case: (leqP V M) => [VM'|MV].
  by rewrite IH // addn0.
have -> : V = M.+1 by apply/eqP; rewrite eqn_leq VM MV.
have e : (\sum_(i < M) ((i : nat) < M.+1)%N)%N = M.
  rewrite -[RHS](IH M (leqnn M)); apply: eq_bigr => i _.
  by rewrite ltn_ord ltnS ltnW.
by rewrite e addn1.
Qed.

(* The length of the longest satisfiable prefix is the lifetime of the full
   solution set. *)
Lemma sat_prefix_lenE n k M (t : M.-tuple (clause n k)) :
  (sat_prefix_len t)%:R = life [set: {ffun 'I_n -> bool}] t :> R.
Proof.
set V := sat_prefix_len t.
have VM : (V <= M)%N.
  by apply/bigmax_leqP => m _; rewrite -ltnS (ltn_ord m).
have PV m : (m <= M)%N -> prefix_sat t m = (m <= V)%N.
  move=> mM; apply/idP/idP => [Pm|mV].
    have mM1 : (m < M.+1)%N by rewrite ltnS.
    exact: (leq_bigmax_cond (Ordinal mM1)).
  case: m mM mV => [|m] mM mV; first exact: prefix_sat0.
  case Pm: (prefix_sat t m.+1) => //.
  have : (V <= m)%N.
    apply/bigmax_leqP => i Pi; rewrite leqNgt; apply/negP => mi.
    by move: Pm; rewrite (prefix_sat_le mi Pi).
  by rewrite leqNgt mV.
rewrite life_sum size_tuple.
transitivity (\sum_(j < M) ((j < V)%N)%:R : R).
  by rewrite -natr_sum sum_ltn_ord.
apply: eq_bigr => j _.
by rewrite /alive -prefix_satE PV.
Qed.

End prefix.

(* The first variable of a clause: a clause on n.+1 variables is a clause on
   the last n variables, with the first variable absent or present with a
   sign. *)
Section clause_split.

Definition prepend n (b : option bool) (c : {ffun 'I_n -> option bool}) :
    {ffun 'I_n.+1 -> option bool} :=
  [ffun i => if unlift ord0 i is Some j then c j else b].

Definition ftail n (c : {ffun 'I_n.+1 -> option bool}) :
    {ffun 'I_n -> option bool} :=
  [ffun j => c (lift ord0 j)].

Lemma prepend0 n b (c : {ffun 'I_n -> option bool}) : prepend b c ord0 = b.
Proof. by rewrite ffunE unlift_none. Qed.

Lemma prepend_lift n b (c : {ffun 'I_n -> option bool}) j :
  prepend b c (lift ord0 j) = c j.
Proof. by rewrite ffunE liftK. Qed.

Lemma ftail_prepend n b (c : {ffun 'I_n -> option bool}) :
  ftail (prepend b c) = c.
Proof. by apply/ffunP => j; rewrite ffunE prepend_lift. Qed.

Lemma prepend_ftail n (c : {ffun 'I_n.+1 -> option bool}) :
  prepend (c ord0) (ftail c) = c.
Proof.
apply/ffunP => i; rewrite ffunE; case: (unliftP ord0 i) => [j ->|->] //.
by rewrite ffunE.
Qed.

Lemma card_support n (c : {ffun 'I_n -> option bool}) :
  #|[set i | c i != None]| = (\sum_i (c i != None))%N.
Proof. by rewrite -sum1dep_card big_mkcond. Qed.

Lemma card_support_prepend n b (c : {ffun 'I_n -> option bool}) :
  #|[set i | prepend b c i != None]| =
    ((b != None) + #|[set i | c i != None]|)%N.
Proof.
rewrite !card_support big_ord_recl prepend0; congr addn.
by apply: eq_bigr => j _; rewrite prepend_lift.
Qed.

Lemma proper_prepend n k b (c : {ffun 'I_n -> option bool}) :
  proper_clause k c -> proper_clause ((b != None) + k) (prepend b c).
Proof. by rewrite /proper_clause card_support_prepend => /eqP ->. Qed.

Lemma proper_ftail n k (c : {ffun 'I_n.+1 -> option bool}) :
  proper_clause ((c ord0 != None) + k) c -> proper_clause k (ftail c).
Proof.
rewrite /proper_clause -{1}(prepend_ftail c) card_support_prepend.
by rewrite eqn_add2l.
Qed.

Definition cabsent n k (c : clause n k) : clause n.+1 k :=
  exist _ (prepend None (val c)) (proper_prepend None (valP c)).

Definition cpresent n k (c : clause n k) (b : bool) : clause n.+1 k.+1 :=
  exist _ (prepend (Some b) (val c)) (proper_prepend (Some b) (valP c)).

Lemma proper_ftail_None n k (c : clause n.+1 k) :
  val c ord0 = None -> proper_clause k (ftail (val c)).
Proof.
by move=> e; apply: proper_ftail; rewrite e /= add0n; exact: valP.
Qed.

Lemma proper_ftail_Some n k (c : clause n.+1 k.+1) b :
  val c ord0 = Some b -> proper_clause k (ftail (val c)).
Proof.
by move=> e; apply: proper_ftail; rewrite e /= add1n; exact: valP.
Qed.

Definition csplit n k (c : clause n.+1 k.+1) :
    clause n k.+1 + clause n k * bool :=
  match val c ord0 as o return val c ord0 = o -> _ with
  | None => fun e => inl (exist _ (ftail (val c)) (proper_ftail_None e))
  | Some b => fun e => inr (exist _ (ftail (val c)) (proper_ftail_Some e), b)
  end erefl.

Definition cjoin n k (x : clause n k.+1 + clause n k * bool) :
    clause n.+1 k.+1 :=
  match x with
  | inl c => cabsent c
  | inr (c, b) => cpresent c b
  end.

Lemma cjoinK n k : cancel (@cjoin n k) (@csplit n k).
Proof.
move=> [c|[c b]]; rewrite /csplit /=.
- move: (@proper_ftail_None n k.+1 (cabsent c))
    (@proper_ftail_Some n k (cabsent c)).
  rewrite /= prepend0 => p _; congr inl; apply: val_inj => /=.
  exact: ftail_prepend.
- move: (@proper_ftail_None n k.+1 (cpresent c b))
    (@proper_ftail_Some n k (cpresent c b)).
  rewrite /= prepend0 => _ p; congr (inr (_, _)); apply: val_inj => /=.
  exact: ftail_prepend.
Qed.

Lemma cjoin_surj n k (c : clause n.+1 k.+1) : exists x, cjoin x = c.
Proof.
case e: (val c ord0) => [b|].
  exists (inr (exist _ (ftail (val c)) (proper_ftail_Some e), b)).
  by apply: val_inj => /=; rewrite -e prepend_ftail.
exists (inl (exist _ (ftail (val c)) (proper_ftail_None e))).
by apply: val_inj => /=; rewrite -e prepend_ftail.
Qed.

Lemma csplitK n k : cancel (@csplit n k) (@cjoin n k).
Proof. by move=> c; have [x <-] := cjoin_surj c; rewrite cjoinK. Qed.

Lemma cjoin_bij n k : bijective (@cjoin n k).
Proof. by exists (@csplit n k); [exact: cjoinK|exact: csplitK]. Qed.

(* The number of proper signed k-clauses on n variables. *)
Lemma card_clause0 n : #|{: clause n 0}| = 1%N.
Proof.
have p : proper_clause 0 [ffun _ : 'I_n => None].
  by rewrite /proper_clause card_support big1 // => i _; rewrite ffunE.
pose c0 : clause n 0 := exist (fun c => proper_clause 0 c) [ffun=> None] p.
apply: (@eq_card1 _ c0) => c; rewrite !inE; apply/esym/eqP.
apply: val_inj => /=; apply/ffunP => i; rewrite ffunE.
have := valP c; rewrite /proper_clause card_support => /eqP s0.
apply/eqP; rewrite -[_ == _]negbK; apply/negP => ci.
have : (0 < \sum_j (val c j != None))%N.
  by rewrite (bigD1 i) //= ci.
by rewrite s0.
Qed.

Lemma card_clause0S k : #|{: clause 0 k.+1}| = 0%N.
Proof.
apply: eq_card0 => c; rewrite !inE; have := valP c.
by rewrite /proper_clause card_support big_ord0.
Qed.

Lemma card_clauseSS n k :
  #|{: clause n.+1 k.+1}| = (#|{: clause n k.+1}| + #|{: clause n k}| * 2)%N.
Proof.
by rewrite -(bij_eq_card (@cjoin_bij n k)) card_sum card_prod card_bool.
Qed.

Lemma card_clause n k : #|{: clause n k}| = ('C(n, k) * 2 ^ k)%N.
Proof.
elim: n k => [|n IH] [|k].
- by rewrite card_clause0.
- by rewrite card_clause0S bin0n.
- by rewrite card_clause0 bin0.
by rewrite card_clauseSS !IH binS mulnDl expnS -mulnA [(2 ^ k * 2)%N]mulnC.
Qed.

Lemma card_clause_gt0 n k : (k <= n)%N -> (0 < #|{: clause n k}|)%N.
Proof. by move=> kn; rewrite card_clause muln_gt0 bin_gt0 kn expn_gt0. Qed.

End clause_split.

(* The uniform clause on n.+1 variables: its first variable is absent with
   probability 1 - k.+1 / n.+1, and the rest is a uniform clause of size k.+1;
   or present with probability k.+1 / n.+1, with a uniform sign, and the rest
   is a uniform clause of size k. *)
Lemma unif_mean_clause_split (R : realType) n k (f : clause n.+1 k.+1 -> R) :
  (k <= n)%N ->
  unif_mean f =
  (1 - k.+1%:R / n.+1%:R) * unif_mean (fun c : clause n k.+1 => f (cabsent c)) +
  k.+1%:R / n.+1%:R *
    unif_mean (fun c : clause n k =>
      unif_mean (fun b : bool => f (cpresent c b))).
Proof.
move=> kn.
rewrite -(unif_mean_bij f (@cjoin_bij n k)) unif_mean_sum_type /=.
rewrite (unif_mean_pair (fun p : clause n k * bool => f (cjoin (inr p)))) /=.
have hB : (#|{: clause n k * bool}| = 'C(n, k) * 2 ^ k.+1)%N.
  by rewrite card_prod card_bool card_clause expnS mulnCA [(2 * _)%N]mulnC.
have hAB : (#|{: clause n k.+1}| + #|{: clause n k * bool}| =
    'C(n.+1, k.+1) * 2 ^ k.+1)%N.
  by rewrite hB card_clause binS mulnDl.
have hd : (n.+1 * 'C(n, k) = k.+1 * 'C(n.+1, k.+1))%N.
  exact: (mul_bin_diag n.+1 k).
have c0 : (0 < 'C(n.+1, k.+1))%N by rewrite bin_gt0.
have b0 : (2 ^ k.+1)%:R != 0 :> R by rewrite pnatr_eq0 -lt0n expn_gt0.
have cc0 : 'C(n.+1, k.+1)%:R != 0 :> R by rewrite pnatr_eq0 -lt0n.
have N0 : (#|{: clause n k.+1}| + #|{: clause n k * bool}|)%:R != 0 :> R.
  by rewrite hAB natrM mulf_neq0.
have hdR : n.+1%:R * 'C(n, k)%:R = k.+1%:R * 'C(n.+1, k.+1)%:R :> R.
  by rewrite -!natrM hd.
have wB : #|{: clause n k * bool}|%:R / (#|{: clause n k.+1}| +
    #|{: clause n k * bool}|)%:R = k.+1%:R / n.+1%:R :> R.
  rewrite hAB hB !natrM invfM mulrACA divff // mulr1.
  apply/eqP; rewrite eqr_div // ?pnatr_eq0 //; apply/eqP.
  by rewrite mulrC hdR mulrC.
have wA : #|{: clause n k.+1}|%:R / (#|{: clause n k.+1}| +
    #|{: clause n k * bool}|)%:R = 1 - k.+1%:R / n.+1%:R :> R.
  rewrite -wB; apply/eqP; rewrite eq_sym subr_eq -mulrDl -natrD divff //.
by rewrite wA wB.
Qed.

