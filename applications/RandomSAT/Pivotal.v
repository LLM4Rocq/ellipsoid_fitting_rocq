From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import arithmetic_tactic ring_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: the variance of the lifetime                               *)
(*                                                                            *)
(* Part of target T7 of phase 12 (see Model.v). A Rocq formalization of the   *)
(* credited argument of the lemmas 'Deletion variance bound' and 'Pivotal     *)
(* pairs' of 'A limiting satisfiability threshold for every fixed clause      *)
(* size' (family 235 of the OpenAI math collection, revision 1581d4cbd,       *)
(* source/sections/concentration.tex), in the recursive form of the Lean      *)
(* development of the collection, which this file follows                     *)
(* (lean/OAI/Probability/RandomSAT):                                          *)
(* Lean: clauseAverage (ClauseProcess.lean, line 148)                         *)
(* Lean: survival (ClauseProcess.lean, line 152)                              *)
(* Lean: survival_le_geometric (Variance.lean, line 135)                      *)
(* Lean: insertionSecond_succ (Variance.lean, line 204)                       *)
(* Lean: pivotal_local_bound (Variance.lean, line 243)                        *)
(* Lean: insertionSecond_le_occupation (Variance.lean, line 285)              *)
(* Lean: lifetimeVariance_succ_le (Variance.lean, line 330)                   *)
(* Lean: lifetimeVariance_le_occupation (Variance.lean, line 361)             *)
(*                                                                            *)
(* S is a set of assignments on n variables, and the clauses of size k are    *)
(* uniform and independent; the means are those of finite_mean.v.             *)
(*                                                                            *)
(* - clause_avg k f S is the mean of f (add_clause S c) over one clause c,    *)
(*   tuple_avg k m f S the mean of f (restrict S t) over m clauses t,         *)
(*   survival k m S the probability that S survives m clauses, and kill k S   *)
(*   the probability that one clause empties S. survival_le_geom: survival k  *)
(*   d S <= (1 - kill k S)^d, since each of the d clauses must spare S.       *)
(* - life_mean m S and life_var m S are the mean and the variance of the      *)
(*   lifetime life S t over m clauses t.                                      *)
(* - life_var_succ_le: by the law of total variance for the first clause      *)
(*   (unif_var_tuple_cons), the variance over m.+1 clauses is at most the     *)
(*   mean over the first clause of the variance over the other m, plus the    *)
(*   second moment second m S of the change of the lifetime when a clause is  *)
(*   inserted in front (delay).                                               *)
(* - With trunc M S = min(M kill k S, 1) and occ f m S the sum over j < m of  *)
(*   the mean of f after j clauses, secondS and pivotal_local give second m S *)
(*   <= 2 occ (trunc M) m.+1 S for m < M (second_le_occ).                     *)
(* - life_var_le_occ: if clause n k is not empty (k <= n), then life_var m S  *)
(*   <= 2 m occ (trunc M) m S for m <= M.                                     *)
(*                                                                            *)
(* The manuscript omits the clause i, bounds Var V by the sum over i of E     *)
(* (V^(-i) - V)^2 (the omission form of the Efron-Stein inequality,           *)
(* efron_stein_omission in library/probability/efron_stein_omission.v), and   *)
(* counts the pairs of pivotal times. The recursion here inserts a clause in  *)
(* front instead, as the Lean development does, and gives a bound of the same *)
(* form: 2 M times the sum over the M prefixes of the mean of min(M q, 1),    *)
(* with q the killing probability.                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section clause_means.
Context {R : realType} (n k : nat).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C := (clause n k).

(* The mean over one uniform clause, and over m independent ones. *)
Definition clause_avg (f : {set asg} -> R) (S : {set asg}) : R :=
  unif_mean (fun c : C => f (add_clause S c)).

Definition tuple_avg m (f : {set asg} -> R) (S : {set asg}) : R :=
  unif_mean (fun t : m.-tuple C => f (restrict S t)).

Definition survival m (S : {set asg}) : R := tuple_avg m alive S.

Lemma tuple_avg0 f S : tuple_avg 0 f S = f S.
Proof. by rewrite /tuple_avg unif_mean_tuple0. Qed.

Lemma tuple_avgS m f S : tuple_avg m.+1 f S = clause_avg (tuple_avg m f) S.
Proof. by rewrite /tuple_avg unif_mean_tuple_cons. Qed.

Lemma ler_clause_avg (f g : {set asg} -> R) S :
  (forall T, f T <= g T) -> clause_avg f S <= clause_avg g S.
Proof. by move=> fg; apply: ler_unif_mean => c; exact: fg. Qed.

Lemma ler_tuple_avg m (f g : {set asg} -> R) S :
  (forall T, f T <= g T) -> tuple_avg m f S <= tuple_avg m g S.
Proof. by move=> fg; apply: ler_unif_mean => t; exact: fg. Qed.

Lemma survival_ge0 m S : 0 <= survival m S.
Proof. by apply: unif_mean_ge0 => t; exact: alive_ge0. Qed.

Lemma survival_mono m (S T : {set asg}) :
  S \subset T -> survival m S <= survival m T.
Proof.
move=> ST; apply: ler_unif_mean => t.
by apply: alive_mono; exact: restrict_mono.
Qed.

Lemma survival0_set m : survival m (set0 : {set asg}) = 0.
Proof.
rewrite /survival /tuple_avg (eq_unif_mean (g := fun=> 0)) /unif_mean ?big1 ?mulr0 //.
by move=> t; rewrite restrictE (_ : [set x in _ | _] = set0) ?alive0 //;
  apply/setP => x; rewrite !inE.
Qed.

Hypothesis C0 : (0 < #|{: C}|)%N.

Lemma clause_avg_cst (c : R) S : clause_avg (fun=> c) S = c.
Proof. exact: unif_mean_cst. Qed.

Lemma survival_le1 m S : survival m S <= 1.
Proof.
apply: unif_mean_le; last by move=> t; exact: alive_le1.
by rewrite card_tuple expn_gt0 C0.
Qed.

(* The probability that one uniform clause kills S. *)
Definition kill (S : {set asg}) : R :=
  unif_mean (fun c : C => alive S - alive (add_clause S c)).

Lemma kill_ge0 S : 0 <= kill S.
Proof.
by apply: unif_mean_ge0 => c; rewrite subr_ge0 alive_mono ?add_clause_sub.
Qed.

Lemma kill_le1 S : kill S <= 1.
Proof.
apply: unif_mean_le => // c.
by have := alive_le1 (R := R) S; have := alive_ge0 (R := R) (add_clause S c); lra.
Qed.

Lemma kill0 : kill set0 = 0.
Proof.
rewrite /kill (eq_unif_mean (g := fun=> 0)) ?unif_mean_cst // => c.
by rewrite add_clause0 subrr.
Qed.

Lemma killE S : kill S = alive S - survival 1 S.
Proof.
rewrite /kill unif_meanB unif_mean_cst //; congr (_ - _).
by rewrite /survival tuple_avgS /clause_avg; apply: eq_unif_mean => c;
  rewrite tuple_avg0.
Qed.

(* A solution of all the clauses of s satisfies each of them. *)
Lemma alive_restrict_le (S : {set asg}) (s : seq C) :
  alive (restrict S s) <= \prod_(c <- s) alive (add_clause S c) :> R.
Proof.
elim: s S => [|c s IH] S /=; first by rewrite big_nil alive_le1.
rewrite big_cons; have [Sc0|Sc0] := eqVneq (add_clause S c) set0.
  have -> : restrict (add_clause S c) s = set0.
    by apply/eqP; rewrite -subset0 -Sc0; exact: restrict_sub.
  by rewrite Sc0 alive0 mul0r lexx.
have -> : alive (add_clause S c) = 1 :> R by rewrite /alive Sc0.
rewrite mul1r (le_trans (IH _)) //; apply: ler_prod => d _.
by rewrite alive_ge0 alive_mono // add_clause_mono // add_clause_sub.
Qed.

(* Surviving d clauses requires that none of them kills S on its own. *)
Lemma survival_le_geom d S : survival d S <= (1 - kill S) ^+ d.
Proof.
have [->|S0] := eqVneq S set0.
  by rewrite survival0_set kill0 subr0 expr1n.
have aS : alive S = 1 :> R by rewrite /alive S0.
have -> : 1 - kill S = unif_mean (fun c : C => alive (add_clause S c)).
  by rewrite /kill unif_meanB unif_mean_cst // aS opprB addrC subrK.
rewrite -unif_mean_tuple_prod; apply: ler_unif_mean => t.
exact: alive_restrict_le.
Qed.

End clause_means.

Arguments clause_avg {R n} k f S.
Arguments tuple_avg {R n} k m f S.
Arguments survival {R n} k m S.
Arguments kill {R n} k S.

Section lifetime.
Context {R : realType} (n k : nat).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C := (clause n k).
Hypothesis C0 : (0 < #|{: C}|)%N.

Let T0 m : (0 < #|{: m.-tuple C}|)%N.
Proof. by rewrite card_tuple expn_gt0 C0. Qed.

Definition life_mean m (S : {set asg}) : R :=
  unif_mean (fun t : m.-tuple C => life S t).

Definition life_var m (S : {set asg}) : R :=
  unif_var (fun t : m.-tuple C => life S t).

Lemma life_meanS m S :
  life_mean m.+1 S = clause_avg k (fun T => alive T + life_mean m T) S.
Proof.
rewrite /life_mean unif_mean_tuple_cons /clause_avg; apply: eq_unif_mean => c.
by rewrite unif_meanD unif_mean_cst.
Qed.

Lemma life_mean_ge0 m S : 0 <= life_mean m S.
Proof. by apply: unif_mean_ge0 => t; exact: life_ge0. Qed.

Lemma life_mean_sum m S :
  life_mean m S = \sum_(j < m) survival k j.+1 S.
Proof.
elim: m S => [|m IH] S.
  by rewrite big_ord0 /life_mean unif_mean_tuple0.
rewrite life_meanS big_ord_recl /clause_avg.
under eq_unif_mean do rewrite IH.
rewrite unif_meanD unif_mean_sum; congr (_ + _).
  by rewrite /survival tuple_avgS; apply: eq_unif_mean => c; rewrite tuple_avg0.
by apply: eq_bigr => j _; rewrite /survival [in RHS]tuple_avgS.
Qed.

(* Inserting the clause c at the front: the change of the lifetime. *)
Definition delay m (S : {set asg}) (c : C) (t : m.-tuple C) : R :=
  (alive S + life S t) - (alive (add_clause S c) + life (add_clause S c) t).

Definition second m (S : {set asg}) : R :=
  unif_mean (fun c : C => unif_mean (fun t : m.-tuple C => delay S c t ^+ 2)).

Lemma delay_cons m S (c d : C) (t : m.-tuple C) :
  delay S c [tuple of d :: t] =
  alive S - alive (add_clause S c) + delay (add_clause S d) c t.
Proof. by rewrite /delay /= add_clauseC; ring. Qed.

Lemma bool_diff_sqr (a b : bool) :
  (b ==> a) -> (a%:R - b%:R : R) ^+ 2 = a%:R - b%:R.
Proof. by case: a; case: b => //= _; rewrite ?subrr ?subr0 ?expr0n ?expr1n. Qed.

Lemma pivot_sqr S (c : C) :
  (alive S - alive (add_clause S c)) ^+ 2 = alive S - alive (add_clause S c) :> R.
Proof.
rewrite /alive bool_diff_sqr //; apply/implyP => h.
by apply: contra_neq h => ->; rewrite add_clause0.
Qed.

Lemma delay_cross m (S T : {set asg}) (c : C) (t : m.-tuple C) :
  T \subset S ->
  (alive S - alive (add_clause S c)) * delay T c t =
  (alive S - alive (add_clause S c)) * (alive T + life T t).
Proof.
move=> TS; have [Sc0|Sc0] := eqVneq (add_clause S c) set0; last first.
  have -> : alive (add_clause S c) = 1 :> R by rewrite /alive Sc0.
  have -> : alive S = 1 :> R.
    rewrite /alive; case: (eqVneq S set0) => // S0.
    by move: Sc0; rewrite S0 add_clause0 eqxx.
  by rewrite subrr !mul0r.
rewrite /delay; have -> : add_clause T c = set0.
  by apply/eqP; rewrite -subset0 -Sc0; exact: add_clause_mono.
by rewrite alive0 life0 addr0 subr0.
Qed.

Lemma delay_cons_sqr m S (c d : C) (t : m.-tuple C) :
  delay S c [tuple of d :: t] ^+ 2 =
  delay (add_clause S d) c t ^+ 2 + (alive S - alive (add_clause S c)) +
  2 * (alive S - alive (add_clause S c)) *
    (alive (add_clause S d) + life (add_clause S d) t).
Proof.
rewrite delay_cons sqrrD pivot_sqr (delay_cross c t (add_clause_sub S d)).
by rewrite mulr2n; ring.
Qed.

Lemma second0 S : second 0 S = kill k S.
Proof.
rewrite /second /kill; apply: eq_unif_mean => c.
by rewrite unif_mean_tuple0 /delay /= !addr0 pivot_sqr.
Qed.

Lemma secondS m S :
  second m.+1 S =
  clause_avg k (second m) S + kill k S * (1 + 2 * life_mean m.+1 S).
Proof.
have hY : unif_mean (fun d : C => unif_mean (fun t : m.-tuple C =>
    alive (add_clause S d) + life (add_clause S d) t)) = life_mean m.+1 S.
  rewrite life_meanS /clause_avg; apply: eq_unif_mean => d.
  by rewrite unif_meanD unif_mean_cst.
have inner c : unif_mean (fun t : m.+1.-tuple C => delay S c t ^+ 2) =
    unif_mean (fun d : C => unif_mean (fun t : m.-tuple C =>
      delay (add_clause S d) c t ^+ 2)) +
    (alive S - alive (add_clause S c)) * (1 + 2 * life_mean m.+1 S).
  rewrite unif_mean_tuple_cons.
  under eq_unif_mean => d do under eq_unif_mean => t do
    rewrite delay_cons_sqr -addrA.
  under eq_unif_mean => d do rewrite unif_meanD.
  rewrite unif_meanD; congr (_ + _).
  under eq_unif_mean => d do rewrite unif_meanD unif_mean_cst // unif_meanZ.
  by rewrite unif_meanD unif_mean_cst // unif_meanZ hY; ring.
rewrite /second (eq_unif_mean inner) unif_meanD unif_meanZr; congr (_ + _).
rewrite /clause_avg /second.
exact: (unif_mean_comm (fun c d => unif_mean (fun t : m.-tuple C =>
  delay (add_clause S d) c t ^+ 2))).
Qed.

Lemma second_ge0 m S : 0 <= second m S.
Proof.
by apply: unif_mean_ge0 => c; apply: unif_mean_ge0 => t; exact: sqr_ge0.
Qed.

Lemma geom_sum_le (q : R) t : 0 <= q -> q <= 1 ->
  q * \sum_(j < t) (1 - q) ^+ j <= Num.min (t%:R * q) 1.
Proof.
move=> q0 q1; have q1' : 0 <= 1 - q by rewrite subr_ge0.
have hg : q * \sum_(j < t) (1 - q) ^+ j = 1 - (1 - q) ^+ t.
  elim: t => [|t IH]; first by rewrite big_ord0 mulr0 expr0 subrr.
  by rewrite big_ord_recr /= mulrDr IH exprSr; ring.
rewrite le_min; apply/andP; split.
  apply: le_trans (_ : q * \sum_(j < t) 1 <= _).
    apply: (ler_wpM2l q0); apply: ler_sum => j _.
    by apply: exprn_ile1 => //; rewrite lerBlDr lerDl.
  by rewrite sumr_const card_ord -[1 *+ t]mulr_natl mulr1 mulrC.
by rewrite hg lerBlDr lerDl exprn_ge0.
Qed.

(* The killing chance, truncated at 1 / M. *)
Definition trunc M (S : {set asg}) : R := Num.min (M%:R * kill k S) 1.

Lemma trunc_ge0 M S : 0 <= trunc M S.
Proof. by rewrite le_min ler01 mulr_ge0 ?ler0n ?kill_ge0. Qed.

Lemma pivotal_local m M S : (m.+1 <= M)%N ->
  kill k S * (1 + 2 * life_mean m S) <= 2 * trunc M S.
Proof.
move=> mM; set q := kill k S; have q0 : 0 <= q := kill_ge0 k S.
have q1 : q <= 1 := kill_le1 C0 S.
have hs : 1 + life_mean m S <= \sum_(j < m.+1) (1 - q) ^+ j.
  rewrite life_mean_sum big_ord_recl expr0 lerD2l; apply: ler_sum => j _.
  exact: survival_le_geom.
have hq : q * (1 + life_mean m S) <= trunc M S.
  apply: le_trans (ler_wpM2l q0 hs) _; apply: le_trans (geom_sum_le _ q0 q1) _.
  rewrite /trunc le_min; apply/andP; split; rewrite ge_min; apply/orP.
    by left; rewrite ler_wpM2r // ler_nat.
  by right.
have := life_mean_ge0 m S; nra.
Qed.

(* The occupation sum of f along the first m clauses. *)
Definition occ (f : {set asg} -> R) m (S : {set asg}) : R :=
  \sum_(j < m) tuple_avg k j f S.

Lemma occS f m S : occ f m.+1 S = f S + clause_avg k (occ f m) S.
Proof.
rewrite /occ big_ord_recl tuple_avg0; congr (_ + _).
rewrite /clause_avg unif_mean_sum; apply: eq_bigr => j _.
by rewrite tuple_avgS.
Qed.

Lemma occ_ge0 f m S : (forall T, 0 <= f T) -> 0 <= occ f m S.
Proof.
move=> f0; apply: sumr_ge0 => j _; apply: unif_mean_ge0 => t; exact: f0.
Qed.

Lemma second_le_occ m M S : (m.+1 <= M)%N ->
  second m S <= 2 * occ (trunc M) m.+1 S.
Proof.
elim: m S => [|m IH] S mM.
  rewrite second0 occS.
  have -> : clause_avg k (occ (trunc M) 0) S = 0.
    rewrite /clause_avg (eq_unif_mean (g := fun=> 0)) ?unif_mean_cst // => c.
    by rewrite /occ big_ord0.
  rewrite addr0.
  have := pivotal_local (m := 0) S mM; rewrite /life_mean unif_mean_tuple0 /=.
  by rewrite mulr0 addr0 mulr1.
rewrite secondS occS [2 * (_ + _)]mulrDr.
have h1 := pivotal_local (m := m.+1) S mM.
have h2 : clause_avg k (second m) S <= 2 * clause_avg k (occ (trunc M) m.+1) S.
  rewrite /clause_avg -unif_meanZ; apply: ler_unif_mean => c.
  by apply: IH; exact: ltnW.
by rewrite addrC; apply: lerD.
Qed.

Lemma life_var_succ_le m S :
  life_var m.+1 S <= clause_avg k (life_var m) S + second m S.
Proof.
rewrite /life_var unif_var_tuple_cons //; apply: lerD.
  rewrite /clause_avg; apply: ler_unif_mean => c /=.
  by rewrite unif_var_addl.
set c0 := alive S + life_mean m S.
apply: le_trans (unif_var_le _ c0 C0) _.
rewrite /second; apply: ler_unif_mean => c /=.
have -> : unif_mean (fun t : m.-tuple C =>
    alive (add_clause S c) + life (add_clause S c) t) - c0 =
  - unif_mean (fun t : m.-tuple C => delay S c t).
  by rewrite /delay unif_meanB !unif_meanD !unif_mean_cst // /c0 /life_mean; ring.
by rewrite sqrrN; exact: unif_mean_sqr_le.
Qed.

(* The variance of the lifetime is at most 2 m times the occupation sum of
   the truncated killing chance. *)
Lemma life_var_le_occ m M S : (m <= M)%N ->
  life_var m S <= 2 * m%:R * occ (trunc M) m S.
Proof.
elim: m S => [|m IH] S mM.
  by rewrite /life_var /unif_var !unif_mean_tuple0 subrr expr0n /= mulr0 mul0r.
apply: le_trans (life_var_succ_le m S) _.
have h1 := second_le_occ S mM.
have h2 : clause_avg k (life_var m) S <=
    2 * m%:R * clause_avg k (occ (trunc M) m) S.
  rewrite /clause_avg -unif_meanZ; apply: ler_unif_mean => c.
  by apply: IH; exact: ltnW.
have h3 : clause_avg k (occ (trunc M) m) S <= occ (trunc M) m.+1 S.
  by rewrite occS lerDr trunc_ge0.
have h4 : 0 <= 2 * m%:R :> R by rewrite mulr_ge0 ?ler0n.
apply: le_trans (lerD h2 h1) _.
have -> : 2 * m.+1%:R * occ (trunc M) m.+1 S =
    2 * m%:R * occ (trunc M) m.+1 S + 2 * occ (trunc M) m.+1 S.
  by rewrite -addn1 natrD; ring.
by rewrite lerD2r ler_wpM2l.
Qed.

End lifetime.

