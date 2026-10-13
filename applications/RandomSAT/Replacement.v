From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model Pivotal.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: forced variables and the replacement of a shorter clause   *)
(*                                                                            *)
(* Part of target T7 of phase 12 (see Model.v). A Rocq formalization of the   *)
(* credited argument of the subsection 'Killing a solution set with one       *)
(* clause' and of the lemma 'Replacing a (k-1)-clause' of 'A limiting         *)
(* satisfiability threshold for every fixed clause size' (family 235 of the   *)
(* OpenAI math collection, revision 1581d4cbd, source/sections/forcing.tex),  *)
(* following the Lean development of the collection                           *)
(* (lean/OAI/Probability/RandomSAT):                                          *)
(* Lean: forcedVariables (Clauses.lean, line 162)                             *)
(* Lean: card_killingClauses (Clauses.lean, line 216)                         *)
(* Lean: killFraction (Replacement.lean, line 18)                             *)
(* Lean: killFraction_le_pow (Replacement.lean, line 56)                      *)
(* Lean: replacement_numeric (Replacement.lean, line 228)                     *)
(* Lean: shorter_clause_replacement (Replacement.lean, line 324)              *)
(*                                                                            *)
(* S is a set of assignments on n variables.                                  *)
(*                                                                            *)
(* - forced S is the set of the variables on which all the elements of S      *)
(*   agree, and is empty when S is empty, as b(H) = 0 for an unsatisfiable H  *)
(*   in the manuscript; frozen S s0 is the set of the variables on which they *)
(*   all agree with s0 (forced_frozen).                                       *)
(* - A clause empties a nonempty S exactly when its variables are forced and  *)
(*   its signs oppose the forced values (kills_frozen, frozen_kills), so      *)
(*   these clauses correspond to the sets of k forced variables (card_kills). *)
(*   With kfrac b v r = 'C(b, r) / ('C(v, r) 2^r), the killing probability of *)
(*   a nonempty S is kfrac #|forced S| n k (killE_forced): the q_r(H) = (b)_r *)
(*   / (2^r (v)_r) of the manuscript.                                         *)
(* - Bounds on kfrac: kfrac b v r <= (b / v)^r (kfrac_le_pow), the recursion  *)
(*   in r (kfrac_succ) and its lower bound (kfrac_succ_lower), and kfrac b v  *)
(*   r <= 1 / (v + 1) when b <= r, for few forced variables (kfrac_small).    *)
(* - kill_replacement, the lemma 'Replacing a (k-1)-clause': for 1 <= r < v,  *)
(*   a > 0 with 1 / (v + 1) <= a^-r and g >= 2 (r + 1) a, the probability     *)
(*   that a block of g independent clauses of size r + 1 empties S is at      *)
(*   least kill r S - a^-r. The manuscript takes r = k - 1, v = n - 1, a =    *)
(*   n^(1/k) and g = ceil(2 k n^(1/k)); the lemma assumes only the            *)
(*   inequalities that these choices satisfy.                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section killing_clauses.
Variable n : nat.
Local Notation asg := {ffun 'I_n -> bool}.

Definition support k (c : clause n k) : {set 'I_n} := [set i | val c i != None].

Lemma card_support_clause k (c : clause n k) : #|support c| = k.
Proof. by have := valP c; rewrite /proper_clause => /eqP. Qed.

(* The variables on which all the assignments of S agree with s0. *)
Definition frozen (S : {set asg}) (s0 : asg) : {set 'I_n} :=
  [set i | [forall s in S, s i == s0 i]].

(* The variables forced by S: those on which all its elements agree, when S
   is not empty. *)
Definition forced (S : {set asg}) : {set 'I_n} :=
  [set i | (S != set0) && [exists b, [forall s in S, s i == b]]].

Lemma forced_frozen (S : {set asg}) (s0 : asg) : s0 \in S -> forced S = frozen S s0.
Proof.
move=> s0S; apply/setP => i; rewrite !inE.
have -> /= : S != set0 by apply/set0Pn; exists s0.
apply/existsP/forall_inP => [[b /forall_inP h] s sS|h].
  by rewrite (eqP (h s sS)) (eqP (h s0 s0S)).
by exists (s0 i); apply/forall_inP.
Qed.

Lemma forced0 : forced set0 = set0.
Proof. by apply/setP => i; rewrite !inE eqxx. Qed.

(* A clause kills S when no element of S satisfies it: then each of its
   variables is frozen in S with the sign opposite to the frozen value. *)
Lemma kills_frozen k (S : {set asg}) (s0 : asg) (c : clause n k) : s0 \in S ->
  add_clause S c = set0 ->
  forall i, val c i != None -> (i \in frozen S s0) /\ val c i = Some (~~ s0 i).
Proof.
move=> s0S Sc i ci.
have opp s : s \in S -> val c i = Some (~~ s i).
  move=> sS; have : s \notin add_clause S c by rewrite Sc inE.
  rewrite inE sS /= /clause_sat negb_exists => /forallP /(_ i).
  by case: (val c i) ci => // b _; case: b; case: (s i).
split; last exact: opp.
rewrite inE; apply/forall_inP => s sS.
by have := opp s sS; rewrite (opp s0 s0S) => -[] /negbLR <-; rewrite negbK.
Qed.

Lemma frozen_kills k (S : {set asg}) (s0 : asg) (c : clause n k) : s0 \in S ->
  (forall i, val c i != None -> (i \in frozen S s0) /\ val c i = Some (~~ s0 i)) ->
  add_clause S c = set0.
Proof.
move=> s0S h; apply/setP => s; rewrite !inE; apply/negP => /andP[sS].
move=> /existsP[i /eqP ci].
have [] := h i; first by rewrite ci.
rewrite inE => /forall_inP /(_ s sS) /eqP si.
by rewrite ci si => -[] /eqP; case: (s0 i).
Qed.

(* The opposing clause on a set A of k variables. *)
Definition opp_ffun (s0 : asg) (A : {set 'I_n}) : {ffun 'I_n -> option bool} :=
  [ffun i => if i \in A then Some (~~ s0 i) else None].

Lemma proper_opp k s0 (A : {set 'I_n}) : #|A| = k -> proper_clause k (opp_ffun s0 A).
Proof.
move=> Ak; rewrite /proper_clause -Ak; apply/eqP; apply: eq_card => i.
by rewrite !inE ffunE; case: (i \in A).
Qed.

(* The killing clauses of a nonempty S correspond to the sets of k forced
   variables. *)
Lemma card_kills k (S : {set asg}) : S != set0 ->
  #|[set c : clause n k | add_clause S c == set0]| = 'C(#|forced S|, k).
Proof.
case/set0Pn => s0 s0S; rewrite (forced_frozen s0S).
set D := [set c : clause n k | add_clause S c == set0].
have inj : {in D &, injective (@support k)}.
  move=> c d; rewrite !inE => /eqP hc /eqP hd e; apply: val_inj.
  apply/ffunP => i; move/setP: e => /(_ i); rewrite !inE.
  case ci: (val c i) => [b|]; case di: (val d i) => [b'|] //= _.
  have ci' : val c i != None by rewrite ci.
  have di' : val d i != None by rewrite di.
  have [_ ec] := kills_frozen s0S hc ci'.
  have [_ ed] := kills_frozen s0S hd di'.
  by rewrite -ci -di ec ed.
rewrite -(card_in_imset inj) -cards_draws; apply: eq_card => A; rewrite !inE.
apply/imsetP/andP => [[c cD ->]|[AF /eqP Ak]].
  move: cD; rewrite inE => /eqP hc; split; last by rewrite card_support_clause.
  apply/subsetP => i; rewrite inE => ci.
  by have [] := kills_frozen s0S hc ci.
pose c : clause n k := exist (fun f => proper_clause k f) _ (proper_opp s0 Ak).
exists c.
  rewrite inE; apply/eqP; apply: (frozen_kills s0S) => i /=.
  rewrite ffunE; case iA: (i \in A) => // _; split => //.
  exact: (subsetP AF).
by apply/setP => i; rewrite !inE ffunE; case: (i \in A).
Qed.

End killing_clauses.

(* The fraction of the clauses of size r on v variables whose variables all
   lie in a given set of b variables, with prescribed signs. *)
Definition kfrac {R : realType} (b v r : nat) : R :=
  'C(b, r)%:R / ('C(v, r)%:R * 2 ^+ r).

(* The probability that a uniform k-clause kills a nonempty S. *)
Lemma killE_forced (R : realType) n k (S : {set {ffun 'I_n -> bool}}) :
  S != set0 -> kill (R := R) k S = kfrac #|forced S| n k.
Proof.
move=> S0.
have e : (fun c : clause n k => alive S - alive (add_clause S c) : R) =1
    (fun c : clause n k => (add_clause S c == set0)%:R : R).
  by move=> c; rewrite /alive S0; case: (add_clause S c == set0); rewrite /= ?subr0 ?subrr.
rewrite /kill (eq_unif_mean e) unif_mean_indicator card_kills // card_clause.
by rewrite /kfrac natrM natrX.
Qed.

Section kfrac.
Context {R : realType}.
Local Notation kfrac := (@kfrac R).

Lemma kfrac_ge0 b v r : 0 <= kfrac b v r.
Proof. by rewrite /kfrac divr_ge0 ?mulr_ge0 ?exprn_ge0 ?ler0n. Qed.

Lemma kfrac0 b v : kfrac b v 0 = 1.
Proof. by rewrite /kfrac !bin0 expr0 mulr1 divr1. Qed.

Lemma kfrac_succ b v r : (r < v)%N ->
  kfrac b v r.+1 = kfrac b v r * (b - r)%:R / (2 * (v - r)%:R).
Proof.
move=> rv.
have cv : 'C(v, r)%:R != 0 :> R by rewrite pnatr_eq0 -lt0n bin_gt0 ltnW.
have vr : (v - r)%:R != 0 :> R by rewrite pnatr_eq0 subn_eq0 -ltnNge.
have r1 : r.+1%:R != 0 :> R by rewrite pnatr_eq0.
have hb : 'C(b, r.+1)%:R = (b - r)%:R * 'C(b, r)%:R / r.+1%:R :> R.
  by rewrite -natrM -mul_bin_left natrM mulrC (mulKf r1).
have hv : 'C(v, r.+1)%:R = (v - r)%:R * 'C(v, r)%:R / r.+1%:R :> R.
  by rewrite -natrM -mul_bin_left natrM mulrC (mulKf r1).
have t0 : 2 ^+ r != 0 :> R by rewrite expf_neq0 // pnatr_eq0.
have two0 : 2 != 0 :> R by rewrite pnatr_eq0.
by rewrite /kfrac hb hv exprS; field by rewrite ?vr ?t0 ?cv ?nat1r ?r1.
Qed.

Lemma ratio_le b v r : (b <= v)%N -> (r <= b)%N -> (r < v)%N ->
  (b - r)%:R / (v - r)%:R <= b%:R / v%:R :> R.
Proof.
move=> bv rb rv.
have v0 : 0 < v%:R :> R by rewrite ltr0n (leq_ltn_trans (leq0n r)).
have vr0 : 0 < (v - r)%:R :> R by rewrite ltr0n subn_gt0.
have rv' : (r <= v)%N := ltnW rv.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr // natrB // natrB //.
rewrite mulrBl mulrBr lerD2l lerN2 [b%:R * _]mulrC.
by apply: ler_wpM2l; rewrite ?ler0n // ler_nat.
Qed.

Lemma kfrac_le_pow b v r : (b <= v)%N -> (r <= v)%N -> (0 < v)%N ->
  kfrac b v r <= (b%:R / (2 * v%:R)) ^+ r.
Proof.
move=> bv rv v0; elim: r rv => [|r IH] rv; first by rewrite kfrac0 expr0.
have [br|rb] := ltnP b r.+1.
  by rewrite /kfrac bin_small // mul0r exprn_ge0 // divr_ge0 ?mulr_ge0.
rewrite kfrac_succ // exprSr -mulrA.
apply: ler_pM; first exact: kfrac_ge0.
- by rewrite divr_ge0 ?mulr_ge0.
- exact: IH (ltnW rv).
rewrite !invfM mulrCA [b%:R * _]mulrCA.
apply: ler_wpM2l; first by rewrite invr_ge0.
exact: (ratio_le bv (ltnW rb) rv).
Qed.

Lemma kfrac_le_half_pow b v r : (b <= v)%N -> (r <= v)%N -> (0 < v)%N ->
  kfrac b v r <= 2^-1 ^+ r.
Proof.
move=> bv rv v0; apply: le_trans (kfrac_le_pow bv rv v0) _.
have v0' : 0 < v%:R :> R by rewrite ltr0n.
apply: lerXn2r; rewrite ?nnegrE.
- by rewrite divr_ge0 // mulr_ge0.
- by rewrite invr_ge0.
rewrite invfM mulrCA -[X in _ <= X]mulr1; apply: ler_wpM2l.
  by rewrite invr_ge0.
by rewrite ler_pdivrMr // mul1r ler_nat.
Qed.

Lemma bin_ge_internal v r : (1 <= r)%N -> (r < v)%N -> (v <= 'C(v, r))%N.
Proof.
elim: v r => [|v IH] [|r] // r1 rv.
case: r r1 rv => [|r] _ rv; first by rewrite bin1.
rewrite binS; have rv' : (r.+1 < v)%N by [].
apply: leq_trans (_ : (1 + v <= _)%N); first by rewrite add1n.
by apply: leq_add; [rewrite bin_gt0 | exact: IH].
Qed.

Lemma kfrac_small b v r : (1 <= r)%N -> (r < v)%N -> (b <= r)%N ->
  kfrac b v r <= (v.+1%:R)^-1.
Proof.
move=> r1 rv br.
have v0 : (0 < v)%N by apply: leq_ltn_trans rv.
have hc : 'C(b, r)%:R <= 1 :> R.
  have [-> //|bltr] := eqVneq b r; first by rewrite binn.
  by rewrite bin_small ?ler01 // ltn_neqAle bltr br.
have h2 : 2 <= 2 ^+ r :> R.
  by rewrite -[X in X <= _]expr1 ler_eXn2l // ltr1n.
have Cv0 : 0 < 'C(v, r)%:R :> R by rewrite ltr0n bin_gt0 ltnW.
have den : v.+1%:R <= 'C(v, r)%:R * 2 ^+ r :> R.
  have : v.+1%:R <= v%:R * 2 :> R.
    by rewrite -natrM ler_nat muln2 -addnn -addn1 leq_add2l.
  move/le_trans; apply.
  by apply: ler_pM; rewrite ?ler0n // ler_nat bin_ge_internal.
have D0 : 0 < 'C(v, r)%:R * 2 ^+ r :> R by rewrite mulr_gt0 ?exprn_gt0.
rewrite /kfrac; apply: le_trans (_ : 1 / ('C(v, r)%:R * 2 ^+ r) <= _).
  by rewrite ler_pdivrMr // divfK ?gt_eqF.
by rewrite div1r lef_pV2 ?posrE ?ltr0n.
Qed.

Lemma kfrac_succ_lower b v r : (r.+1 <= b)%N -> (r < v)%N ->
  kfrac b v r * (b%:R / (2 * v%:R)) / r.+1%:R <= kfrac b v r.+1.
Proof.
move=> rb rv; rewrite kfrac_succ //.
move: (kfrac b v r) (kfrac_ge0 b v r) => K K0.
have v0 : 0 < v%:R :> R by rewrite ltr0n (leq_ltn_trans (leq0n r)).
have vr0 : 0 < (v - r)%:R :> R by rewrite ltr0n subn_gt0.
have r0 : 0 < r.+1%:R :> R by rewrite ltr0n.
have hb : (b <= (b - r) * r.+1)%N.
  rewrite mulnS -[X in (X <= _)%N](subnK (ltnW rb)) leq_add2l.
  by rewrite leq_pmull // subn_gt0.
have core : b%:R / (2 * v%:R) / r.+1%:R <= (b - r)%:R / (2 * (v - r)%:R) :> R.
  apply: le_trans (_ : (b - r)%:R / (2 * v%:R) <= _).
    rewrite mulrAC; apply: ler_wpM2r; first by rewrite invr_ge0 mulr_ge0.
    by rewrite ler_pdivrMr // -natrM ler_nat.
  apply: ler_wpM2l; first exact: ler0n.
  rewrite lef_pV2 ?posrE ?mulr_gt0 //.
  by apply: ler_wpM2l; rewrite ?ler0n // ler_nat leq_subr.
by rewrite -mulrA -[X in _ <= X]mulrA; apply: ler_wpM2l.
Qed.



Lemma power_survival_bound (q : R) g : 0 <= q -> q <= 1 ->
  (1 - q) ^+ g * (1 + g%:R * q) <= 1.
Proof.
move=> q0 q1; elim: g => [|g IH]; first by rewrite expr0 mul0r addr0 mulr1.
have hs : (1 - q) * (1 + g.+1%:R * q) <= 1 + g%:R * q.
  have -> : (1 - q) * (1 + g.+1%:R * q) = 1 + g%:R * q - g.+1%:R * q ^+ 2.
    by rewrite -nat1r; ring.
  by rewrite lerBlDr lerDl mulr_ge0 // sqr_ge0.
apply: le_trans IH; rewrite exprSr -mulrA ler_wpM2l //.
by rewrite exprn_ge0 // subr_ge0.
Qed.

Lemma block_ge_of_double (x q : R) g : 0 <= x -> 2 * x <= 1 -> 0 <= q ->
  q <= 1 -> 2 * x <= g%:R * q -> x <= 1 - (1 - q) ^+ g.
Proof.
move=> x0 xh q0 q1 hg.
have h := power_survival_bound g q0 q1.
have p0 : 0 <= (1 - q) ^+ g by rewrite exprn_ge0 // subr_ge0.
have h1 : (1 - q) ^+ g * (1 + 2 * x) <= 1.
  by apply: le_trans h; rewrite ler_wpM2l // lerD2l.
have hx2 : 0 < 1 + 2 * x by rewrite ltr_wpDr // mulr_ge0.
have h2 : 1 <= (1 - x) * (1 + 2 * x).
  have -> : (1 - x) * (1 + 2 * x) = 1 + x * (1 - 2 * x) by ring.
  by rewrite lerDl mulr_ge0 // subr_ge0.
have : (1 - q) ^+ g <= 1 - x.
  rewrite -(ler_pM2r hx2); exact: le_trans h1 h2.
by rewrite lerBrDr addrC -lerBrDr.
Qed.

Lemma replacement_numeric b v r g (a : R) : (1 <= r)%N -> (r < v)%N ->
  (b <= v)%N -> 0 < a -> (v.+1%:R)^-1 <= a^-1 ^+ r -> 2 * r.+1%:R * a <= g%:R ->
  kfrac b v r - a^-1 ^+ r <= 1 - (1 - kfrac b v r.+1) ^+ g.
Proof.
move=> r1 rv bv a0 hsmall hg.
have v0 : (0 < v)%N by apply: leq_ltn_trans rv.
set x := kfrac b v r; set q := kfrac b v r.+1.
have x0 : 0 <= x := kfrac_ge0 b v r.
have q0 : 0 <= q := kfrac_ge0 b v r.+1.
have xh : 2 * x <= 1.
  have xh' : x <= 2^-1.
    apply: le_trans (kfrac_le_half_pow bv (ltnW rv) v0) _.
    by rewrite -[X in _ <= X]expr1 ler_wiXn2l // ?invr_ge0 // invf_le1 // ler1n.
  apply: le_trans (_ : 2 * x <= 2 * 2^-1) _; first by apply: ler_wpM2l.
  by rewrite mulfV // pnatr_eq0.
have q1 : q <= 1.
  apply: le_trans (kfrac_le_half_pow bv rv v0) _.
  by rewrite exprn_ile1 // ?invr_ge0 // invf_le1 // ler1n.
have e0 : 0 <= a^-1 ^+ r by rewrite exprn_ge0 // invr_ge0 ltW.
have pq : (1 - q) ^+ g <= 1 by rewrite exprn_ile1 // ?subr_ge0 // lerBlDr lerDl.
have [xa|xa] := lerP x (a^-1 ^+ r).
  have h1 : x - a^-1 ^+ r <= 0 by rewrite subr_le0.
  have h2 : 0 <= 1 - (1 - q) ^+ g by rewrite subr_ge0.
  exact: le_trans h1 h2.
have rb : (r.+1 <= b)%N.
  rewrite ltnNge; apply/negP => br.
  have := kfrac_small r1 rv br; rewrite -/x => /le_trans /(_ hsmall) h.
  by move: xa; rewrite ltNge h.
have ab : a^-1 <= b%:R / (2 * v%:R).
  rewrite leNgt; apply/negP => ba.
  have h : (b%:R / (2 * v%:R)) ^+ r <= a^-1 ^+ r.
    apply: lerXn2r; rewrite ?nnegrE.
    - by rewrite divr_ge0 // mulr_ge0.
    - by rewrite invr_ge0 ltW.
    - exact: ltW.
  have := le_trans (kfrac_le_pow bv (ltnW rv) v0) h; rewrite -/x => hx.
  by move: xa; rewrite ltNge hx.
have a1 : 1 <= a * (b%:R / (2 * v%:R)).
  rewrite -[X in X <= _](mulfV (lt0r_neq0 a0)).
  by apply: ler_wpM2l; [exact: ltW | exact: ab].
have hq := kfrac_succ_lower rb rv; rewrite -/x -/q in hq.
have r0 : 0 < r.+1%:R :> R by rewrite ltr0n.
have hd : 2 * x <= g%:R * q.
  apply: le_trans (_ : 2 * r.+1%:R * a * (x * (b%:R / (2 * v%:R)) / r.+1%:R) <= _).
    have -> : 2 * r.+1%:R * a * (x * (b%:R / (2 * v%:R)) / r.+1%:R) =
        2 * x * (a * (b%:R / (2 * v%:R))) * (r.+1%:R / r.+1%:R) by ring.
    rewrite divff ?gt_eqF // mulr1.
    rewrite -[X in X <= _]mulr1; apply: ler_wpM2l => //.
    by apply: mulr_ge0; [exact: ler0n | exact: x0].
  have ha : 0 <= a := ltW a0.
  have hv : 0 <= 2 * v%:R :> R by apply: mulr_ge0; exact: ler0n.
  apply: ler_pM => //.
    by apply: mulr_ge0 => //; apply: mulr_ge0; exact: ler0n.
  apply: divr_ge0; last exact: ler0n.
  by apply: mulr_ge0 => //; apply: divr_ge0 => //; exact: ler0n.
apply: le_trans (block_ge_of_double x0 xh q0 q1 hd).
by rewrite lerBlDr lerDl.
Qed.

End kfrac.

(* Replacing a shorter clause by a block of g clauses: the probability that
   the block kills S is at least the probability that one clause of size r
   kills it, minus a^-r. *)
Lemma kill_replacement (R : realType) v r g (a : R)
    (S : {set {ffun 'I_v -> bool}}) :
  (1 <= r)%N -> (r < v)%N -> 0 < a -> (v.+1%:R)^-1 <= a^-1 ^+ r ->
  2 * r.+1%:R * a <= g%:R ->
  kill r S - a^-1 ^+ r <= 1 - survival r.+1 g S.
Proof.
move=> r1 rv a0 hsmall hg.
have e0 : 0 <= a^-1 ^+ r by rewrite exprn_ge0 // invr_ge0 ltW.
have C0 : (0 < #|{: clause v r}|)%N by rewrite card_clause_gt0 // ltnW.
have C1 : (0 < #|{: clause v r.+1}|)%N by rewrite card_clause_gt0.
have [->|S0] := eqVneq S set0.
  by rewrite (kill0 C0) survival0_set sub0r subr0 (le_trans _ ler01) // oppr_le0.
have bv : (#|forced S| <= v)%N by rewrite -[X in (_ <= X)%N]card_ord max_card.
rewrite killE_forced //.
apply: le_trans (replacement_numeric r1 rv bv a0 hsmall hg) _.
rewrite lerD2l lerN2 -killE_forced //.
exact: survival_le_geom.
Qed.

