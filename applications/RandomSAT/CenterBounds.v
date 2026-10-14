From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianAnalysis.matrix Require Import nets.
From GaussianAnalysis.random_matrix Require Import matrix_series.
From GaussianApplications.RandomSAT Require Import Model Pivotal Replacement.
From GaussianApplications.RandomSAT Require Import Survival Tails.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: bounds on the centers                                      *)
(*                                                                            *)
(* Part of target T9 of phase 13. A Rocq formalization of the credited        *)
(* argument of the lemma 'Bounds on the centers' (lem:center-bounds) of 'A    *)
(* Limiting Satisfiability Threshold for Every Fixed Clause Size' (family 235 *)
(* of the OpenAI math collection, revision 1581d4cbd,                         *)
(* source/sections/anchors.tex). The first moment and the comparisons of the  *)
(* centers with P_n follow the Lean development of the collection             *)
(* (lean/OAI/Probability/RandomSAT):                                          *)
(* Lean: first_moment_bound (CenterBounds.lean, line 69)                      *)
(* Lean: center_lower_by_probability (CenterBounds.lean, line 107)            *)
(* Lean: center_upper_by_probability (CenterBounds.lean, line 116)            *)
(* Lean: center_first_moment (CenterBounds.lean, line 181)                    *)
(* Lean: small_density_probability_bound (CenterBounds.lean, line 451)        *)
(* Lean: center_lower_explicit (CenterBounds.lean, line 475)                  *)
(*                                                                            *)
(* P_n(m) = sat_prob R n k m and mu_n = sat_center n k, as in Tails.v.        *)
(*                                                                            *)
(* - sat_prob_first_moment: P_n(m) <= 2^n (1 - 2^-k)^m, the mean number of    *)
(*   satisfying assignments; sat_prob_first_moment_linear: P_n(2^k n) <=      *)
(*   (2/e)^n.                                                                 *)
(* - sat_center_ge_prob (Markov's inequality): (m/n) P_n(m) <= mu_n;          *)
(*   sat_center_le_prob: mu_n <= m/n + 2^(k+1) P_n(m); both for k <= n and m  *)
(*   <= sat_cap k n.                                                          *)
(* - sat_center_first_moment: mu_n <= 2^k + 2^(k+1) (2/e)^n;                  *)
(*   sat_center_upper: mu_n <= 2^k + 1 once 2^(k+1) (2/e)^n <= 1.             *)
(* - sat_prob_small_density: P_n(m) >= 1 - k/n when 3 <= k <= n and 2 e^2 k m *)
(*   <= n.                                                                    *)
(* - sat_center_lower: mu_n >= sat_a0 k = 1 / (8 e^2 k) for 3 <= k <= n and n *)
(*   >= 4 e^2 k.                                                              *)
(*                                                                            *)
(* Departure: a minimal unsatisfiable core instead of Hall's theorem. The     *)
(* manuscript and the Lean development find a set of t clauses that uses      *)
(* fewer than t variables in an unsatisfiable formula, by Hall's theorem.     *)
(* Here unsat_core takes a minimal unsatisfiable set J of clause positions. A *)
(* variable of its support that occurs in one clause of J only could be set   *)
(* to satisfy that clause (the one-point update upd), so every variable of    *)
(* the support occurs at least twice and the support has at most k |J| / 2    *)
(* variables (core_support_card). The union bound runs over the pairs (J, W), *)
(* W a set of floor(k |J| / 2) variables that contains the support            *)
(* (set_enlarge, support_sub_le, core_sum_le). The density constant is 1 / (2 *)
(* e^2 k), against the manuscript's e^2 c_0 < 1 and the Lean development's    *)
(* e^(-2) / 4.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.


Section first_moment.
Context {R : realType}.

Lemma forced_set1 n (s : {ffun 'I_n -> bool}) : forced [set s] = [set: 'I_n].
Proof.
apply/setP => i; rewrite !inE; apply/andP; split.
  by apply/set0Pn; exists s; rewrite inE.
by apply/existsP; exists (s i); apply/forall_inP => s'; rewrite inE => /eqP ->.
Qed.

(* A fixed assignment satisfies a uniform clause with probability
   1 - 2^-k. *)
Lemma clause_sat_mean n k (s : {ffun 'I_n -> bool}) : (k <= n)%N ->
  unif_mean (fun c : clause n k => (clause_sat s c)%:R : R) = 1 - 2^-1 ^+ k.
Proof.
move=> kn; have C0 := card_clause_gt0 kn.
have S0 : [set s] != set0 by apply/set0Pn; exists s; rewrite inE.
have := killE_forced R k S0; rewrite forced_set1 cardsT card_ord.
rewrite /kill /kfrac unif_meanB unif_mean_cst // /alive S0 /=.
have Cn : 'C(n, k)%:R != 0 :> R by rewrite pnatr_eq0 -lt0n bin_gt0.
rewrite invfM mulrA mulfV // mul1r => h.
rewrite exprVn -h opprB addrC subrK; apply: eq_unif_mean => c.
case: (boolP (clause_sat s c)) => hc.
  have -> : add_clause [set s] c = [set s].
    by apply/setP => s'; rewrite !inE; case: eqP => // ->.
  by rewrite S0.
have -> : add_clause [set s] c = set0.
  by apply/setP => s'; rewrite !inE; case: eqP => // ->; rewrite (negbTE hc).
by rewrite eqxx.
Qed.

Lemma prod_indicator (T : Type) (s : seq T) (P : pred T) :
  \prod_(x <- s) (P x)%:R = (all P s)%:R :> R.
Proof.
elim: s => [|x s IH]; first by rewrite big_nil.
by rewrite big_cons IH /=; case: (P x); rewrite ?mul1r ?mul0r.
Qed.

(* The first moment: P_n(m) is at most the expected number of assignments
   that satisfy the m clauses. *)
Lemma sat_prob_first_moment n k m : (k <= n)%N ->
  sat_prob R n k m <= 2 ^+ n * (1 - 2^-1 ^+ k) ^+ m.
Proof.
move=> kn; rewrite /sat_prob sat_meanE /prefix_sat.
apply: le_trans (unif_mean_union R _) _.
have e s : unif_mean (fun t : m.-tuple (clause n k) =>
    [forall i : 'I_m, (i < m)%N ==> clause_sat s (tnth t i)]%:R : R) =
    (1 - 2^-1 ^+ k) ^+ m.
  rewrite -(clause_sat_mean s kn) -unif_mean_tuple_prod.
  apply: eq_unif_mean => t; rewrite prod_indicator.
  by rewrite -(all_take_tnth t (clause_sat s) m) take_oversize ?size_tuple.
under eq_bigr do rewrite e.
rewrite sumr_const card_ffun card_bool card_ord.
by rewrite -[(_ ^+ m) *+ _]mulr_natl natrX.
Qed.

(* At 2^k n clauses the first moment is at most (2/e)^n. *)
Lemma sat_prob_first_moment_linear n k : (k <= n)%N ->
  sat_prob R n k (2 ^ k * n) <= (2 / expR 1) ^+ n.
Proof.
move=> kn; apply: le_trans (sat_prob_first_moment _ kn) _.
have x0 : 0 <= 2^-1 ^+ k :> R by rewrite exprn_ge0 // invr_ge0 ler0n.
have q0 : 0 <= 1 - 2^-1 ^+ k :> R.
  by rewrite subr_ge0 exprn_ile1 // ?invr_ge0 ?ler0n // invf_le1 ?ler1n.
have hq : 1 - 2^-1 ^+ k <= expR (- 2^-1 ^+ k) :> R.
  by have := expR_ge1Dx (- 2^-1 ^+ k : R); rewrite addrC.
have e : - 2^-1 ^+ k * (2 ^ k * n)%:R = -1 * n%:R :> R.
  rewrite natrM natrX mulrA !mulNr -exprMn mulVf ?pnatr_eq0 //.
  by rewrite expr1n !mul1r.
have h : (1 - 2^-1 ^+ k) ^+ (2 ^ k * n) <= expR (- 1) ^+ n :> R.
  apply: le_trans (lerXn2r _ _ _ hq) _; rewrite ?nnegrE ?expR_ge0 //.
  by rewrite -[expR (- 2^-1 ^+ k) ^+ _]expRM_natr e expRM_natr.
rewrite exprMn; apply: ler_wpM2l; first by rewrite exprn_ge0 ?ler0n.
by rewrite expRN in h.
Qed.

End first_moment.


Section centers.
Context {R : realType}.

(* Markov's inequality: m P_n(m) <= E V. *)
Lemma sat_center_ge_prob n k m : (k <= n)%N -> (m <= sat_cap k n)%N ->
  m%:R / n%:R * sat_prob R n k m <= sat_center n k.
Proof.
move=> kn mM; rewrite (sat_prob_tail kn mM) /sat_center mulrAC.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
rewrite !sat_meanE.
have h := @unif_mean_markov R _ (fun t : (sat_cap k n).-tuple (clause n k) =>
  (sat_prefix_len t)%:R : R) (m%:R) (fun t => ler0n _ _).
apply: le_trans h; apply: ler_wpM2l; first exact: ler0n.
by apply: ler_unif_mean => t; rewrite [(m%:R <= _)%R]ler_nat.
Qed.

(* The bound by a cutoff: E V <= m + cap P(V >= m). *)
Lemma sat_center_le_prob n k m : (k <= n)%N -> (m <= sat_cap k n)%N ->
  sat_center n k <= m%:R / n%:R + 2 ^+ k.+1 * sat_prob R n k m.
Proof.
move=> kn mM; have [->|n0] := posnP n.
  by rewrite /sat_center !invr0 !mulr0 add0r mulr_ge0 ?exprn_ge0 ?sat_prob_ge0.
rewrite (sat_prob_tail kn mM) /sat_center ler_pdivrMr ?ltr0n //.
rewrite mulrDl divfK ?pnatr_eq0 -?lt0n // mulrAC.
have -> : 2 ^+ k.+1 * n%:R = (sat_cap k n)%:R :> R.
  by rewrite /sat_cap natrM natrX.
have hM (t : (sat_cap k n).-tuple (clause n k)) :
    (sat_prefix_len t)%:R <= (sat_cap k n)%:R :> R.
  by rewrite ler_nat sat_prefix_len_le.
rewrite !sat_meanE; apply: le_trans (unif_mean_cutoff (ler0n _ m) hM) _.
rewrite lerD2l; apply: ler_wpM2l; first exact: ler0n.
by apply: ler_unif_mean => t; rewrite [(m%:R <= _)%R]ler_nat.
Qed.

(* The upper bound of the centers from the first moment. *)
Lemma sat_center_first_moment n k : (k <= n)%N -> (0 < n)%N ->
  sat_center n k <= 2 ^+ k + 2 ^+ k.+1 * (2 / expR 1) ^+ n :> R.
Proof.
move=> kn n0; have mM : (2 ^ k * n <= sat_cap k n)%N.
  by rewrite /sat_cap leq_mul2r expnS leq_pmull // orbT.
apply: le_trans (sat_center_le_prob kn mM) _.
rewrite natrM natrX mulfK ?pnatr_eq0 -?lt0n // lerD2l.
apply: ler_wpM2l; first by rewrite exprn_ge0.
exact: sat_prob_first_moment_linear.
Qed.

End centers.


Section assignments.
Context {R : realType}.

(* A uniform assignment takes prescribed values on a set P of variables
   with probability 2^-|P|. *)
Lemma unif_mean_asg_fix n (P : {set 'I_n}) (v : 'I_n -> bool) :
  unif_mean (fun s : {ffun 'I_n -> bool} =>
    [forall i in P, s i == v i]%:R : R) = 2^-1 ^+ #|P|.
Proof.
pose F (i : 'I_n) (b : bool) : R := if i \in P then (b == v i)%:R else 1.
have e (s : {ffun 'I_n -> bool}) :
    [forall i in P, s i == v i]%:R = \prod_i F i (s i) :> R.
  rewrite /F; case: (boolP [forall i in P, s i == v i]) =>
    [/forall_inP h|/forall_inPn [i iP /negbTE si]].
    by rewrite big1 // => i _; case: ifP => // /h ->.
  by rewrite (bigD1 i) //= iP si mul0r.
rewrite /unif_mean (eq_bigr _ (fun s _ => e s)) -bigA_distr_bigA.
rewrite card_ffun card_bool card_ord natrX -exprVn.
have -> : 2^-1 ^+ n = \prod_(i < n) (2^-1 : R) by rewrite prodr_const card_ord.
rewrite -big_split /=.
transitivity (\prod_(i < n) (if i \in P then 2^-1 else 1 : R)).
  apply: eq_bigr => i _; rewrite big_bool /F; case: ifP => _.
    by case: (v i); rewrite /= ?addr0 ?add0r mulr1.
  by rewrite mulVf ?pnatr_eq0.
by rewrite -big_mkcond prodr_const.
Qed.

End assignments.

Section supports.
Context {R : realType} (n k : nat).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C := (clause n k).

(* The assignments that agree with tau on W. *)
Definition agree_on (W : {set 'I_n}) (tau : asg) : {set asg} :=
  [set s : asg | [forall i in W, s i == tau i]].

Lemma agree_on_self W tau : tau \in agree_on W tau.
Proof. by rewrite inE; apply/forall_inP. Qed.

Lemma forced_agree W tau : forced (agree_on W tau) = W.
Proof.
rewrite (forced_frozen (agree_on_self W tau)); apply/setP => i; rewrite inE.
apply/forall_inP/idP => [h|iW s]; last by rewrite inE => /forall_inP /(_ i iW).
apply/negPn/negP => iW.
pose s := [ffun j => if j == i then ~~ tau i else tau j].
have sA : s \in agree_on W tau.
  rewrite inE; apply/forall_inP => j jW; rewrite ffunE.
  case: (eqVneq j i) => [ji|_]; last by [].
  by move: jW; rewrite ji (negbTE iW).
by have := h s sA; rewrite ffunE eqxx; case: (tau i).
Qed.

Lemma kills_agree W tau (c : C) :
  (add_clause (agree_on W tau) c == set0) =
  (support c \subset W) &&
    [forall i in support c, tau i == ~~ odflt false (val c i)].
Proof.
have tA := agree_on_self W tau.
have fr : frozen (agree_on W tau) tau = W.
  by rewrite -(forced_frozen tA) forced_agree.
apply/eqP/andP => [h|[sW /forall_inP hs]].
  have hk := kills_frozen tA h; split.
    apply/subsetP => i; rewrite inE => ci.
    by have [] := hk i ci; rewrite fr.
  apply/forall_inP => i; rewrite inE => ci.
  have [_ ->] := hk i ci; by rewrite /= negbK.
apply: (frozen_kills tA) => i ci; rewrite fr; split.
  by apply: (subsetP sW); rewrite inE.
have := hs i; rewrite inE => /(_ ci) /eqP ->.
by case: (val c i) ci => // b _; rewrite /= negbK.
Qed.

(* The variables of a uniform clause lie in W with probability
   C(|W|, k) / C(n, k). *)
Lemma support_sub_mean (W : {set 'I_n}) : (k <= n)%N ->
  unif_mean (fun c : C => (support c \subset W)%:R : R) =
  'C(#|W|, k)%:R / 'C(n, k)%:R.
Proof.
move=> kn; have C0 := card_clause_gt0 kn.
have A0 : (0 < #|{: asg}|)%N by rewrite card_ffun card_bool expn_gt0.
have S0 tau : agree_on W tau != set0.
  by apply/set0Pn; exists tau; exact: agree_on_self.
have hk tau : kill (R := R) k (agree_on W tau) = kfrac #|W| n k.
  by rewrite killE_forced ?forced_agree.
have hk' tau : kill (R := R) k (agree_on W tau) =
    unif_mean (fun c : C => (add_clause (agree_on W tau) c == set0)%:R : R).
  rewrite /kill; apply: eq_unif_mean => c; rewrite /alive S0.
  by case: (add_clause (agree_on W tau) c == set0); rewrite /= ?subr0 ?subrr.
have hmean : unif_mean (fun tau : asg => unif_mean (fun c : C =>
    (add_clause (agree_on W tau) c == set0)%:R : R)) = kfrac #|W| n k.
  rewrite -[RHS](unif_mean_cst (kfrac #|W| n k) A0).
  by apply: eq_unif_mean => tau; rewrite -hk' hk.
rewrite unif_mean_comm in hmean.
have hc (c : C) : unif_mean (fun tau : asg =>
    (add_clause (agree_on W tau) c == set0)%:R : R) =
    (support c \subset W)%:R * 2^-1 ^+ k.
  under eq_unif_mean => tau do rewrite kills_agree.
  case: (support c \subset W) => /=;
    last by rewrite mul0r /unif_mean big1 ?mulr0.
  rewrite mul1r (unif_mean_asg_fix (support c)
    (fun i => ~~ odflt false (sval c i))).
  by rewrite card_support_clause.
rewrite (eq_unif_mean hc) unif_meanZr /kfrac in hmean.
have t1 : (2^-1 ^+ k : R) != 0 by rewrite expf_neq0 // invr_eq0 pnatr_eq0.
by apply: (mulIf t1); rewrite hmean invfM mulrA exprVn.
Qed.

Lemma support_sub_le (W : {set 'I_n}) : (k <= n)%N -> (0 < n)%N ->
  unif_mean (fun c : C => (support c \subset W)%:R : R) <=
  (#|W|%:R / n%:R) ^+ k.
Proof.
move=> kn n0; rewrite support_sub_mean //.
have Wn : (#|W| <= n)%N by rewrite -[n in (_ <= n)%N]card_ord max_card.
have := kfrac_le_pow (R := R) Wn kn n0; rewrite /kfrac => h.
have t0 : (2 ^+ k : R) != 0 by rewrite expf_neq0 // pnatr_eq0.
have b0 : ('C(n, k)%:R : R) != 0 by rewrite pnatr_eq0 -lt0n bin_gt0.
have n0' : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have e1 : 'C(#|W|, k)%:R / 'C(n, k)%:R =
    2 ^+ k * ('C(#|W|, k)%:R / ('C(n, k)%:R * 2 ^+ k)) :> R by field.
have e2 : (#|W|%:R / n%:R) ^+ k =
    2 ^+ k * (#|W|%:R / (2 * n%:R)) ^+ k :> R.
  by rewrite -exprMn; congr (_ ^+ k); field.
by rewrite e1 e2 ler_wpM2l ?exprn_ge0.
Qed.

End supports.

(* A set of size at most s <= #|T| lies in a set of size exactly s. *)
Lemma set_enlarge (T : finType) (U : {set T}) s :
  (#|U| <= s)%N -> (s <= #|T|)%N -> exists2 W : {set T}, U \subset W & #|W| = s.
Proof.
elim: s => [|s IH] Us sT.
  by exists U => //; apply/eqP; rewrite -leqn0.
case: (ltngtP #|U| s.+1) Us => // [Us _|Us _]; last by exists U.
have [W0 UW0 W0s] := IH Us (ltnW sT).
have : ~~ ([set: T] \subset W0).
  rewrite subTset; apply/negP => /eqP W0T; move: sT.
  by rewrite -W0s W0T cardsT ltnn.
case/subsetPn => x _ xW0; exists (x |: W0).
  by apply: subset_trans UW0 _; exact: subsetU1.
by rewrite cardsU1 xW0 W0s.
Qed.

Section core.
Variables (n k M : nat) (t : M.-tuple (clause n k)).
Local Notation asg := {ffun 'I_n -> bool}.

(* The clauses of t at the positions J have a common solution. *)
Definition sat_on (J : {set 'I_M}) : bool :=
  [exists s : asg, [forall i in J, clause_sat s (tnth t i)]].

Lemma sat_onT : sat_on [set: 'I_M] = prefix_sat t M.
Proof.
rewrite /sat_on /prefix_sat; apply: eq_existsb => s.
by apply: eq_forallb => i; rewrite inE ltn_ord.
Qed.

(* The assignment s with the value b at x. *)
Definition upd (s : asg) (x : 'I_n) (b : bool) : asg :=
  [ffun y => if y == x then b else s y].

Lemma clause_sat_upd (s : asg) x b (c : clause n k) :
  x \notin support c -> clause_sat (upd s x b) c = clause_sat s c.
Proof.
rewrite inE negbK => /eqP cx; apply: eq_existsb => i; rewrite ffunE.
by case: (eqVneq i x) => // ->; rewrite cx.
Qed.

Lemma clause_sat_lit (s : asg) x b (c : clause n k) :
  val c x = Some b -> clause_sat (upd s x b) c.
Proof. by move=> cx; apply/existsP; exists x; rewrite ffunE eqxx cx. Qed.

(* No clause, or one clause, is satisfiable. *)
Lemma sat_on_small (J : {set 'I_M}) : (0 < k)%N -> (#|J| <= 1)%N -> sat_on J.
Proof.
move=> k0 J1; case: (set_0Vmem J) => [->|[j jJ]].
  by apply/existsP; exists [ffun=> true]; apply/forall_inP => i; rewrite inE.
have Jj : [set j] = J by apply/eqP; rewrite eqEcard sub1set jJ cards1.
have [x xc] : exists x, x \in support (tnth t j).
  by apply/set0Pn; rewrite -card_gt0 card_support_clause.
case cx: (val (tnth t j) x) => [b|]; last by rewrite inE cx in xc.
apply/existsP; exists (upd [ffun=> true] x b); apply/forall_inP => i.
by rewrite -Jj inE => /eqP ->; exact: clause_sat_lit.
Qed.

(* A minimal unsatisfiable set of clauses: every variable of one of its
   clauses occurs in another of its clauses. *)
Lemma unsat_core : (0 < k)%N -> ~~ prefix_sat t M ->
  exists J : {set 'I_M}, [/\ ~~ sat_on J, (2 <= #|J|)%N &
    forall j x, j \in J -> x \in support (tnth t j) ->
      exists2 j', j' \in J & (j' != j) && (x \in support (tnth t j'))].
Proof.
move=> k0 unsat; have PT : ~~ sat_on [set: 'I_M] by rewrite sat_onT.
case: (@arg_minnP _ _ (fun J => ~~ sat_on J) (fun J => #|J|) PT).
move=> J PJ Jmin; exists J; split => //.
  by rewrite ltnNge; apply/negP => J1; move: PJ; rewrite sat_on_small.
move=> j x jJ xj.
case: (boolP [exists j' in J, (j' != j) && (x \in support (tnth t j'))]).
  by case/exists_inP => j' j'J hj'; exists j'.
move=> none; exfalso; move/negP: PJ; apply.
have : sat_on (J :\ j).
  case: (boolP (sat_on (J :\ j))) => // h.
  by have := Jmin _ h; rewrite (cardsD1 j J) jJ ltnn.
case/existsP => s /forall_inP hs.
case cx: (val (tnth t j) x) => [b|]; last by rewrite inE cx in xj.
apply/existsP; exists (upd s x b); apply/forall_inP => i iJ.
case: (eqVneq i j) => [->|ij]; first exact: clause_sat_lit.
have xi : x \notin support (tnth t i).
  apply/negP => xi; move/negP: none; apply; apply/exists_inP.
  by exists i => //; rewrite ij xi.
by rewrite clause_sat_upd //; apply: hs; rewrite !inE ij iJ.
Qed.

(* Hence the clauses of the core have at most k |J| / 2 variables. *)
Lemma core_support_card (J : {set 'I_M}) :
  (forall j x, j \in J -> x \in support (tnth t j) ->
     exists2 j', j' \in J & (j' != j) && (x \in support (tnth t j'))) ->
  (2 * #|\bigcup_(j in J) support (tnth t j)| <= k * #|J|)%N.
Proof.
move=> h; set U := \bigcup_(j in J) _.
have hU j x : j \in J -> x \in support (tnth t j) -> x \in U.
  by move=> jJ xj; apply/bigcupP; exists j.
have -> : (k * #|J| =
    \sum_(j in J) \sum_(x in support (tnth t j)) 1)%N.
  rewrite -[LHS]mulnC -sum_nat_const; apply: eq_bigr => j _.
  by rewrite sum1_card card_support_clause.
rewrite (exchange_big_dep (mem U) hU) /= mulnC -sum_nat_const.
apply: leq_sum => x /bigcupP [j jJ xj].
have [j' j'J /andP [j'j xj']] := h j x jJ xj.
rewrite sum1dep_card; apply: (@leq_trans #|[set j'; j]|).
  by rewrite cards2 j'j.
apply: subset_leq_card; apply/subsetP => i; rewrite !inE.
case/orP => /eqP ->; first by rewrite j'J; rewrite inE in xj'.
by rewrite jJ; rewrite inE in xj.
Qed.

End core.


Section union_arith.
Context {R : realType}.

(* floor(k t / 2) >= t + 1 for k >= 3 and t >= 2. *)
Lemma half_kt_ge k t : (3 <= k)%N -> (2 <= t)%N -> (t.+1 <= (k * t) %/ 2)%N.
Proof.
move=> k3 t2; rewrite leq_divRL //.
apply: (@leq_trans (3 * t)); last by rewrite leq_mul2r k3 orbT.
by rewrite mulSn (mulSn 2 t) mulnC leq_add2r.
Qed.

Lemma expR1_ge2 : 2 <= expR 1 :> R.
Proof. by have := expR_ge1Dx (1 : R). Qed.

(* A term of the union bound over minimal unsatisfiable cores. *)
Lemma core_summand_le (n k m t : nat) : (3 <= k)%N -> (2 <= t)%N ->
  (t <= m)%N -> 2 * expR 2 * k%:R * m%:R <= n%:R :> R ->
  'C(m, t)%:R * 'C(n, (k * t) %/ 2)%:R *
    (((k * t) %/ 2)%:R / n%:R) ^+ (k * t)
  <= 4^-1 ^+ t * (expR 1 * k%:R * t%:R / (2 * n%:R)) :> R.
Proof.
move=> k3 t2 tm hd; set s := ((k * t) %/ 2)%N.
have st : (t.+1 <= s)%N := half_kt_ge k3 t2.
have s2 : (s * 2 <= k * t)%N := leq_divM (k * t) 2.
set e : R := expR 1; have e2 : 2 <= e := expR1_ge2.
have ee : expR 2 = e ^+ 2 :> R by rewrite -expRM_natl mulr1.
rewrite ee in hd.
have t0 : (0 < t%:R :> R) by rewrite ltr0n (leq_trans _ t2).
have k0 : (0 < k%:R :> R) by rewrite ltr0n (leq_trans _ k3).
have s0 : (0 < s%:R :> R) by rewrite ltr0n (leq_trans _ st).
have hm : (t%:R <= m%:R :> R) by rewrite ler_nat.
have e0 : 0 < e by apply: lt_le_trans e2.
have n0 : (0 < n%:R :> R).
  apply: lt_le_trans hd; rewrite !mulr_gt0 ?exprn_gt0 //.
  exact: lt_le_trans t0 hm.
have tn : (t%:R : R) != 0 by rewrite gt_eqF.
have nn : (n%:R : R) != 0 by rewrite gt_eqF.
have sn0 : (s%:R : R) != 0 by rewrite gt_eqF.
have hs2 : 2 * s%:R <= k%:R * t%:R :> R.
  by rewrite -natrM mulnC -natrM ler_nat.
set a := e * m%:R / t%:R; set y := e * s%:R / n%:R.
set z := e * k%:R * t%:R / (2 * n%:R).
have a0 : 0 <= a by rewrite /a divr_ge0 ?mulr_ge0 ?ler0n // ltW.
have z0 : 0 <= z by rewrite /z divr_ge0 ?mulr_ge0 ?ler0n ?ltW.
have y0 : 0 <= y by rewrite /y divr_ge0 ?mulr_ge0 ?ler0n ?ltW.
have az4 : a * z <= 4^-1.
  have -> : a * z = e ^+ 2 * k%:R * m%:R / (2 * n%:R) by rewrite /a /z; field.
  by rewrite ler_pdivrMr ?mulr_gt0 //; move: hd; lra.
have a1 : 1 <= a.
  rewrite /a ler_pdivlMr // mul1r; apply: le_trans hm _.
  by rewrite -[X in X <= _]mul1r ler_wpM2r ?ler0n //; lra.
have z4 : z <= 4^-1.
  by apply: le_trans az4; rewrite -[X in X <= _]mul1r ler_wpM2r.
have yz : y <= z.
  have hzy : z - y = e * (k%:R * t%:R - 2 * s%:R) / (2 * n%:R).
    by rewrite /y /z; field.
  rewrite -subr_ge0 hzy; apply: divr_ge0; last by rewrite mulr_ge0 ?ler0n.
  by rewrite mulr_ge0 ?subr_ge0 // ltW.
have y1 : y <= 1.
  by apply: le_trans yz _; apply: le_trans z4 _; rewrite invf_le1 ?ler1n ?ltr0n.
set x := s%:R / n%:R.
have x0 : 0 <= x by rewrite /x divr_ge0 ?ler0n.
have xy : x <= y by rewrite /y /x -mulrA ler_peMl // (le_trans _ e2) ?ler1n.
have x1 : x <= 1 := le_trans xy y1.
have hC2 : 'C(n, s)%:R * x ^+ (k * t) <= y ^+ s.
  apply: le_trans (ler_pM (ler0n _ _) (exprn_ge0 _ x0) (bin_le_expR R n s)
    (ler_wiXn2l x0 x1 s2)) _.
  have ey : expR 1 * n%:R / s%:R * x ^+ 2 = y by rewrite /x /y /e; field.
  by rewrite mulnC exprM -exprMn ey.
rewrite -mulrA; apply: le_trans (ler_pM (ler0n _ _)
  (mulr_ge0 (ler0n _ _) (exprn_ge0 _ x0)) (bin_le_expR R m t) hC2) _.
have hys : y ^+ s <= y ^+ t.+1 := ler_wiXn2l y0 y1 st.
have hyz : y ^+ t.+1 <= z ^+ t.+1 by rewrite lerXn2r ?nnegrE.
apply: le_trans (ler_wpM2l (exprn_ge0 _ a0) (le_trans hys hyz)) _.
rewrite exprSr mulrA -exprMn; apply: ler_wpM2r => //.
by apply: lerXn2r => //; rewrite nnegrE; [exact: mulr_ge0 | rewrite invr_ge0].
Qed.

(* The tail of the geometric series of ratio 1/2 from 2. *)
Lemma geom_half_tail m : \sum_(2 <= t < m.+1) (2^-1 : R) ^+ t <= 2^-1.
Proof.
case: m => [|m]; first by rewrite big_geq // invr_ge0 ler0n.
suff -> : \sum_(2 <= t < m.+2) (2^-1 : R) ^+ t = 2^-1 - 2^-1 ^+ m.+1.
  by rewrite lerBlDr lerDl exprn_ge0 // invr_ge0.
elim: m => [|m IH]; first by rewrite big_geq // expr1 subrr.
rewrite big_nat_recr //= IH [2^-1 ^+ m.+2]exprS.
have h2 : (2 : R) != 0 by rewrite pnatr_eq0.
by rewrite exprS; field.
Qed.

(* The sum of the terms of the union bound over the sizes t >= 2. *)
Lemma core_sum_le (n k m : nat) : (0 < n)%N ->
  \sum_(2 <= t < m.+1)
     4^-1 ^+ t * (expR 1 * k%:R * t%:R / (2 * n%:R))
  <= k%:R / n%:R :> R.
Proof.
move=> n0; have n0' : (0 < n%:R :> R) by rewrite ltr0n.
have nn : (n%:R : R) != 0 by rewrite gt_eqF.
set c : R := expR 1 * k%:R / (2 * n%:R).
have c0 : 0 <= c by rewrite /c divr_ge0 ?mulr_ge0 ?expR_ge0 ?ler0n.
apply: (@le_trans _ _ (\sum_(2 <= t < m.+1) c * 2^-1 ^+ t)).
  apply: ler_sum => t _.
  have e4 : (4 : R)^-1 = 2^-1 * 2^-1.
    by rewrite -invfM; congr (_^-1); rewrite -natrM.
  have -> : 4^-1 ^+ t * (expR 1 * k%:R * t%:R / (2 * n%:R)) =
      c * (2^-1 ^+ t * (2^-1 ^+ t * t%:R)) :> R.
    by rewrite e4 /c exprMn; field.
  apply: ler_wpM2l => //; rewrite -[X in _ <= X]mulr1.
  apply: ler_wpM2l; first by rewrite exprn_ge0 // invr_ge0.
  rewrite exprVn mulrC ler_pdivrMr ?exprn_gt0 // mul1r -natrX ler_nat.
  exact: ltnW (ltn_expl _ _).
rewrite -mulr_sumr; apply: le_trans (ler_wpM2l c0 (geom_half_tail m)) _.
have e4 := expR1_le4 (R := R).
have -> : c / 2 = (expR 1 / 4) * (k%:R / n%:R) by rewrite /c; field.
rewrite -[X in _ <= X]mul1r ler_wpM2r ?divr_ge0 ?ler0n //.
by rewrite ler_pdivrMr ?mul1r.
Qed.

End union_arith.

Section small_density.
Context {R : realType}.

(* A sum over the subsets of T of a function of their size. *)
Lemma sum_set_card (T : finType) (F : nat -> R) :
  \sum_(A : {set T}) F #|A| = \sum_(t < #|T|.+1) 'C(#|T|, t)%:R * F t.
Proof.
rewrite (partition_big (fun A : {set T} => (inord #|A| : 'I_#|T|.+1)) xpredT)
  //=.
apply: eq_bigr => t _.
have e (A : {set T}) : (inord #|A| == t :> 'I_#|T|.+1) = (#|A| == t).
  by rewrite -val_eqE /= inordK // ltnS max_card.
under eq_bigl => A do rewrite e.
rewrite (eq_bigr (fun=> F t)); first by move=> A /eqP ->.
by rewrite sumr_const -card_draws cardsE mulr_natl.
Qed.

(* At density m / n <= 1 / (2 e^2 k), m uniform clauses are satisfiable
   with probability at least 1 - k / n: an unsatisfiable formula has a
   minimal unsatisfiable core, whose variables occur twice. *)
Lemma sat_prob_small_density n k m : (3 <= k)%N -> (k <= n)%N ->
  2 * expR 2 * k%:R * m%:R <= n%:R :> R ->
  1 - k%:R / n%:R <= sat_prob R n k m.
Proof.
move=> k3 kn hd; have k0 : (0 < k)%N by apply: leq_trans k3.
have n0 : (0 < n)%N := leq_trans k0 kn.
have C0 := card_clause_gt0 kn.
have T0 : (0 < #|{: m.-tuple (clause n k)}|)%N.
  by rewrite card_tuple expn_gt0 C0.
rewrite lerBlDr -lerBlDl.
have -> : 1 - sat_prob R n k m =
    unif_mean (fun t : m.-tuple (clause n k) => (~~ prefix_sat t m)%:R : R).
  by rewrite /sat_prob sat_meanE (unif_mean_indicatorN R
    (fun t : m.-tuple (clause n k) => prefix_sat t m) T0).
have e1 : (1 <= expR 2 :> R).
  by apply: le_trans (expR_ge1Dx _); rewrite lerDl ler0n.
have km : (k * m <= n)%N.
  rewrite -(ler_nat R) natrM; apply: le_trans hd.
  have h2 : (1 : R) <= 2 * expR 2.
    apply: le_trans (e1 : 1 <= expR 2) _.
    by rewrite ler_peMl ?ler1n ?expR_ge0.
  rewrite -[X in X <= _]mul1r -!mulrA mulrA [X in _ <= X]mulrA -mulrA.
  by apply: ler_wpM2r => //; rewrite mulr_ge0 ?ler0n.
(* An unsatisfiable formula has a core J of at least two clauses, whose
   variables lie in a set W of floor(k |J| / 2) variables. *)
pose Q (p : {set 'I_m} * {set 'I_n}) (t : m.-tuple (clause n k)) :=
  [&& (2 <= #|p.1|)%N, #|p.2| == ((k * #|p.1|) %/ 2)%N &
      [forall i in p.1, support (tnth t i) \subset p.2]].
have hcore t : ~~ prefix_sat t m -> [exists p, Q p t].
  move=> unsat; have [J [hJ J2 hJx]] := unsat_core k0 unsat.
  set U := \bigcup_(j in J) support (tnth t j).
  have hU := core_support_card hJx.
  have Us : (#|U| <= (k * #|J|) %/ 2)%N by rewrite leq_divRL // mulnC.
  have Jm : (#|J| <= m)%N by rewrite -[m in (_ <= m)%N]card_ord max_card.
  have sn : ((k * #|J|) %/ 2 <= #|'I_n|)%N.
    rewrite card_ord; apply: leq_trans (leq_div _ _) _.
    by apply: leq_trans km; rewrite leq_mul2l Jm orbT.
  have [W UW Ws] := set_enlarge Us sn.
  apply/existsP; exists (J, W); rewrite /Q /= J2 Ws eqxx /=.
  apply/forall_inP => i iJ; apply: subset_trans UW.
  by apply/subsetP => x xi; apply/bigcupP; exists i.
apply: (@le_trans _ _ (unif_mean (fun t : m.-tuple (clause n k) =>
  [exists p, Q p t]%:R : R))).
  apply: ler_unif_mean => t; case: (boolP (prefix_sat t m)) => h /=.
    exact: ler0n.
  by rewrite (hcore t h).
apply: le_trans (unif_mean_union R Q) _.
(* The union bound over the pairs (J, W). *)
pose G (p : {set 'I_m} * {set 'I_n}) : R :=
  ((2 <= #|p.1|)%N && (#|p.2| == ((k * #|p.1|) %/ 2)%N))%:R *
  ((#|p.2|%:R / n%:R) ^+ k) ^+ #|p.1|.
apply: (@le_trans _ _ (\sum_p G p)).
  apply: ler_sum => p _; rewrite /G /Q.
  case: (boolP ((2 <= #|p.1|)%N && (#|p.2| == ((k * #|p.1|) %/ 2)%N))).
    case/andP => -> /eqP Ws /=; rewrite Ws eqxx /= mul1r.
    have e (t : m.-tuple (clause n k)) :
        [forall i in p.1, support (tnth t i) \subset p.2]%:R =
        \prod_(i in p.1) (support (tnth t i) \subset p.2)%:R :> R.
      case: (boolP [forall i in p.1, support (tnth t i) \subset p.2]) =>
        [/forall_inP h|/forall_inPn [i iJ /negbTE hi]].
        by rewrite big1 // => i /h ->.
      by rewrite (bigD1 i) //= hi mul0r.
    rewrite (eq_unif_mean e).
    have -> := @unif_mean_tuple_prod_set R (clause n k) m p.1
      (fun c : clause n k => (support c \subset p.2)%:R) C0.
    apply: lerXn2r; rewrite ?nnegrE ?exprn_ge0 ?divr_ge0 ?ler0n //.
      by apply: unif_mean_ge0 => c; exact: ler0n.
    by rewrite -Ws; exact: support_sub_le.
  move=> hp; rewrite mul0r /unif_mean big1 ?mulr0 // => t _.
  by move: hp; case: (1 < #|p.1|)%N; case: (#|p.2| == _).
have -> : \sum_p G p = \sum_(J : {set 'I_m}) \sum_(W : {set 'I_n}) G (J, W).
  by rewrite pair_bigA; apply: eq_bigr => -[J W].
pose H (t : nat) : R := (2 <= t)%N%:R * 'C(n, (k * t) %/ 2)%:R *
  ((((k * t) %/ 2)%:R / n%:R) ^+ k) ^+ t.
have hW (J : {set 'I_m}) : \sum_(W : {set 'I_n}) G (J, W) = H #|J|.
  rewrite /G /H /=; set s := ((k * #|J|) %/ 2)%N.
  set c : R := ((s%:R / n%:R) ^+ k) ^+ #|J|.
  transitivity (\sum_(W : {set 'I_n}) (1 < #|J|)%N%:R * ((#|W| == s)%:R * c)
      : R).
    apply: eq_bigr => W _; rewrite /c.
    by case: (eqVneq #|W| s) => [->|hW];
      rewrite /= ?andbT ?andbF ?mul0r ?mulr0 ?mul1r ?mulr1 ?natrM.
  rewrite -mulr_sumr -mulr_suml mulrA; congr (_ * _ * _).
  rewrite -natr_sum; congr (_%:R).
  rewrite -[n in 'C(n, s)]card_ord -card_draws -sum1_card big_mkcond /=.
  rewrite [RHS]big_mkcond; apply: eq_bigr => W _.
  by rewrite inE; case: (#|W| == s).
under eq_bigr do rewrite hW.
rewrite sum_set_card card_ord; apply: le_trans (core_sum_le k m n0).
rewrite big_geq_mkord [X in _ <= X]big_mkcond /=.
apply: ler_sum => t _; rewrite /H; case: (leqP 2 t) => t2 /=.
  rewrite mul1r mulrA -exprM.
  exact: (core_summand_le k3 t2 (ltnSE (ltn_ord t)) hd).
by rewrite !mul0r mulr0.
Qed.

End small_density.

Section center_bounds.
Context {R : realType}.

(* The positive lower bound a0 = 1 / (8 e^2 k) of the centers. *)
Definition sat_a0 (k : nat) : R := (8 * expR 2 * k%:R)^-1.

Lemma sat_a0_gt0 k : (0 < k)%N -> 0 < sat_a0 k.
Proof. by move=> k0; rewrite invr_gt0 !mulr_gt0 ?expR_gt0 ?ltr0n. Qed.

(* For n >= 4 e^2 k, the center is at least a0: at the density
   m / n = floor(n / (2 e^2 k)) / n, which is at least 1 / (4 e^2 k), the
   formula is satisfiable with probability at least 1/2. *)
Lemma sat_center_lower n k : (3 <= k)%N -> (k <= n)%N ->
  4 * expR 2 * k%:R <= n%:R :> R -> sat_a0 k <= sat_center n k :> R.
Proof.
move=> k3 kn hn; have k0 : (0 < k)%N by apply: leq_trans k3.
have n0 : (0 < n)%N := leq_trans k0 kn.
have n0' : 0 < n%:R :> R by rewrite ltr0n.
have k0' : 0 <= k%:R :> R by exact: ler0n.
have e1 : (1 <= expR 2 :> R).
  by apply: le_trans (expR_ge1Dx _); rewrite lerDl ler0n.
set c0 : R := (2 * expR 2 * k%:R)^-1.
have pos : 0 < 2 * expR 2 * k%:R :> R by rewrite !mulr_gt0 ?expR_gt0 ?ltr0n.
have c0p : 0 < c0 by rewrite invr_gt0.
set m := Num.truncn (c0 * n%:R).
have cn0 : 0 <= c0 * n%:R by rewrite mulr_ge0 ?ler0n // ltW.
have hm : m%:R <= c0 * n%:R by rewrite truncn_le.
have hm' : c0 * n%:R < m.+1%:R := truncnS_gt _.
have hd : 2 * expR 2 * k%:R * m%:R <= n%:R :> R.
  apply: le_trans (ler_wpM2l (ltW pos) hm) _.
  by rewrite /c0 mulrA mulfV ?gt_eqF // mul1r.
have hP := sat_prob_small_density k3 kn hd.
have nk : 2 * k%:R <= n%:R :> R by nra.
have kn2 : k%:R / n%:R <= 2^-1 :> R by rewrite ler_pdivrMr //; move: nk; lra.
have c1 : c0 <= 1.
  rewrite invf_le1 //; apply: le_trans (_ : 2 <= _); first by rewrite ler1n.
  by rewrite -mulrA ler_peMr ?ler0n // -[X in X <= _]mul1r ler_pM ?ler01 ?ler1n.
have mn : (m <= n)%N.
  rewrite -(ler_nat R); apply: le_trans hm _.
  by rewrite -[X in _ <= X]mul1r ler_wpM2r ?ler0n.
have mM : (m <= sat_cap k n)%N.
  by apply: leq_trans mn _; rewrite /sat_cap leq_pmull ?expn_gt0.
have cn2 : 2 <= c0 * n%:R.
  by rewrite /c0 mulrC ler_pdivlMr //; move: hn; rewrite -!mulrA; lra.
have hcm : c0 / 2 <= m%:R / n%:R.
  rewrite ler_pdivlMr // mulrAC ler_pdivrMr ?ltr0n //.
  by move: hm'; rewrite -natr1; lra.
apply: le_trans (sat_center_ge_prob kn mM).
have hpos : 0 <= c0 / 2 by rewrite divr_ge0 ?ltW.
have hP2 : 2^-1 <= sat_prob R n k m by apply: le_trans hP; move: kn2; lra.
have h2 : 0 <= (2 : R)^-1 by rewrite invr_ge0 ler0n.
apply: le_trans (ler_pM hpos h2 hcm hP2).
have hk : (k%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
have he : expR 2 != 0 :> R by rewrite gt_eqF ?expR_gt0.
by have -> : c0 / 2 / 2 = sat_a0 k by rewrite /sat_a0 /c0; field.
Qed.

(* The upper bound 2^k + 1 of the centers, once 2^(k+1) (2/e)^n <= 1. *)
Lemma sat_center_upper n k : (k <= n)%N -> (0 < n)%N ->
  2 ^+ k.+1 * (2 / expR 1) ^+ n <= 1 :> R ->
  sat_center n k <= 2 ^+ k + 1 :> R.
Proof.
move=> kn n0 h; apply: le_trans (sat_center_first_moment kn n0) _.
by rewrite lerD2l.
Qed.

End center_bounds.
