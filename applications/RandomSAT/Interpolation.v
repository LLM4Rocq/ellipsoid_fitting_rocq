From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum reals.
From mathcomp Require Import archimedean sequences exp.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean binomial_mean.
From GaussianAnalysis.probability Require Import commuting_operators.
From GaussianApplications.RandomSAT Require Import Model Pivotal Replacement.
From GaussianApplications.RandomSAT Require Import Survival.
From GaussianApplications Require Import SatVarianceDefinitions.
From GaussianApplications Require Import SatThresholdDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: the interpolation of auxiliary formulas                    *)
(*                                                                            *)
(* Part of target T9 of phase 13. A Rocq formalization of the credited        *)
(* argument of the lemma 'Auxiliary product inequality'                       *)
(* (lem:auxiliary-product) of 'A Limiting Satisfiability Threshold for Every  *)
(* Fixed Clause Size' (family 235 of the OpenAI math collection, revision     *)
(* 1581d4cbd, source/sections/convergence.tex), in the fixed-count form of    *)
(* the Lean development of the collection (lean/OAI/Probability/RandomSAT):   *)
(* Lean: auxiliaryProbability (Interpolation.lean, line 126)                  *)
(* Lean: embedded_kill_probability (Interpolation.lean, line 179)             *)
(* Lean: partition_kill_convex (Interpolation.lean, line 244)                 *)
(* Lean: globalAverage_ge_local (Interpolation.lean, line 264)                *)
(* Lean: local_iterates_block (Interpolation.lean, line 371)                  *)
(* Lean: auxiliary_interpolation (Interpolation.lean, line 397)               *)
(*                                                                            *)
(* An auxiliary clause on v variables (aux_clause v k) is a k-tuple of signed *)
(* literals drawn independently and uniformly: repeated variables and         *)
(* tautologies are allowed. aux_sat e C is the set of the assignments of 'I_n *)
(* that satisfy C read through e : 'I_v -> 'I_n, and emb_avg e averages a     *)
(* function of sets of assignments at the intersection with aux_sat e C over  *)
(* a uniform clause C (meet_avg of commuting_operators.v). aux_prob n k m,    *)
(* the m-th iterate of aux_avg at the indicator alive of nonempty sets        *)
(* started at the set of all assignments, is the probability that m           *)
(* independent auxiliary clauses on n variables are satisfiable.              *)
(*                                                                            *)
(* - emb_avg_alive: one embedded clause empties a nonempty set S with         *)
(*   probability (b / (2 v))^k, where b is the number of variables of 'I_v    *)
(*   whose images are forced by S (emb_forced).                               *)
(* - global_ge_local: on r + s variables, the global average is at least the  *)
(*   mixture of the two block averages with weights r/(r+s) and s/(r+s), by   *)
(*   the convexity of z^k (convex_expr2).                                     *)
(* - aux_interpolation: binomial_mean m (r/(r+s)) (fun j => aux_prob r k j *  *)
(*   aux_prob s k (m - j)) <= aux_prob (r + s) k m, for r, s > 0: the m       *)
(*   clauses split between the two blocks as a binomial law. From             *)
(*   binomial_mix_le_iter of commuting_operators.v and the product of the     *)
(*   iterates on the two blocks (iter_block).                                 *)
(*                                                                            *)
(* Departure: the manuscript draws a Poisson number of clauses and            *)
(* differentiates in time; the Lean development and this file draw a fixed    *)
(* number m of clauses, and the binomial split of m between the two blocks    *)
(* replaces the independence of the Poisson families.                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section aux_clauses.
Context {R : realType}.

(* An auxiliary clause on v variables: k signed literals, drawn
   independently and uniformly; repeated variables are allowed. *)
Definition aux_clause (v k : nat) := (k.-tuple ('I_v * bool))%type.

(* The assignments on n variables that satisfy the auxiliary clause C on v
   variables, read through e : 'I_v -> 'I_n. *)
Definition aux_sat n v k (e : 'I_v -> 'I_n) (C : aux_clause v k) :
    {set {ffun 'I_n -> bool}} :=
  [set s : {ffun 'I_n -> bool} |
    [exists j, s (e (tnth C j).1) == (tnth C j).2]].

(* The average over one uniform embedded auxiliary clause. *)
Definition emb_avg n v k (e : 'I_v -> 'I_n) :
    ({set {ffun 'I_n -> bool}} -> R) -> {set {ffun 'I_n -> bool}} -> R :=
  meet_avg (fun C : aux_clause v k => aux_sat e C).

Definition aux_avg (n k : nat) :
    ({set {ffun 'I_n -> bool}} -> R) -> {set {ffun 'I_n -> bool}} -> R :=
  @emb_avg n n k id.

(* The probability that m independent uniform auxiliary clauses of size k
   on n variables are satisfiable. *)
Definition aux_prob n k m : R :=
  iter m (@aux_avg n k) alive [set: {ffun 'I_n -> bool}].

(* The variables of 'I_v whose image under e is forced by S. *)
Definition emb_forced n v (S : {set {ffun 'I_n -> bool}}) (e : 'I_v -> 'I_n) :
    {set 'I_v} := [set i | e i \in forced S].

(* A literal is false on all of a nonempty S exactly when its variable is
   forced, with the opposite sign. *)
Lemma opposing_literal n v (S : {set {ffun 'I_n -> bool}}) (e : 'I_v -> 'I_n)
    (s0 : {ffun 'I_n -> bool}) (l : 'I_v * bool) : s0 \in S ->
  [forall s in S, s (e l.1) != l.2] =
  (l.1 \in emb_forced S e) && (l.2 == ~~ s0 (e l.1)).
Proof.
move=> s0S; rewrite inE (forced_frozen s0S) inE.
apply/forall_inP/andP => [h|[/forall_inP fr /eqP ->] s sS]; last first.
  by rewrite (eqP (fr s sS)); case: (s0 (e l.1)).
have hb : l.2 = ~~ s0 (e l.1).
  by move: (h s0 s0S); case: (l.2); case: (s0 (e l.1)).
split; last by rewrite hb.
apply/forall_inP => s sS; have := h s sS; rewrite hb.
by case: (s (e l.1)); case: (s0 (e l.1)).
Qed.

(* A uniform literal is false on all of a nonempty S with probability
   #|emb_forced S e| / (2 v). *)
Lemma opposing_mean n v (S : {set {ffun 'I_n -> bool}}) (e : 'I_v -> 'I_n)
    (s0 : {ffun 'I_n -> bool}) : s0 \in S ->
  unif_mean (fun l : 'I_v * bool => [forall s in S, s (e l.1) != l.2]%:R : R)
  = #|emb_forced S e|%:R / (2 * v%:R).
Proof.
move=> s0S; rewrite (eq_unif_mean (fun l => congr1 (fun b : bool => b%:R : R)
  (opposing_literal e l s0S))) unif_mean_pair /=.
transitivity (unif_mean (fun i : 'I_v => (i \in emb_forced S e)%:R * 2^-1 : R)).
  apply: eq_unif_mean => i; rewrite /unif_mean card_bool big_bool /=.
  by case: (i \in emb_forced S e); case: (s0 (e i));
    rewrite /= ?mul0r ?mul1r ?addr0 ?add0r ?mulr0 ?mulr1 // mulrC.
rewrite unif_meanZr unif_mean_indicator card_ord invfM mulrAC mulrA.
by congr (_ * _ * _); congr (_%:R); apply: eq_card => i; rewrite !inE.
Qed.

(* One embedded auxiliary clause kills a nonempty S with probability
   (#|emb_forced S e| / (2 v))^k. *)
Lemma emb_avg_alive n v k (e : 'I_v -> 'I_n) (S : {set {ffun 'I_n -> bool}}) :
  (0 < v)%N -> emb_avg k e alive S =
  alive S * (1 - (#|emb_forced S e|%:R / (2 * v%:R)) ^+ k) :> R.
Proof.
move=> v0; have L0 : (0 < #|{: 'I_v * bool}|)%N.
  by rewrite card_prod card_ord card_bool muln_gt0 v0.
have C0 : (0 < #|{: aux_clause v k}|)%N by rewrite card_tuple expn_gt0 L0.
rewrite /emb_avg /meet_avg; case: (set_0Vmem S) => [->|[s0 s0S]].
  rewrite alive0 mul0r (eq_unif_mean (g := fun=> 0)) ?unif_mean_cst //.
  by move=> C; rewrite set0I alive0.
have S0 : S != set0 by apply/set0Pn; exists s0.
have aS : alive S = 1 :> R by rewrite /alive S0.
rewrite aS mul1r -(opposing_mean e s0S) -unif_mean_tuple_prod.
rewrite -[X in X - _](unif_mean_cst (1 : R) C0) -unif_meanB.
apply: eq_unif_mean => C.
have -> : \prod_(x <- C) [forall s in S, s (e x.1) != x.2]%:R =
    (all (fun x => [forall s in S, s (e x.1) != x.2]) C)%:R :> R.
  elim: (tval C) => [|x c IH]; rewrite ?big_nil ?big_cons //= IH.
  by case: [forall s in S, _]; rewrite ?mul1r ?mul0r.
have hall : (S :&: aux_sat e C == set0) =
    all (fun x => [forall s in S, s (e x.1) != x.2]) C.
  apply/eqP/allP => [h l lC|h].
    apply/forall_inP => s sS; apply/negP => /eqP sl.
    have : s \in S :&: aux_sat e C.
      rewrite inE sS inE; apply/existsP.
      by have /tnthP [j hj] := lC; exists j; rewrite -hj sl.
    by rewrite h inE.
  apply/eqP; rewrite -subset0; apply/subsetP => s.
  rewrite !inE => /andP [sS /existsP [j /eqP hj]].
  have := h _ (mem_tnth j C) => /forall_inP /(_ s sS).
  by rewrite hj eqxx.
by rewrite /alive -hall; case: (S :&: aux_sat e C == set0);
  rewrite ?subrr ?subr0.
Qed.

(* The convexity of x^k on [0, +oo), at two points. *)
Lemma convex_expr2 (p a b : R) k : 0 <= p <= 1 -> 0 <= a -> 0 <= b ->
  (p * a + (1 - p) * b) ^+ k <= p * a ^+ k + (1 - p) * b ^+ k.
Proof.
case/andP => p0 p1 a0 b0; elim: k => [|k IH].
  by rewrite !expr0 !mulr1; lra.
set x := p * a + (1 - p) * b.
have x0 : 0 <= x by rewrite addr_ge0 ?mulr_ge0 ?subr_ge0.
apply: le_trans (_ : x ^+ k.+1 <= x * (p * a ^+ k + (1 - p) * b ^+ k)) _.
  by rewrite exprS ler_wpM2l.
have hab : 0 <= (a - b) * (a ^+ k - b ^+ k).
  case: (leP b a) => ab; first by rewrite mulr_ge0 ?subr_ge0 // lerXn2r ?nnegrE.
  have abk : a ^+ k <= b ^+ k by rewrite lerXn2r ?nnegrE // ltW.
  by apply: mulr_le0; rewrite subr_le0 //; exact: ltW.
have e : p * a ^+ k.+1 + (1 - p) * b ^+ k.+1 -
    x * (p * a ^+ k + (1 - p) * b ^+ k) =
    p * (1 - p) * ((a - b) * (a ^+ k - b ^+ k)) by rewrite /x !exprS; ring.
by rewrite -subr_ge0 e; apply: mulr_ge0 => //; rewrite mulr_ge0 // subr_ge0.
Qed.

(* The forced variables of a set of assignments on r + s variables are those
   of the first block and those of the second. *)
Lemma forced_split r s (S : {set {ffun 'I_(r + s) -> bool}}) :
  #|forced S| =
    (#|emb_forced S (@lshift r s)| + #|emb_forced S (@rshift r s)|)%N.
Proof.
rewrite -!sum1_card !big_mkcond /= big_split_ord /=.
rewrite [X in _ = (X + _)%N]big_mkcond [X in _ = (_ + X)%N]big_mkcond /=.
by congr (_ + _)%N; apply: eq_bigr => i _; rewrite [i \in emb_forced _ _]inE.
Qed.

(* The two blocks of an assignment on r + s variables. *)
Definition block_left r s (sg : {ffun 'I_(r + s) -> bool}) :
  {ffun 'I_r -> bool} := [ffun i => sg (lshift s i)].
Definition block_right r s (sg : {ffun 'I_(r + s) -> bool}) :
  {ffun 'I_s -> bool} := [ffun i => sg (rshift r i)].
Definition block_set r s (S : {set {ffun 'I_r -> bool}})
    (T : {set {ffun 'I_s -> bool}}) : {set {ffun 'I_(r + s) -> bool}} :=
  [set sg | (block_left sg \in S) && (block_right sg \in T)].

Lemma block_setT r s :
  block_set [set: {ffun 'I_r -> bool}] [set: {ffun 'I_s -> bool}] = setT.
Proof. by apply/setP => sg; rewrite !inE. Qed.

Lemma alive_block r s (S : {set {ffun 'I_r -> bool}})
    (T : {set {ffun 'I_s -> bool}}) :
  alive (block_set S T) = alive S * alive T :> R.
Proof.
rewrite /alive; case: (set_0Vmem S) => [->|[s1 s1S]].
  have -> : block_set (set0 : {set {ffun 'I_r -> bool}}) T = set0.
    by apply/setP => sg; rewrite !inE.
  by rewrite !eqxx /= mul0r.
case: (set_0Vmem T) => [->|[s2 s2T]].
  have -> : block_set S (set0 : {set {ffun 'I_s -> bool}}) = set0.
    by apply/setP => sg; rewrite !inE andbF.
  by rewrite !eqxx /= mulr0.
pose sg : {ffun 'I_(r + s) -> bool} :=
  [ffun i => match split i with inl j => s1 j | inr j => s2 j end].
have hsg : sg \in block_set S T.
  rewrite inE; apply/andP; split.
    have -> : block_left sg = s1.
      by apply/ffunP => i; rewrite !ffunE (unsplitK (inl _ i)).
    by [].
  have -> : block_right sg = s2.
    by apply/ffunP => i; rewrite !ffunE (unsplitK (inr _ i)).
  by [].
have -> : block_set S T != set0 by apply/set0Pn; exists sg.
have -> : S != set0 by apply/set0Pn; exists s1.
have -> : T != set0 by apply/set0Pn; exists s2.
by rewrite /= mulr1.
Qed.

(* A clause embedded in the first block acts on the first block only. *)
Lemma block_sat_left r s k (S : {set {ffun 'I_r -> bool}})
    (T : {set {ffun 'I_s -> bool}}) (C : aux_clause r k) :
  block_set S T :&: aux_sat (@lshift r s) C = block_set (S :&: aux_sat id C) T.
Proof.
apply/setP => sg; rewrite !inE.
have -> : [exists j, block_left sg (tnth C j).1 == (tnth C j).2] =
    [exists j, sg (lshift s (tnth C j).1) == (tnth C j).2].
  by apply: eq_existsb => j; rewrite ffunE.
by rewrite -!andbA [_ && (_ \in T)]andbC.
Qed.

Lemma block_sat_right r s k (S : {set {ffun 'I_r -> bool}})
    (T : {set {ffun 'I_s -> bool}}) (C : aux_clause s k) :
  block_set S T :&: aux_sat (@rshift r s) C = block_set S (T :&: aux_sat id C).
Proof.
apply/setP => sg; rewrite !inE.
have -> : [exists j, block_right sg (tnth C j).1 == (tnth C j).2] =
    [exists j, sg (rshift r (tnth C j).1) == (tnth C j).2].
  by apply: eq_existsb => j; rewrite ffunE.
by rewrite -!andbA.
Qed.

(* The iterates of the two embedded averages factor over the blocks. *)
Lemma iter_block r s k j l (S : {set {ffun 'I_r -> bool}})
    (T : {set {ffun 'I_s -> bool}}) :
  iter j (@emb_avg _ r k (@lshift r s))
    (iter l (@emb_avg _ s k (@rshift r s)) alive) (block_set S T) =
  iter j (@aux_avg r k) alive S * iter l (@aux_avg s k) alive T :> R.
Proof.
elim: j S => [|j IH] S /=.
  elim: l T => [|l IHl] T /=; first exact: alive_block.
  rewrite /emb_avg /aux_avg /emb_avg /meet_avg -unif_meanZ.
  by apply: eq_unif_mean => C; rewrite block_sat_right; exact: IHl.
rewrite /emb_avg /aux_avg /emb_avg /meet_avg -unif_meanZr.
by apply: eq_unif_mean => C; rewrite block_sat_left; exact: IH.
Qed.

(* One step: an auxiliary clause on all r + s variables kills a set of
   assignments less often than the r / (r + s)-mixture of the clauses
   confined to each block, by the convexity of x^k. *)
Lemma global_ge_local r s k (S : {set {ffun 'I_(r + s) -> bool}}) :
  (0 < r)%N -> (0 < s)%N ->
  r%:R / (r + s)%:R * @emb_avg _ r k (@lshift r s) alive S +
  (1 - r%:R / (r + s)%:R) * @emb_avg _ s k (@rshift r s) alive S
  <= @aux_avg (r + s) k alive S :> R.
Proof.
move=> r0 s0; have rs0 : (0 < r + s)%N by rewrite addn_gt0 r0.
rewrite /aux_avg !emb_avg_alive //.
have -> : emb_forced S id = forced S by apply/setP => i; rewrite [in LHS]inE.
rewrite forced_split; set b1 := #|emb_forced S (lshift s)|.
set b2 := #|emb_forced S (@rshift r s)|; set p : R := r%:R / (r + s)%:R.
set x1 : R := b1%:R / (2 * r%:R); set x2 : R := b2%:R / (2 * s%:R).
have hx : (b1 + b2)%:R / (2 * (r + s)%:R) = p * x1 + (1 - p) * x2 :> R.
  have rn : (r%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
  have sn : (s%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
  have rsn : (r%:R + s%:R : R) != 0 by rewrite -natrD pnatr_eq0 -lt0n.
  by rewrite /p /x1 /x2 !natrD; field.
have p01 : 0 <= p <= 1.
  apply/andP; split; first by rewrite divr_ge0 ?ler0n.
  by rewrite ler_pdivrMr ?ltr0n // mul1r ler_nat leq_addr.
have x10 : 0 <= x1 by rewrite divr_ge0 ?mulr_ge0 ?ler0n.
have x20 : 0 <= x2 by rewrite divr_ge0 ?mulr_ge0 ?ler0n.
have hc := convex_expr2 k p01 x10 x20.
rewrite hx; have -> : p * (alive S * (1 - x1 ^+ k)) +
    (1 - p) * (alive S * (1 - x2 ^+ k)) =
    alive S * (1 - (p * x1 ^+ k + (1 - p) * x2 ^+ k)) by ring.
by rewrite ler_wpM2l ?alive_ge0 // lerB.
Qed.

(* The fixed-count interpolation of the auxiliary probabilities: m clauses
   on r + s variables survive at least as often as a binomial number of them
   confined to the first block, the others to the second. *)
Theorem aux_interpolation r s k m : (0 < r)%N -> (0 < s)%N ->
  binomial_mean m (r%:R / (r + s)%:R)
    (fun j => aux_prob r k j * aux_prob s k (m - j))
  <= aux_prob (r + s) k m :> R.
Proof.
move=> r0 s0; set p : R := r%:R / (r + s)%:R.
have p01 : 0 <= p <= 1.
  apply/andP; split; first by rewrite divr_ge0 ?ler0n.
  by rewrite ler_pdivrMr ?ltr0n ?addn_gt0 ?r0 // mul1r ler_nat leq_addr.
pose E1 := @emb_avg (r + s) r k (@lshift r s).
pose E2 := @emb_avg (r + s) s k (@rshift r s).
pose E := @aux_avg (r + s) k.
have h := @binomial_mix_le_iter R _ E1 E2 E p alive p01
  (meet_avg_linear _) (meet_avg_linear _) (meet_avg_linear _)
  (meet_avg_monotone _) (meet_avg_monotone _) (meet_avg_monotone _)
  (fun g => meet_avgC _ _ g) (fun g => meet_avgC _ _ g)
  (fun g => meet_avgC _ _ g) (fun S => global_ge_local k S r0 s0) m setT.
apply: le_trans h; rewrite le_eqVlt; apply/orP; left; apply/eqP.
by apply: eq_bigr => j _; congr (_ * _); rewrite -block_setT iter_block.
Qed.

End aux_clauses.
