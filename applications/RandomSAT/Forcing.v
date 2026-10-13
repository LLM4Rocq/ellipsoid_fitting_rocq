From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum
  reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import finite_mean.
From GaussianApplications.RandomSAT Require Import Model Pivotal Replacement.
From GaussianApplications Require Import SatVarianceDefinitions.

(**md**************************************************************************)
(* # Random k-SAT: integrated forcing                                         *)
(*                                                                            *)
(* Part of target T7 of phase 12 (see Model.v). A Rocq formalization of the   *)
(* credited argument of the proposition 'Integrated forcing' of 'A limiting   *)
(* satisfiability threshold for every fixed clause size' (family 235 of the   *)
(* OpenAI math collection, revision 1581d4cbd, source/sections/forcing.tex),  *)
(* following the Lean development of the collection                           *)
(* (lean/OAI/Probability/RandomSAT):                                          *)
(* Lean: binomialMean (Binomial.lean, line 17)                                *)
(* Lean: binomial_replacement_sum_le (Binomial.lean, line 162)                *)
(* Lean: head_forced_reduction (Forcing.lean, line 88)                        *)
(* Lean: deletedMean_eq_binomial (Forcing.lean, line 239)                     *)
(* Lean: erasedMean_replacement (Forcing.lean, line 265)                      *)
(* Lean: integrated_head_forcing (Forcing.lean, line 386)                     *)
(* Lean: forced_coordinate_mean (Forcing.lean, line 493)                      *)
(* Lean: forcedFractionMean_eq_head (Forcing.lean, line 525)                  *)
(*                                                                            *)
(* The clauses have size k.+1 and n.+1 variables, with k < n.                 *)
(*                                                                            *)
(* - binom_mean p m f is the mean of f over a binomial number of successes in *)
(*   m trials of probability p, defined by its recursion on the first trial.  *)
(*   binom_rep_sum_le sums the replacement differences rep_diff P g j d = P   *)
(*   (j - d) - P (j + (g - 1) d) of a nonincreasing P with values in [0, 1],  *)
(*   by telescoping (sum_shift_diff_le).                                      *)
(* - If the first variable is forced by the clauses t, then deleting it, that *)
(*   is dropping the clauses that contain it, leaves a satisfiable formula,   *)
(*   and erasing it, that is removing its literal from these clauses, leaves  *)
(*   an unsatisfiable one (head_forced_reduction).                            *)
(* - The number of clauses that contain the first variable is binomial with p *)
(*   = k.+1 / n.+1, and the other clauses are uniform of size k.+1 on the     *)
(*   other n variables (del_mean_binom). Erasing, then replacing each         *)
(*   shortened clause by a block of g clauses of size k.+1 (kill_replacement  *)
(*   of Replacement.v), costs at most a^-k per shortened clause               *)
(*   (era_mean_replacement).                                                  *)
(* - integrated_head_forcing: for 1 <= k < n, a > 0 with 1 / (n + 1) <= a^-k  *)
(*   and g >= 2 (k + 1) a, the probabilities head_forced n k j that the first *)
(*   variable is forced by j clauses satisfy                                  *)
(*                                                                            *)
(* sum_(j <= M) head_forced n k j <= g M p + (M + 1) M p a^-k.                *)
(*                                                                            *)
(* - The renamings of the variables preserve the uniform law of the clauses   *)
(*   and move the forced variables (forced_rename). Hence the mean fraction   *)
(*   of forced variables forced_frac n k m equals head_forced n k m           *)
(*   (forced_frac_head).                                                      *)
(*                                                                            *)
(* The manuscript erases the last variable; here, as in the Lean development, *)
(* the first. The manuscript bounds the binomial weights by (k M / n)^d / d!; *)
(* here, as in the Lean development, the replacement differences are summed   *)
(* under the binomial mean of the cap M (binom_rep_sum_le), which gives the   *)
(* term g M p instead of the manuscript's (k M / n) e^(k M / n) g; at M =     *)
(* 2^(k+1) n this removes the factor e^(k 2^(k+1)) from the constant.         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The mean of f over a binomial number of successes in m trials of
   probability p, by its recursion on the first trial. *)
Section binom_mean.
Context {R : realType}.

Fixpoint binom_mean (p : R) (m : nat) (f : nat -> R) : R :=
  if m is m'.+1 then
    (1 - p) * binom_mean p m' f + p * binom_mean p m' (fun d => f d.+1)
  else f 0%N.

Lemma eq_binom_mean p m (f g : nat -> R) :
  (forall d, (d <= m)%N -> f d = g d) -> binom_mean p m f = binom_mean p m g.
Proof.
elim: m f g => [|m IH] f g fg /=; first exact: fg.
by rewrite (IH f g) ?(IH (fun d => f d.+1) (fun d => g d.+1)) // => d dm;
  apply: fg; rewrite ?ltnS // ltnW.
Qed.

Lemma binom_mean_cst p m (c : R) : binom_mean p m (fun=> c) = c.
Proof. by elim: m => //= m ->; ring. Qed.

Lemma binom_meanD p m (f g : nat -> R) :
  binom_mean p m (fun d => f d + g d) = binom_mean p m f + binom_mean p m g.
Proof. by elim: m f g => //= m IH f g; rewrite !IH; ring. Qed.

Lemma binom_meanZ p m (c : R) (f : nat -> R) :
  binom_mean p m (fun d => c * f d) = c * binom_mean p m f.
Proof. by elim: m f => //= m IH f; rewrite !IH; ring. Qed.

Lemma binom_meanN p m (f : nat -> R) :
  binom_mean p m (fun d => - f d) = - binom_mean p m f.
Proof.
rewrite -mulN1r -binom_meanZ; apply: eq_binom_mean => d _; by rewrite mulN1r.
Qed.

Lemma binom_meanB p m (f g : nat -> R) :
  binom_mean p m (fun d => f d - g d) = binom_mean p m f - binom_mean p m g.
Proof. by rewrite binom_meanD binom_meanN. Qed.

Lemma ler_binom_mean p m (f g : nat -> R) : 0 <= p -> p <= 1 ->
  (forall d, (d <= m)%N -> f d <= g d) -> binom_mean p m f <= binom_mean p m g.
Proof.
move=> p0 p1; elim: m f g => [|m IH] f g fg /=; first exact: fg.
apply: lerD; apply: ler_wpM2l; rewrite ?subr_ge0 //; apply: IH => d dm.
  by apply: fg; rewrite ltnW.
by apply: fg.
Qed.

Lemma binom_mean_id p m : binom_mean p m (fun d => d%:R) = m%:R * p.
Proof.
elim: m => [|m IH] /=; first by rewrite mul0r.
have -> : binom_mean p m (fun d => d.+1%:R) =
    binom_mean p m (fun d => 1 + d%:R).
  by apply: eq_binom_mean => d _; rewrite -nat1r.
by rewrite binom_meanD binom_mean_cst IH -nat1r; ring.
Qed.

(* More trials give more successes. *)
Lemma binom_mean_trials_le p m (f : nat -> R) : 0 <= p -> p <= 1 ->
  {homo f : d d' / (d <= d')%N >-> d <= d'} ->
  binom_mean p m f <= binom_mean p m.+1 f.
Proof.
move=> p0 p1 hf /=.
have h : binom_mean p m f <= binom_mean p m (fun d => f d.+1).
  by apply: ler_binom_mean => // d _; apply: hf.
by have := ler_wpM2l p0 h; lra.
Qed.

Lemma binom_mean_trials p m m' (f : nat -> R) : 0 <= p -> p <= 1 ->
  {homo f : d d' / (d <= d')%N >-> d <= d'} -> (m <= m')%N ->
  binom_mean p m f <= binom_mean p m' f.
Proof.
move=> p0 p1 hf; elim: m' => [|m' IH]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP -> //|]; rewrite ltnS => mm.
exact: le_trans (IH mm) (binom_mean_trials_le _ p0 p1 hf).
Qed.

Lemma binom_mean_sum p m (I : finType) (F : I -> nat -> R) :
  binom_mean p m (fun d => \sum_i F i d) = \sum_i binom_mean p m (F i).
Proof.
elim: m F => [|m IH] F //=; rewrite IH (IH (fun i d => F i d.+1)).
by rewrite !mulr_sumr -big_split.
Qed.

Lemma unif_mean_binom_mean (T : finType) p m (f : nat -> T -> R) :
  unif_mean (fun x => binom_mean p m (fun d => f d x)) =
  binom_mean p m (fun d => unif_mean (f d)).
Proof.
elim: m f => [|m IH] f //=; rewrite unif_meanD !unif_meanZ IH.
by rewrite (IH (fun d => f d.+1)).
Qed.

(* Telescoping: sum_(j < l) (P j - P (j + b)) <= b for P with values in
   [0, 1]. *)
Lemma sum_shift_diff_le (P : nat -> R) l b :
  (forall j, 0 <= P j) -> (forall j, P j <= 1) ->
  \sum_(j < l) (P j - P (j + b)%N) <= b%:R.
Proof.
move=> P0 P1.
have sh : \sum_(0 <= j < l) P (j + b)%N = \sum_(b <= j < l + b) P j.
  by rewrite -{2}(add0n b) big_addn addnK.
rewrite sumrB -(big_mkord xpredT P)
  -(big_mkord xpredT (fun j => P (j + b)%N)) sh.
have e1 : \sum_(0 <= j < l + b) P j =
    \sum_(0 <= j < b) P j + \sum_(b <= j < l + b) P j.
  by rewrite (big_cat_nat (n := b)) ?leq_addl.
have e2 : \sum_(0 <= j < l + b) P j =
    \sum_(0 <= j < l) P j + \sum_(l <= j < l + b) P j.
  by rewrite (big_cat_nat (n := l)) ?leq_addr.
have h1 : \sum_(0 <= j < b) P j <= b%:R.
  rewrite big_mkord; apply: le_trans (_ : \sum_(j < b) (1 : R) <= _).
    by apply: ler_sum => j _; exact: P1.
  by rewrite sumr_const card_ord.
have h2 : 0 <= \sum_(l <= j < l + b) P j by apply: sumr_ge0 => j _.
lra.
Qed.

Definition rep_diff (P : nat -> R) (g j d : nat) : R :=
  P (j - d)%N - P (j + (g - 1) * d)%N.

Lemma rep_diff_mono (P : nat -> R) g j :
  {homo P : x y / (x <= y)%N >-> y <= x} ->
  {homo rep_diff P g j : d d' / (d <= d')%N >-> d <= d'}.
Proof.
move=> hP d d' dd; rewrite /rep_diff; apply: lerB; apply: hP.
  exact: leq_sub2l.
by rewrite leq_add2l leq_mul2l dd orbT.
Qed.

Lemma rep_diff_sum_le (P : nat -> R) g l d :
  (forall j, 0 <= P j) -> (forall j, P j <= 1) -> (1 <= g)%N ->
  \sum_(j < l) rep_diff P g j d <= g%:R * d%:R.
Proof.
move=> P0 P1 g1.
have e j : rep_diff P g j d =
    (P (j - d)%N - P j) + (P j - P (j + (g - 1) * d)%N).
  by rewrite /rep_diff; ring.
under eq_bigr => j _ do rewrite e.
rewrite big_split /=.
have h1 : \sum_(j < l) (P (j - d)%N - P j) <= d%:R.
  have := sum_shift_diff_le (P := fun j => P (j - d)%N) l d (fun j => P0 _)
    (fun j => P1 _).
  by under eq_bigr do rewrite addnK.
have h2 := sum_shift_diff_le l ((g - 1) * d) P0 P1.
have -> : g%:R * d%:R = d%:R + ((g - 1) * d)%:R :> R.
  by rewrite -natrM -natrD -mulSn subn1 prednK.
exact: lerD.
Qed.

Lemma binom_rep_sum_le (P : nat -> R) p g M : 0 <= p -> p <= 1 ->
  {homo P : x y / (x <= y)%N >-> y <= x} ->
  (forall j, 0 <= P j) -> (forall j, P j <= 1) -> (1 <= g)%N ->
  \sum_(j < M.+1) binom_mean p j (rep_diff P g j) <= g%:R * M%:R * p.
Proof.
move=> p0 p1 hP P0 P1 g1.
apply: le_trans (_ : \sum_(j < M.+1) binom_mean p M (rep_diff P g j) <= _).
  apply: ler_sum => j _; apply: binom_mean_trials => //.
    exact: rep_diff_mono.
  by rewrite -ltnS.
rewrite -binom_mean_sum.
apply: le_trans (_ : binom_mean p M (fun d => g%:R * d%:R) <= _).
  by apply: ler_binom_mean => // d _; exact: rep_diff_sum_le.
by rewrite binom_meanZ binom_mean_id mulrA.
Qed.

End binom_mean.

(* The first variable of an assignment on n.+1 variables, and the rest. *)
Section assignment_split.
Variable n : nat.
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation asg1 := {ffun 'I_n.+1 -> bool}.

Definition atail (s : asg1) : asg := [ffun j => s (lift ord0 j)].

Definition aext (s : asg) (b : bool) : asg1 :=
  [ffun i => if unlift ord0 i is Some j then s j else b].

Lemma atail_ext s b : atail (aext s b) = s.
Proof. by apply/ffunP => j; rewrite !ffunE liftK. Qed.

Lemma aext0 s b : aext s b ord0 = b.
Proof. by rewrite ffunE unlift_none. Qed.

Lemma exists_ordS (P : pred 'I_n.+1) :
  [exists i, P i] = P ord0 || [exists j : 'I_n, P (lift ord0 j)].
Proof.
apply/existsP/orP => [[i]|[P0|/existsP[j Pj]]]; last 2 first.
- by exists ord0.
- by exists (lift ord0 j).
by case: (unliftP ord0 i) => [j ->|->] Pi;
  [right; apply/existsP; exists j|left].
Qed.

Lemma sat_cabsent k (s : asg1) (d : clause n k) :
  clause_sat s (cabsent d) = clause_sat (atail s) d.
Proof.
rewrite /clause_sat exists_ordS /= prepend0 /=.
by apply: eq_existsb => j; rewrite prepend_lift ffunE.
Qed.

Lemma sat_cpresent k (s : asg1) (q : clause n k) b :
  clause_sat s (cpresent q b) = (b == s ord0) || clause_sat (atail s) q.
Proof.
rewrite /clause_sat exists_ordS /= prepend0; congr orb.
by apply: eq_existsb => j; rewrite prepend_lift ffunE.
Qed.

End assignment_split.

Section erasure.
Context {R : realType} (n k : nat).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation asg1 := {ffun 'I_n.+1 -> bool}.
Local Notation C1 := (clause n.+1 k.+1).

(* The constraints left on the other variables by a clause on n.+1
   variables, once the first variable is deleted (its clauses are dropped)
   or erased (its literal is removed from its clauses). *)
Definition del_ok (s : asg) (c : C1) : bool :=
  if csplit c is inl d then clause_sat s d else true.

Definition era_ok (s : asg) (c : C1) : bool :=
  match csplit c with inl d => clause_sat s d
  | inr (q, _) => clause_sat s q end.

Definition deleted (S : {set asg}) (t : seq C1) : {set asg} :=
  [set s in S | all (del_ok s) t].

Definition erased (S : {set asg}) (t : seq C1) : {set asg} :=
  [set s in S | all (era_ok s) t].

Lemma era_del_ok s c : era_ok s c -> del_ok s c.
Proof. by rewrite /era_ok /del_ok; case: (csplit c) => // -[]. Qed.

Lemma erased_sub S t : erased S t \subset deleted S t.
Proof.
apply/subsetP => s; rewrite !inE => /andP[-> /allP h] /=.
by apply/allP => c ct; apply: era_del_ok; exact: h.
Qed.

Lemma sat_del_ok (s : asg1) (c : C1) : clause_sat s c -> del_ok (atail s) c.
Proof.
rewrite -[c in clause_sat _ c](csplitK c) /del_ok.
by case: (csplit c) => [d|[q b]] //=; rewrite sat_cabsent.
Qed.

Lemma era_ok_sat (s : asg) b (c : C1) : era_ok s c -> clause_sat (aext s b) c.
Proof.
rewrite -[c in clause_sat _ c](csplitK c) /era_ok.
case: (csplit c) => [d|[q b']] /=; first by rewrite sat_cabsent atail_ext.
by rewrite sat_cpresent atail_ext => ->; rewrite orbT.
Qed.

(* If the first variable is forced by the clauses t, then deleting it leaves
   a satisfiable formula and erasing it an unsatisfiable one. *)
Lemma head_forced_reduction (t : seq C1) :
  ord0 \in forced (restrict [set: asg1] t) ->
  deleted [set: asg] t != set0 /\ erased [set: asg] t = set0.
Proof.
rewrite inE => /andP[S0 /existsP[bb /forall_inP hb]]; split.
  case/set0Pn: S0 => s1; rewrite restrictE !inE /= => /allP h.
  apply/set0Pn; exists (atail s1); rewrite !inE /=; apply/allP => c ct.
  by apply: sat_del_ok; exact: h.
apply/setP => s; rewrite !inE /=; apply/negbTE/negP => /allP h.
have mem b : aext s b \in restrict [set: asg1] t.
  by rewrite restrictE !inE /=; apply/allP => c ct; apply: era_ok_sat; exact: h.
have := hb _ (mem true); have := hb _ (mem false); rewrite !aext0.
by clear hb mem; case: bb.
Qed.

Lemma head_forced_ind (t : seq C1) :
  (ord0 \in forced (restrict [set: asg1] t))%:R <=
  alive (deleted [set: asg] t) - alive (erased [set: asg] t) :> R.
Proof.
have [/head_forced_reduction [h1 h2]|_] :=
  boolP (ord0 \in forced (restrict [set: asg1] t)).
  by rewrite /alive h1 h2 eqxx subr0.
by rewrite subr_ge0 alive_mono // erased_sub.
Qed.

Lemma deleted_cons S c t :
  deleted S (c :: t) =
  if csplit c is inl d then deleted (add_clause S d) t else deleted S t.
Proof.
apply/setP => s; rewrite /deleted /del_ok !inE /=.
by case: (csplit c) => [d|[q b]]; rewrite /add_clause ?inE /= ?andbA.
Qed.

Lemma erased_cons S c t :
  erased S (c :: t) =
  match csplit c with
  | inl d => erased (add_clause S d) t
  | inr (q, _) => erased (add_clause S q) t
  end.
Proof.
apply/setP => s; rewrite /erased /era_ok !inE /=.
by case: (csplit c) => [d|[q b]]; rewrite /add_clause ?inE /= ?andbA.
Qed.

End erasure.

Lemma csplit_absent n k (d : clause n k.+1) : csplit (cabsent d) = inl d.
Proof. exact: (cjoinK (inl d)). Qed.

Lemma csplit_present n k (q : clause n k) b :
  csplit (cpresent q b) = inr (q, b).
Proof. exact: (cjoinK (inr (q, b))). Qed.

(* Means over consecutive blocks of clauses, and their commutation. *)
Section tuple_avg_facts.
Context {R : realType} (n : nat).
Local Notation asg := {ffun 'I_n -> bool}.

Lemma restrict_add_clause k r (S : {set asg}) (c : clause n r)
    (s : seq (clause n k)) :
  restrict (add_clause S c) s = add_clause (restrict S s) c.
Proof.
rewrite !restrictE /add_clause; apply/setP => x; rewrite !inE.
by rewrite -!andbA [clause_sat x c && _]andbC.
Qed.

Lemma tuple_avg_add k t u (f : {set asg} -> R) S :
  tuple_avg k (t + u) f S = tuple_avg k t (tuple_avg k u f) S.
Proof.
elim: t S => [|t IH] S; first by rewrite add0n tuple_avg0.
rewrite addSn !tuple_avgS /clause_avg; apply: eq_unif_mean => c.
exact: IH.
Qed.

Lemma clause_avg_tuple_avg k r t (f : {set asg} -> R) S :
  clause_avg r (tuple_avg k t f) S = tuple_avg k t (clause_avg r f) S.
Proof.
rewrite /clause_avg /tuple_avg.
rewrite (unif_mean_comm (fun (c : clause n r) (u : t.-tuple (clause n k)) =>
  f (restrict (add_clause S c) u))).
by apply: eq_unif_mean => u; apply: eq_unif_mean => c;
  rewrite restrict_add_clause.
Qed.

Lemma ler_tuple_avg_cst k t (f : {set asg} -> R) (c : R) S :
  (0 < #|{: clause n k}|)%N ->
  tuple_avg k t (fun T => f T - c) S = tuple_avg k t f S - c.
Proof.
move=> C0; rewrite /tuple_avg unif_meanB unif_mean_cst //.
by rewrite card_tuple expn_gt0 C0.
Qed.

Lemma survival_antitone k m (S : {set asg}) : (0 < #|{: clause n k}|)%N ->
  survival k m.+1 S <= survival (R := R) k m S.
Proof.
move=> C0; rewrite {1}/survival tuple_avgS.
rewrite -[X in _ <= X](@unif_mean_cst R (clause n k) _ C0).
by apply: ler_unif_mean => c; apply: survival_mono; exact: add_clause_sub.
Qed.

End tuple_avg_facts.

Section erasure_means.
Context {R : realType} (n k : nat).
Hypothesis kn : (k < n)%N.
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C1 := (clause n.+1 k.+1).

Let p : R := k.+1%:R / n.+1%:R.

Let Ck : (0 < #|{: clause n k}|)%N.
Proof. by rewrite card_clause_gt0 // ltnW. Qed.

Let Ck1 : (0 < #|{: clause n k.+1}|)%N.
Proof. by rewrite card_clause_gt0. Qed.

Lemma p_ge0 : 0 <= p.
Proof. by rewrite /p divr_ge0. Qed.

Lemma p_le1 : p <= 1.
Proof. by rewrite /p ler_pdivrMr ?ltr0n // mul1r ler_nat ltnS ltnW. Qed.

Definition del_mean m (S : {set asg}) : R :=
  unif_mean (fun t : m.-tuple C1 => alive (deleted S t)).

Definition era_mean m (S : {set asg}) : R :=
  unif_mean (fun t : m.-tuple C1 => alive (erased S t)).

Lemma del_mean0 S : del_mean 0 S = alive S.
Proof.
rewrite /del_mean unif_mean_tuple0 /deleted /=; congr alive.
by apply/setP => x; rewrite !inE andbT.
Qed.

Lemma era_mean0 S : era_mean 0 S = alive S.
Proof.
rewrite /era_mean unif_mean_tuple0 /erased /=; congr alive.
by apply/setP => x; rewrite !inE andbT.
Qed.

Lemma del_meanS m S :
  del_mean m.+1 S = (1 - p) * clause_avg k.+1 (del_mean m) S + p * del_mean m S.
Proof.
rewrite /del_mean unif_mean_tuple_cons (unif_mean_clause_split _ (ltnW kn)).
congr (_ * _ + _ * _).
  rewrite /clause_avg; apply: eq_unif_mean => d; apply: eq_unif_mean => t /=.
  by rewrite deleted_cons csplit_absent.
under eq_unif_mean do under eq_unif_mean do under eq_unif_mean do
  rewrite /= deleted_cons csplit_present.
transitivity (unif_mean (fun _ : clause n k =>
    unif_mean (fun t : m.-tuple C1 => alive (deleted S t) : R))).
  by apply: eq_unif_mean => c; apply: unif_mean_cst; rewrite card_bool.
exact: unif_mean_cst.
Qed.

Lemma era_meanS m S :
  era_mean m.+1 S = (1 - p) * clause_avg k.+1 (era_mean m) S +
    p * clause_avg k (era_mean m) S.
Proof.
rewrite /era_mean unif_mean_tuple_cons (unif_mean_clause_split _ (ltnW kn)).
congr (_ * _ + _ * _).
  rewrite /clause_avg; apply: eq_unif_mean => d; apply: eq_unif_mean => t /=.
  by rewrite erased_cons csplit_absent.
rewrite /clause_avg; apply: eq_unif_mean => q.
under eq_unif_mean do under eq_unif_mean do
  rewrite /= erased_cons csplit_present.
by apply: unif_mean_cst; rewrite card_bool.
Qed.

(* Deleting the first variable: the clauses that contain it, a binomial
   number of them, are dropped, and the others are uniform k.+1-clauses on
   the remaining n variables. *)
Lemma del_mean_binom m S :
  del_mean m S = binom_mean p m (fun d => survival k.+1 (m - d) S).
Proof.
elim: m S => [|m IH] S.
  by rewrite del_mean0 /= /survival tuple_avg0.
rewrite del_meanS /=; congr (_ * _ + _ * _).
  rewrite /clause_avg (eq_unif_mean (fun c => IH (add_clause S c))).
  rewrite unif_mean_binom_mean; apply: eq_binom_mean => d dm.
  by rewrite subSn // /survival tuple_avgS.
by rewrite IH; apply: eq_binom_mean => d dm; rewrite subSS.
Qed.

End erasure_means.

Section erased_replacement.
Context {R : realType} (n k g : nat) (a : R).
Hypotheses (k1 : (1 <= k)%N) (kn : (k < n)%N) (a0 : 0 < a).
Hypotheses (hsmall : (n.+1%:R)^-1 <= a^-1 ^+ k) (hg : 2 * k.+1%:R * a <= g%:R).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation C1 := (clause n.+1 k.+1).

Let eps : R := a^-1 ^+ k.
Let p : R := k.+1%:R / n.+1%:R.

Let Ck : (0 < #|{: clause n k}|)%N.
Proof. by rewrite card_clause_gt0 // ltnW. Qed.

Let Ck1 : (0 < #|{: clause n k.+1}|)%N.
Proof. by rewrite card_clause_gt0. Qed.

Let eps0 : 0 <= eps.
Proof. by rewrite exprn_ge0 // invr_ge0 ltW. Qed.

Lemma g_ge1 : (1 <= g)%N.
Proof.
rewrite lt0n; apply/eqP => g0; move: hg; rewrite g0 mulr0n.
by apply/negP; rewrite -ltNge !mulr_gt0 // ltr0n.
Qed.

(* A block of g clauses of size k.+1 survives at most as often as one
   clause of size k, up to eps. *)
Lemma short_survival (T : {set asg}) :
  survival k.+1 g T - eps <= survival (R := R) k 1 T.
Proof.
have h := kill_replacement T k1 kn a0 hsmall hg.
rewrite (killE Ck) in h.
have [->|T0] := eqVneq T set0.
  by rewrite !survival0_set sub0r oppr_le0.
have aT : alive T = 1 :> R by rewrite /alive T0.
move: h; rewrite aT -/eps.
move: (survival k 1 T) (survival k.+1 g T) (eps) => A B e h; lra.
Qed.

Lemma clause_avg_short_survival t (S : {set asg}) :
  survival k.+1 (t + g) S - eps <= clause_avg k (survival k.+1 t) S.
Proof.
rewrite /survival tuple_avg_add -ler_tuple_avg_cst //.
rewrite /survival clause_avg_tuple_avg; apply: ler_tuple_avg => T.
have e : clause_avg k (tuple_avg k 0 (@alive R n)) T = clause_avg k alive T.
  by rewrite /clause_avg; apply: eq_unif_mean => c; rewrite tuple_avg0.
by have := short_survival T; rewrite /survival tuple_avgS e.
Qed.

Lemma clause_avg_subr r (f : {set asg} -> R) (c : R) S :
  (0 < #|{: clause n r}|)%N ->
  clause_avg r (fun T => f T - c) S = clause_avg r f S - c.
Proof. by move=> C0; rewrite /clause_avg unif_meanB unif_mean_cst. Qed.

(* Erasing the first variable and replacing each shortened clause by a block
   of g clauses of size k.+1. *)
Lemma era_mean_replacement m (S : {set asg}) :
  binom_mean p m (fun d => survival k.+1 (m - d + g * d) S - d%:R * eps) <=
  era_mean (R := R) k m S.
Proof.
elim: m S => [|m IH] S.
  by rewrite era_mean0 /= subn0 muln0 addn0 mul0r subr0 /survival tuple_avg0.
rewrite (era_meanS kn) /=.
have p0 := p_ge0 (R := R) n k; have p1 := p_le1 (R := R) kn.
apply: lerD; apply: ler_wpM2l; rewrite ?subr_ge0 //.
- apply: le_trans (_ : clause_avg k.+1 (fun T => binom_mean p m
      (fun d => survival k.+1 (m - d + g * d) T - d%:R * eps)) S <= _).
    rewrite /clause_avg unif_mean_binom_mean; apply: ler_binom_mean => // d dm.
    rewrite unif_meanB unif_mean_cst // lerD2r subSn // addSn.
    by rewrite {1}/survival tuple_avgS.
  by apply: ler_clause_avg => T; exact: IH.
- apply: le_trans (_ : clause_avg k (fun T => binom_mean p m
      (fun d => survival k.+1 (m - d + g * d) T - d%:R * eps)) S <= _).
    rewrite /clause_avg unif_mean_binom_mean; apply: ler_binom_mean => // d dm.
    rewrite unif_meanB unif_mean_cst // subSS mulnSr addnA -nat1r mulrDl mul1r.
    rewrite opprD addrA lerD2r.
    exact: clause_avg_short_survival.
  by apply: ler_clause_avg => T; exact: IH.
Qed.

End erased_replacement.

Lemma survival_le (R : realType) n k x y (S : {set {ffun 'I_n -> bool}}) :
  (0 < #|{: clause n k}|)%N -> (x <= y)%N ->
  survival (R := R) k y S <= survival k x S.
Proof.
move=> C0 xy; rewrite -(subnK xy); elim: (y - x)%N => [|j IH] //.
by rewrite addSn; apply: le_trans IH; exact: survival_antitone.
Qed.

Section head_forcing.
Context {R : realType} (n k g : nat) (a : R).
Hypotheses (k1 : (1 <= k)%N) (kn : (k < n)%N) (a0 : 0 < a).
Hypotheses (hsmall : (n.+1%:R)^-1 <= a^-1 ^+ k) (hg : 2 * k.+1%:R * a <= g%:R).
Local Notation asg := {ffun 'I_n -> bool}.
Local Notation asg1 := {ffun 'I_n.+1 -> bool}.
Local Notation C1 := (clause n.+1 k.+1).

Let eps : R := a^-1 ^+ k.
Let p : R := k.+1%:R / n.+1%:R.
Let P (j : nat) : R := survival k.+1 j [set: asg].

Let Ck1 : (0 < #|{: clause n k.+1}|)%N.
Proof. by rewrite card_clause_gt0. Qed.

(* The probability that the first variable is forced by m clauses. *)
Definition head_forced m : R :=
  unif_mean (fun t : m.-tuple C1 =>
    (ord0 \in forced (restrict [set: asg1] t))%:R).

Lemma head_forced_mean_le m :
  head_forced m <= binom_mean p m (rep_diff P g m) + m%:R * p * eps.
Proof.
have g1 := g_ge1 a0 hg.
apply: le_trans (_ : del_mean k m [set: asg] - era_mean k m [set: asg] <= _).
  rewrite /head_forced /del_mean /era_mean -unif_meanB;
    apply: ler_unif_mean => t.
  exact: head_forced_ind.
rewrite (del_mean_binom kn).
apply: le_trans (lerB (lexx _) (era_mean_replacement k1 kn a0 hsmall hg m _)) _.
rewrite -binom_meanB.
have e d : (d <= m)%N ->
    P (m - d) - (survival k.+1 (m - d + g * d) [set: asg] - d%:R * eps) =
    rep_diff P g m d + eps * d%:R.
  move=> dm; rewrite /rep_diff /P.
  have -> : (m - d + g * d = m + (g - 1) * d)%N.
    by rewrite -{1}(subnK g1) mulnDl mul1n addnCA subnK // addnC.
  by ring.
rewrite (eq_binom_mean p e) binom_meanD binom_meanZ binom_mean_id.
by rewrite -/p -/eps lerD2l mulrC mulrA.
Qed.

Lemma integrated_head_forcing M :
  \sum_(j < M.+1) head_forced j <= g%:R * M%:R * p + M.+1%:R * M%:R * p * eps.
Proof.
have g1 := g_ge1 a0 hg.
have p0 : 0 <= p := p_ge0 (R := R) n k.
have p1 : p <= 1 := p_le1 (R := R) kn.
have e0 : 0 <= eps by rewrite exprn_ge0 // invr_ge0 ltW.
apply: le_trans (_ : \sum_(j < M.+1) (binom_mean p j (rep_diff P g j) +
    j%:R * p * eps) <= _).
  by apply: ler_sum => j _; exact: head_forced_mean_le.
rewrite big_split /=; apply: lerD.
  apply: binom_rep_sum_le => //.
  - by move=> x y xy; exact: survival_le.
  - by move=> j; exact: survival_ge0.
  - by move=> j; exact: survival_le1.
apply: le_trans (_ : \sum_(j < M.+1) (M%:R * p * eps) <= _).
  apply: ler_sum => j _; apply: ler_wpM2r => //; apply: ler_wpM2r => //.
  by rewrite ler_nat -ltnS.
rewrite sumr_const card_ord [in X in _ <= X]mulr_natl !mulrnAl; exact: lexx.
Qed.

End head_forcing.

(* Renaming the variables by a permutation preserves the uniform law of the
   clauses and moves the forced variables accordingly. *)
Section renaming.
Variables (N k : nat) (sg : {perm 'I_N}).
Local Notation asg := {ffun 'I_N -> bool}.

Definition rename_ffun (c : {ffun 'I_N -> option bool}) :
    {ffun 'I_N -> option bool} :=
  [ffun i => c (sg i)].

Lemma proper_rename (c : clause N k) : proper_clause k (rename_ffun (val c)).
Proof.
rewrite /proper_clause; apply/eqP;
  rewrite -[RHS](card_support_clause c) /support.
have -> : [set i | rename_ffun (val c) i != None] =
    sg @^-1: [set i | val c i != None].
  by apply/setP => i; rewrite !inE ffunE.
by rewrite card_preimset //; exact: perm_inj.
Qed.

Definition rename_clause (c : clause N k) : clause N k :=
  exist (fun f => proper_clause k f) _ (proper_rename c).

Definition rename_asg (s : asg) : asg := [ffun i => s (sg i)].

Lemma sat_rename (s : asg) (c : clause N k) :
  clause_sat (rename_asg s) (rename_clause c) = clause_sat s c.
Proof.
rewrite /clause_sat /=; apply/existsP/existsP => [[i]|[j]].
  by rewrite !ffunE => h; exists (sg i).
by move=> h; exists ((sg^-1)%g j); rewrite !ffunE permKV.
Qed.

Lemma rename_asg_bij : bijective rename_asg.
Proof.
exists (fun s : asg => [ffun i => s ((sg^-1)%g i)]) => s; apply/ffunP => i;
  by rewrite !ffunE ?permK ?permKV.
Qed.

End renaming.

Lemma rename_clause_bij N k (sg : {perm 'I_N}) :
  bijective (@rename_clause N k sg).
Proof.
exists (@rename_clause N k (sg^-1)%g) => c; apply: val_inj; apply/ffunP => i;
  by rewrite /= !ffunE ?permK ?permKV.
Qed.

Section forced_symmetry.
Context {R : realType} (n k : nat).
Local Notation asg1 := {ffun 'I_n.+1 -> bool}.
Local Notation C1 := (clause n.+1 k.+1).

Definition rename_tuple m (sg : {perm 'I_n.+1}) (t : m.-tuple C1) :
    m.-tuple C1 :=
  map_tuple (rename_clause sg) t.

Lemma rename_tuple_bij m sg : bijective (@rename_tuple m sg).
Proof.
have [f fK Kf] := rename_clause_bij k.+1 sg.
exists (map_tuple f) => t; apply: eq_from_tnth => i; rewrite !tnth_map.
  by rewrite fK.
by rewrite Kf.
Qed.

Lemma mem_restrict_rename m sg (t : m.-tuple C1) (s : asg1) :
  (s \in restrict [set: asg1] (rename_tuple sg t)) =
  (rename_asg (sg^-1)%g s \in restrict [set: asg1] t).
Proof.
rewrite !restrictE !inE /= all_map; apply: eq_all => c /=.
have e : rename_asg sg (rename_asg (sg^-1)%g s) = s.
  by apply/ffunP => i; rewrite !ffunE permK.
by rewrite -[in LHS]e sat_rename.
Qed.

Lemma forced_rename m sg (t : m.-tuple C1) i :
  (i \in forced (restrict [set: asg1] (rename_tuple sg t))) =
  (sg i \in forced (restrict [set: asg1] t)).
Proof.
set S := restrict [set: asg1] t;
  set S' := restrict [set: asg1] (rename_tuple sg t).
have hS (s : asg1) : (s \in S') = (rename_asg (sg^-1)%g s \in S).
  exact: mem_restrict_rename.
have hS' (s : asg1) : (rename_asg sg s \in S') = (s \in S).
  rewrite hS; congr (_ \in S); apply/ffunP => j; rewrite !ffunE permKV.
  by [].
rewrite !inE; congr andb.
  apply/idP/idP => /set0Pn [s sS]; apply/set0Pn.
    by exists (rename_asg (sg^-1)%g s); rewrite -hS.
  by exists (rename_asg sg s); rewrite hS'.
apply/existsP/existsP => -[b /forall_inP h]; exists b; apply/forall_inP => s sS.
  by have := h (rename_asg sg s); rewrite hS' ffunE => /(_ sS).
have := h (rename_asg (sg^-1)%g s); rewrite -hS ffunE => /(_ sS).
by rewrite permK.
Qed.

Lemma forced_coord_mean m (i : 'I_n.+1) :
  unif_mean (fun t : m.-tuple C1 =>
    (i \in forced (restrict [set: asg1] t))%:R) =
  head_forced (R := R) n k m.
Proof.
pose sg : {perm 'I_n.+1} := tperm ord0 i.
rewrite /head_forced -(unif_mean_bij _ (rename_tuple_bij m sg)).
by apply: eq_unif_mean => t; rewrite forced_rename tpermR.
Qed.

(* The mean fraction of forced variables. *)
Definition forced_frac m : R :=
  unif_mean (fun t : m.-tuple C1 =>
    #|forced (restrict [set: asg1] t)|%:R / n.+1%:R).

Lemma card_as_sum (A : {set 'I_n.+1}) :
  #|A|%:R = \sum_(i : 'I_n.+1) (i \in A)%:R :> R.
Proof.
rewrite -sum1_card natr_sum [LHS]big_mkcond /=.
by apply: eq_bigr => i _; case: (i \in A).
Qed.

Lemma forced_frac_head m : forced_frac m = head_forced (R := R) n k m.
Proof.
rewrite /forced_frac.
under eq_unif_mean do rewrite card_as_sum.
rewrite unif_meanZr unif_mean_sum.
under eq_bigr do rewrite forced_coord_mean.
rewrite sumr_const card_ord -[_ *+ n.+1]mulr_natr mulfK //.
by rewrite pnatr_eq0.
Qed.

End forced_symmetry.

