From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum finfun.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences esum exp.
From mathcomp Require Import cardinality.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import numfun lebesgue_integral probability.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.probability Require Import mixture.

(**md**************************************************************************)
(* # Countable mixtures of probabilities                                      *)
(*                                                                            *)
(* The mixture of probabilities P s, s : nat, with weights p s >= 0 of sum    *)
(* one, and the sums over the tuples of labels that describe n independent    *)
(* draws from it. The weights are a proof argument of the mixture, as in      *)
(* probability/mixture.v.                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*     cmixture_weights p == p s >= 0 for every s and \sum_(s <oo) p s = 1    *)
(*          cmixture P hp == for hp : cmixture_weights p, the probability     *)
(*                           A |-> \sum_(s <oo) p s P s (A)                   *)
(*      cmixture_tail p m == r_m = \sum_(s > m) p s, the weight of the        *)
(*                           labels above m                                   *)
(*  cmixture_tail_w p m s == p s / r_m for s > m and 0 otherwise, the weights *)
(*                           of the normalized tail                           *)
(*          labels_le n m == the n-tuples of labels in nat that are all <= m  *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - cmixtureE: cmixture P hp A = \sum_(s <oo) p s P s (A); the mixture is    *)
(*   the measure series mseries of the scaled probabilities p s P s;          *)
(* - ge0_integral_cmixture, integral_cmixture: \int f d(cmixture P hp) =      *)
(*   \sum_s p s \int f dP_s for f nonnegative and measurable, and for f       *)
(*   integrable under every P s with \sum_s p s \int |f| dP_s < +oo, which    *)
(*   is then integrable under the mixture (from                               *)
(*   ge0_integral_measure_series and integral_measure_series);                *)
(* - cmixture_tailE, cmixture_tail_small, cmixture_tail_series,               *)
(*   cmixture_tail_weights: \sum_(s <= m) p s + r_m = 1, r_m tends to 0,      *)
(*   and for r_m > 0 the normalized tail weights are mixture weights, so      *)
(*   that cmixture P with them is the normalized tail                         *)
(*   \sum_(s > m) p s P s / r_m;                                              *)
(* - esumZl, esum_fin, esum_tuple_prod: an esum of nonnegative terms          *)
(*   commutes with a nonnegative factor; over a subset of a finite type it    *)
(*   is a finite sum; the esum over s : n.-tuple nat of \prod_i a (s_i) is    *)
(*   the n-th power of the esum of a;                                         *)
(* - label_esum1, label_esum_le: the product weights \prod_i p (s_i) of the   *)
(*   label tuples have sum one, and sum (1 - r_m)^n over labels_le n m;       *)
(* - label_coupling, bernoulli_tail: an esum over the label tuples in nat     *)
(*   and a finite sum over the label tuples in 'I_N, of product weights       *)
(*   times probabilities, whose weights and probabilities agree on the        *)
(*   tuples with all labels at most m, differ by at most                      *)
(*   1 - (1 - r_m)^n <= n r_m on every measurable set.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Weights p s >= 0, s : nat, of sum one. *)
Definition cmixture_weights (R : realType) (p : nat -> R) : Prop :=
  (forall s, 0 <= p s) /\ (\sum_(s <oo) (p s)%:E = 1)%E.

Section countable_mixture.
Context d (T : measurableType d) (R : realType).
Variables (P : nat -> probability T R) (p : nat -> R).
Local Open Scope ereal_scope.

Definition cmixture (hp : cmixture_weights p) (A : set T) : \bar R :=
  \sum_(s <oo) (p s)%:E * P s A.

Variable hp : cmixture_weights p.

Let p0 s : (0 <= p s)%R. Proof. exact: hp.1. Qed.

Let mterm (s : nat) : {measure set T -> \bar R} := mscale (NngNum (p0 s)) (P s).

Let cmixture_mseries A : cmixture hp A = mseries mterm 0 A.
Proof. by []. Qed.

Let cmixture0 : cmixture hp set0 = 0.
Proof. by rewrite cmixture_mseries measure0. Qed.

Let cmixture_ge0 A : 0 <= cmixture hp A.
Proof. by rewrite cmixture_mseries measure_ge0. Qed.

Let cmixture_sigma_additive : semi_sigma_additive (cmixture hp).
Proof.
have -> : cmixture hp = mseries mterm 0 := funext cmixture_mseries.
exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (cmixture hp)
  cmixture0 cmixture_ge0 cmixture_sigma_additive.

Let cmixture_setT : cmixture hp [set: T] = 1.
Proof.
rewrite /cmixture -hp.2; apply: eq_eseriesr => s _.
by rewrite probability_setT mule1.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R (cmixture hp) cmixture_setT.

Lemma cmixtureE A : cmixture hp A = \sum_(s <oo) (p s)%:E * P s A.
Proof. by []. Qed.

Lemma ge0_integral_cmixture (D : set T) (f : T -> \bar R) :
  measurable D -> measurable_fun D f -> (forall x, D x -> 0 <= f x) ->
  \int[cmixture hp]_(x in D) f x =
  \sum_(s <oo) (p s)%:E * \int[P s]_(x in D) f x.
Proof.
move=> mD mf f0.
rewrite (eq_measure_integral (mseries mterm 0)); try
  by move=> A mA _; exact: cmixture_mseries.
rewrite ge0_integral_measure_series //.
by apply: eq_eseriesr => s _; rewrite ge0_integral_mscale.
Qed.

Lemma integral_cmixture (D : set T) (f : T -> \bar R) : measurable D ->
  measurable_fun D f -> (forall s, (P s).-integrable D f) ->
  \sum_(s <oo) (p s)%:E * \int[P s]_(x in D) `|f x| < +oo ->
  (cmixture hp).-integrable D f /\
  \int[cmixture hp]_(x in D) f x =
  \sum_(s <oo) (p s)%:E * \int[P s]_(x in D) f x.
Proof.
move=> mD mf fi fs.
have ma : measurable_fun D (fun x => `|f x|) by exact: measurableT_comp.
have ab s : \int[mterm s]_(x in D) `|f x| =
    (p s)%:E * \int[P s]_(x in D) `|f x|.
  by rewrite ge0_integral_mscale.
have fin s : \int[P s]_(x in D) `|f x| \is a fin_num.
  have /integrableP[_ h] := fi s.
  by rewrite ge0_fin_numE // integral_ge0.
have mi s : (mterm s).-integrable D f.
  apply/integrableP; split => //; rewrite ab.
  by rewrite -(fineK (fin s)) -EFinM ltry.
split.
  apply/integrableP; split => //.
  by rewrite ge0_integral_cmixture.
rewrite (eq_measure_integral (mseries mterm 0)); try
  by move=> A mA _; exact: cmixture_mseries.
have mfp : measurable_fun D f^\+ by exact: measurable_funepos.
have mfn : measurable_fun D f^\- by exact: measurable_funeneg.
have lepos x : f^\+ x <= `|f x|.
  by rewrite -/((abse \o f) x) fune_abse /= leeDl.
have leneg x : f^\- x <= `|f x|.
  by rewrite -/((abse \o f) x) fune_abse /= leeDr.
have bnd (g : T -> \bar R) : measurable_fun D g -> (forall x, 0 <= g x) ->
    (forall x, g x <= `|f x|) ->
    \sum_(s <oo) `|\int[mterm s]_(x in D) g x| < +oo.
  move=> mg g0 gf; apply: le_lt_trans fs.
  apply: lee_nneseries => [s _ _|s _]; first exact: abse_ge0.
  have ig : 0 <= \int[mterm s]_(x in D) g x.
    by apply: integral_ge0 => x _; exact: g0.
  have g0D : forall x, D x -> 0 <= g x by move=> x _; exact: g0.
  rewrite gee0_abs // ge0_integral_mscale //.
  apply: lee_wpmul2l; first by rewrite lee_fin.
  by apply: ge0_le_integral => // x _; exact: gf.
rewrite (integral_measure_series mD mi mf
  (bnd _ mfn (fun x => funeneg_ge0 f x) leneg)
  (bnd _ mfp (fun x => funepos_ge0 f x) lepos)).
apply: eq_eseriesr => s _.
have fp0 : forall x, D x -> 0 <= f^\+ x by move=> x _; exact: funepos_ge0.
have fn0 : forall x, D x -> 0 <= f^\- x by move=> x _; exact: funeneg_ge0.
rewrite (integralE (mterm s) D f) (integralE (P s) D f).
rewrite (ge0_integral_mscale (P s) mD (NngNum (p0 s)) mfp fp0).
rewrite (ge0_integral_mscale (P s) mD (NngNum (p0 s)) mfn fn0) /=.
have fpf : \int[P s]_(x in D) f^\+ x \is a fin_num.
  have i0 : 0 <= \int[P s]_(x in D) f^\+ x by apply: integral_ge0.
  rewrite ge0_fin_numE //; exact: (integral_funepos_lt_pinfty mD (fi s)).
rewrite [RHS]muleBr //; apply: fin_num_adde_defr; exact: fpf.
Qed.

End countable_mixture.

Section countable_tail.
Context (R : realType) (p : nat -> R).
Hypothesis hp : cmixture_weights p.
Local Open Scope ereal_scope.

Let p0 s : (0 <= p s)%R. Proof. exact: hp.1. Qed.

(* The mass of the labels s > m. *)
Definition cmixture_tail (m : nat) : R :=
  fine (\sum_(s <oo | (m < s)%N) (p s)%:E).

Lemma cmixture_tailE (m : nat) :
  \sum_(s <oo | (m < s)%N) (p s)%:E = (cmixture_tail m)%:E /\
  (\sum_(s < m.+1) p s + cmixture_tail m = 1)%R.
Proof.
have pe0 k : (0 <= k)%N -> 0 <= (p k)%:E by move=> _; rewrite lee_fin.
have := @nneseries_split R (fun k => (p k)%:E) 0 m.+1 pe0.
rewrite hp.2 add0n ereal_series => hsplit.
have t0 : 0 <= \sum_(s <oo | (m < s)%N) (p s)%:E.
  by apply: nneseries_ge0 => k _ _; rewrite lee_fin.
have h0 : 0 <= (\sum_(0 <= k < m.+1) (p k)%:E)%R.
  by apply: sume_ge0 => k _; rewrite lee_fin.
have tf : \sum_(s <oo | (m < s)%N) (p s)%:E \is a fin_num.
  rewrite ge0_fin_numE //; apply: (@le_lt_trans _ _ 1); last exact: ltry.
  by rewrite hsplit leeDr.
split; first by rewrite /cmixture_tail fineK.
apply: EFin_inj; rewrite EFinD -sumEFin /cmixture_tail fineK //.
by rewrite (big_mkord xpredT) in hsplit; rewrite hsplit.
Qed.

(* The tail mass tends to zero: it is at most any eps > 0 from some m on. *)
Lemma cmixture_tail_small (eps : R) : (0 < eps)%R ->
  exists m, (cmixture_tail m <= eps)%R.
Proof.
move=> e0; apply: contrapT => hno.
have hgt m : (eps < cmixture_tail m)%R.
  by rewrite ltNge; apply/negP => h; apply: hno; exists m.
have hlt m : (\sum_(k < m.+1) p k <= 1 - eps)%R.
  by have [_ hh] := cmixture_tailE m; have := hgt m; lra.
have hs0 : (0 <= \sum_(k < 1) p k)%R by apply: sumr_ge0 => k _; exact: p0.
have : (\sum_(k <oo) (p k)%:E <= (1 - eps)%:E)%E.
  apply: lime_le; first by apply: is_cvg_nneseries => k _ _; rewrite lee_fin.
  apply: nearW => n; case: n => [|n].
    by rewrite big_geq // lee_fin; have := hlt 0%N; lra.
  by rewrite sumEFin lee_fin big_mkord; exact: hlt.
by rewrite hp.2 lee_fin; lra.
Qed.

(* The normalized tail: the weights p s / r_m for s > m, and 0 for s <= m. *)
Definition cmixture_tail_w (m s : nat) : R :=
  (if (m < s)%N then p s / cmixture_tail m else 0)%R.

Lemma cmixture_tail_series m (F : nat -> \bar R) : (0 < cmixture_tail m)%R ->
  (forall s, 0 <= F s) ->
  \sum_(s <oo) (cmixture_tail_w m s)%:E * F s =
  ((cmixture_tail m)^-1)%:E * \sum_(s <oo | (m < s)%N) (p s)%:E * F s.
Proof.
move=> r0 F0.
have fF0 s : (m < s)%N -> 0 <= (p s)%:E * F s.
  by move=> _; rewrite mule_ge0 // lee_fin.
rewrite -nneseriesZl // [RHS]eseries_mkcond; apply: eq_eseriesr => s _.
rewrite /cmixture_tail_w; case: ifP => ms; last by rewrite mul0e.
by rewrite muleA -EFinM mulrC.
Qed.

Lemma cmixture_tail_weights m : (0 < cmixture_tail m)%R ->
  cmixture_weights (cmixture_tail_w m).
Proof.
move=> r0; split => [s|].
  rewrite /cmixture_tail_w; case: ifP => _ //.
  by apply: divr_ge0; [exact: p0 | exact: ltW].
have := cmixture_tail_series (F := fun=> 1) r0 (fun=> lee01).
under eq_eseriesr do rewrite mule1.
move=> ->; have [h _] := cmixture_tailE m.
under eq_eseriesr do rewrite mule1.
by rewrite h -EFinM mulVf // gt_eqF.
Qed.

End countable_tail.

Section label_sums.
Context (R : realType).
Local Open Scope ereal_scope.

Lemma esumZl (I : choiceType) (S : set I) (a : I -> \bar R) (c : R) :
  (0 <= c)%R -> (forall i, S i -> 0 <= a i) ->
  \esum_(i in S) (c%:E * a i) = c%:E * \esum_(i in S) a i.
Proof.
move=> c0 a0.
have ne : [set \sum_(x \in A) a x | A in fsets S] != set0.
  apply/set0P; exists 0; exists set0; first exact: fsets_set0.
  by rewrite fsbigop.fsbig_set0.
have dis (X : set I) : finite_set X -> X `<=` S ->
    (\sum_(x \in X) c%:E * a x) = c%:E * \sum_(x \in X) a x.
  move=> finX XS; rewrite !fsbigop.fsbig_finite //=.
  rewrite big_seq [in RHS]big_seq ge0_sume_distrr // => i.
  by rewrite cardinality.in_fset_set // inE => /XS; exact: a0.
rewrite /esum -ereal_supZl //.
congr ereal_sup; apply/seteqP; split => y /=.
  move=> [X [finX XS] <-]; exists (\sum_(x \in X) a x); first by exists X.
  by rewrite dis.
by move=> [z [X [finX XS] <-] <-]; exists X => //; rewrite dis.
Qed.

(* The sum over the n-tuples of labels of the product weights is the n-th
   power of the sum of the weights. *)
Lemma esum_tuple_prod (a : nat -> R) (x : R) (n : nat) :
  (forall k, (0 <= a k)%R) -> \esum_(k in [set: nat]) (a k)%:E = x%:E ->
  \esum_(s in [set: n.-tuple nat]) (\prod_(i < n) a (tnth s i))%:E =
  (x ^+ n)%:E.
Proof.
move=> a0 hx.
have x0 : (0 <= x)%R.
  by rewrite -lee_fin -hx; apply: esum_ge0 => k _; rewrite lee_fin.
elim: n => [|n IH].
  have -> : [set: 0.-tuple nat] = [set [tuple]].
    by apply/seteqP; split => s //= _; rewrite tuple0.
  by rewrite esum_set1 ?big_ord0 ?expr0 // lee_fin big_ord0.
pose e (st : nat * n.-tuple nat) : n.+1.-tuple nat := cons_tuple st.1 st.2.
have be : set_bij [set: nat * n.-tuple nat] [set: n.+1.-tuple nat] e.
  split; first by move=> st.
    by move=> [a1 t1] [a2 t2] _ _ /= /(congr1 val) /= [-> /val_inj ->].
  move=> s _; exists (thead s, behead_tuple s) => //.
  by rewrite /e /= [RHS]tuple_eta.
rewrite (reindex_esum _ _ _ _ be).
have -> : [set: nat * n.-tuple nat] =
    [set: nat] `*`` (fun=> [set: n.-tuple nat]).
  by apply/seteqP; split => st.
have hnn (k : nat) (t : n.-tuple nat) : [set: nat] k ->
    [set: n.-tuple nat] t -> 0 <= (\prod_(i < n.+1) a (tnth (e (k, t)) i))%:E.
  by move=> _ _; rewrite lee_fin; apply: prodr_ge0 => i _; exact: a0.
rewrite -(esum_esum (a := fun (k : nat) (t : n.-tuple nat) =>
  (\prod_(i < n.+1) a (tnth (e (k, t)) i))%:E)) //.
have hn0 (t : n.-tuple nat) : [set: n.-tuple nat] t ->
    0 <= (\prod_(i < n) a (tnth t i))%:E.
  by move=> _; rewrite lee_fin; apply: prodr_ge0 => i _; exact: a0.
have inner k : \esum_(t in [set: n.-tuple nat])
    (\prod_(i < n.+1) a (tnth (e (k, t)) i))%:E = (x ^+ n)%:E * (a k)%:E.
  rewrite -IH muleC -(esumZl (a0 k) hn0); apply: eq_esum => t _.
  rewrite big_ord_recl -EFinM; congr (_ * _)%:E.
  by apply: eq_bigr => i _; rewrite /e tnthS.
rewrite (eq_esum (fun k _ => inner k)).
have ha0 (k : nat) : [set: nat] k -> 0 <= (a k)%:E.
  by move=> _; rewrite lee_fin.
by rewrite (esumZl (exprn_ge0 n x0) ha0) hx -EFinM -exprSr.
Qed.

(* An esum over a subset of a finite type is a finite sum. *)
Lemma esum_fin (T : finType) (P : pred T) (a : T -> \bar R) :
  (forall t, P t -> 0 <= a t) ->
  \esum_(t in [set t | P t]) a t = \sum_(t | P t) a t.
Proof.
move=> a0.
have fin : finite_set [set t | P t] := finite_finset.
have nn i : i \in [set t | P t] -> 0 <= a i.
  by rewrite inE; exact: a0.
rewrite esum_fset // (fsbigop.fsbigE [seq t <- enum T | P t]).
- by rewrite filter_uniq // enum_uniq.
- by move=> t /=; rewrite mem_filter => /andP[].
- by move=> t /= Pt; rewrite mem_filter Pt mem_enum.
rewrite big_filter_cond big_enum_cond /=; apply: eq_bigl => t.
by rewrite mem_setE andbb.
Qed.

(* Bernoulli's inequality, as used for the mass of the label tuples with
   some label above m. *)
Lemma bernoulli_tail (r : R) (n : nat) : (0 <= r <= 1)%R ->
  (1 - (1 - r) ^+ n <= n%:R * r)%R.
Proof.
move=> /andP[r0 r1].
elim: n => [|n IH]; first by rewrite expr0 subrr mul0r.
have h1 : (0 <= (1 - r) ^+ n)%R by rewrite exprn_ge0 // subr_ge0.
have h2 : ((1 - r) ^+ n <= 1)%R.
  by apply: exprn_ile1; rewrite ?subr_ge0 // lerBlDr lerDl.
by rewrite exprSr -natr1; nra.
Qed.

End label_sums.

Section label_weights.
Context (R : realType) (p : nat -> R).
Hypothesis hp : cmixture_weights p.
Local Open Scope ereal_scope.

Lemma cmixture_weights_esum : \esum_(k in [set: nat]) (p k)%:E = 1.
Proof. by rewrite -nneseries_esumT ?hp.2 // => k; rewrite lee_fin hp.1. Qed.

(* The label tuples s : n.-tuple nat: the product weights have sum one. *)
Lemma label_esum1 n :
  \esum_(s in [set: n.-tuple nat]) (\prod_(i < n) p (tnth s i))%:E = 1.
Proof. by rewrite (esum_tuple_prod n hp.1 cmixture_weights_esum) expr1n. Qed.

(* The label tuples whose labels are all at most m. *)
Definition labels_le (n m : nat) : set (n.-tuple nat) :=
  [set s | all (fun k => (k <= m)%N) s].
Arguments labels_le : clear implicits.

Lemma label_esum_le n m :
  \esum_(s in labels_le n m) (\prod_(i < n) p (tnth s i))%:E =
  ((1 - cmixture_tail p m) ^+ n)%:E.
Proof.
pose a k := if (k <= m)%N then p k else 0%R.
have a0 k : (0 <= a k)%R by rewrite /a; case: ifP => _ //; exact: hp.1.
have ae0 k : (0 <= k)%N -> 0 <= (a k)%:E by move=> _; rewrite lee_fin.
have ha : \esum_(k in [set: nat]) (a k)%:E = (1 - cmixture_tail p m)%:E.
  have aT k : 0 <= (a k)%:E by rewrite lee_fin.
  rewrite -nneseries_esumT //.
  rewrite (@nneseries_split R (fun k => (a k)%:E) 0 m.+1 ae0) add0n.
  have hz : \sum_(m.+1 <= k <oo) (a k)%:E = 0.
    by apply: eseries0 => k mk _; rewrite /a leqNgt mk.
  rewrite hz adde0.
  have [_ hh] := cmixture_tailE hp m.
  rewrite sumEFin big_mkord; congr EFin.
  rewrite -hh addrK; apply: eq_bigr => k _.
  by rewrite /a -ltnS ltn_ord.
rewrite -(esum_tuple_prod n a0 ha) esum_mkcond.
apply: eq_esum => s _.
have mem : (s \in labels_le n m) = all (fun k => (k <= m)%N) s.
  by apply/idP/idP => [|h]; rewrite inE.
rewrite mem; case: ifP => hs.
  congr EFin; apply: eq_bigr => i _; rewrite /a.
  have hi : (tnth s i <= m)%N by move/allP: hs; apply; exact: mem_tnth.
  by rewrite hi.
move/negbT: hs; rewrite -has_predC => /hasP [x xs /= xm].
have /tnthP [i xi] := xs.
by rewrite (bigD1 i) //= /a -xi (negbTE xm) mul0r.
Qed.

(* The coupling of label tuples. A mixture over the tuples s of labels in
   nat, with the product weights of p, and a mixture over the tuples t of
   labels in 'I_N, with the product weights of q, whose weights and laws
   agree on the tuples with all labels at most m, differ by at most the
   mass 1 - (1 - r_m)^n of the tuples with some label above m. *)
Lemma label_coupling dT (T : measurableType dT) (n m N : nat) (q : nat -> R)
    (Q : n.-tuple nat -> probability T R)
    (Q' : n.-tuple 'I_N -> probability T R) (A : set T) :
  measurable A -> (m < N)%N ->
  (forall k, (k < N)%N -> (0 <= q k)%R) -> (\sum_(k < N) q k = 1)%R ->
  (forall k, (k <= m)%N -> q k = p k) ->
  (forall t : n.-tuple 'I_N, all (fun k : 'I_N => (k <= m)%N) t ->
     Q' t A = Q (map_tuple (@nat_of_ord N) t) A) ->
  `|\esum_(s in [set: n.-tuple nat]) (\prod_(i < n) p (tnth s i))%:E * Q s A
    - \sum_(t : n.-tuple 'I_N) (\prod_(i < n) q (tnth t i))%:E * Q' t A|
  <= (1 - (1 - cmixture_tail p m) ^+ n)%:E.
Proof.
move=> mA mN q0 q1 qp QQ.
set r := cmixture_tail p m.
set w := fun s : n.-tuple nat => (\prod_(i < n) p (tnth s i))%:E.
set w' := fun t : n.-tuple 'I_N => (\prod_(i < n) q (tnth t i))%:E.
have w0 s : 0 <= w s by rewrite lee_fin; apply: prodr_ge0 => i _; exact: hp.1.
have w'0 t : 0 <= w' t.
  by rewrite lee_fin; apply: prodr_ge0 => i _; exact: q0.
have F0 s : 0 <= w s * Q s A by rewrite mule_ge0.
have F'0 t : 0 <= w' t * Q' t A by rewrite mule_ge0.
have Fle s : w s * Q s A <= w s.
  rewrite -[X in _ <= X]mule1; apply: lee_wpmul2l => //.
  exact: probability_le1.
have F'le t : w' t * Q' t A <= w' t.
  rewrite -[X in _ <= X]mule1; apply: lee_wpmul2l => //.
  exact: probability_le1.
set L := labels_le n m.
(* the label tuples of nat with some label above m *)
have WC : \esum_(s in ~` L) w s = (1 - (1 - r) ^+ n)%:E.
  have h := esumID L [set: n.-tuple nat] w (fun s _ => w0 s).
  rewrite !setTI /w (label_esum1 n) (label_esum_le n m) -/r in h.
  have c0 : 0 <= \esum_(s in ~` L) w s by apply: esum_ge0 => s _; exact: w0.
  have cf : \esum_(s in ~` L) w s \is a fin_num.
    rewrite ge0_fin_numE //; apply: (@le_lt_trans _ _ 1); last exact: ltry.
    have r1 : (0 <= 1 - r)%R.
      have [_ hh] := cmixture_tailE hp m; rewrite -/r in hh.
      by rewrite -hh addrK; apply: sumr_ge0 => k _; exact: hp.1.
    by rewrite [X in _ <= X]h /w leeDr // lee_fin exprn_ge0.
  have h' : 1 = ((1 - r) ^+ n)%:E + \esum_(s in ~` L) w s := h.
  have e1 : (1 - (1 - r) ^+ n)%:E = 1 - ((1 - r) ^+ n)%:E by rewrite EFinB.
  by rewrite e1 [X in _ = X - _]h' addeAC subee // add0e.
(* the label tuples of 'I_N with some label above m *)
have headq : (\sum_(k < N | (k <= m)%N) q k = 1 - r)%R.
  have [_ hh] := cmixture_tailE hp m; rewrite -/r in hh.
  rewrite -hh addrK (big_ord_widen_cond N xpredT p mN) /=.
  by apply: eq_bigr => k km; rewrite qp.
pose Lp (t : n.-tuple 'I_N) := all (fun k : 'I_N => (k <= m)%N) t.
have totq : (\sum_(t : n.-tuple 'I_N) \prod_(i < n) q (tnth t i) = 1)%R.
  rewrite (big_tuple_distr (fun (_ : 'I_n) (k : 'I_N) => q k)).
  by rewrite (eq_bigr (fun _ => 1%R)) ?big1_eq // => i _; exact: q1.
have Lq : (\sum_(t | Lp t) \prod_(i < n) q (tnth t i) = (1 - r) ^+ n)%R.
  rewrite -headq big_mkcond /=.
  have pc (x : R) : (x ^+ n = \prod_(k < n) x)%R.
    by rewrite prodr_const card_ord.
  rewrite pc [X in (\prod_(k < n) X)%R]big_mkcond /=.
  rewrite -(big_tuple_distr (fun (_ : 'I_n) (i : 'I_N) =>
    if (i <= m)%N then q i else 0%R)).
  apply: eq_bigr => t _; rewrite /Lp; case: ifP => ht.
    apply: eq_bigr => i _.
    have hi : (tnth t i <= m)%N by move/allP: ht; apply; exact: mem_tnth.
    by rewrite hi.
  move/negbT: ht; rewrite -has_predC => /hasP [x xs /= xm].
  have /tnthP [i xi] := xs.
  by rewrite (bigD1 i) //= -xi (negbTE xm) mul0r.
have W'C : (\sum_(t | ~~ Lp t) \prod_(i < n) q (tnth t i) =
    1 - (1 - r) ^+ n)%R.
  by move: totq; rewrite (bigID Lp) /= Lq => h; lra.
(* the label tuples with all labels at most m *)
pose e (t : n.-tuple 'I_N) : n.-tuple nat := map_tuple (@nat_of_ord N) t.
have be : set_bij [set t | Lp t] L e.
  split.
  - by move=> t /= ht; rewrite /L /labels_le /= /e /= all_map.
  - move=> t1 t2 _ _ /(congr1 val) /= /(inj_map val_inj) h.
    exact: val_inj.
  - move=> s /= hs.
    have sN (k : nat) : k \in s -> (k < N)%N.
      by move=> ks; have := allP hs k ks; move/leq_ltn_trans; apply.
    exists [tuple of [seq insubd (Ordinal mN) k | k <- s]].
      rewrite /= /Lp all_map; apply/allP => k ks /=.
      by rewrite val_insubd sN //; exact: (allP hs).
    apply: val_inj; rewrite /e /= -map_comp.
    by apply: map_id_in => k ks /=; rewrite val_insubd sN.
have XL : \esum_(s in L) w s * Q s A = \sum_(t | Lp t) w' t * Q' t A.
  have Fp t : Lp t -> 0 <= w (e t) * Q (e t) A by move=> _; exact: F0.
  rewrite (reindex_esum _ _ _ _ be) (esum_fin Fp).
  apply: eq_bigr => t ht.
  rewrite QQ //; congr (_ * _).
  rewrite /w /w'; congr EFin; apply: eq_bigr => i _.
  rewrite /e tnth_map qp //.
  by move/allP: ht; apply; exact: mem_tnth.
(* the two mixtures differ only on the tuples with some label above m *)
have hX : \esum_(s in [set: n.-tuple nat])
    (\prod_(i < n) p (tnth s i))%:E * Q s A =
    \esum_(s in L) w s * Q s A + \esum_(s in ~` L) w s * Q s A.
  have := esumID L [set: n.-tuple nat] (fun s => w s * Q s A)
    (fun s _ => F0 s).
  by rewrite !setTI.
have hY : \sum_(t : n.-tuple 'I_N) (\prod_(i < n) q (tnth t i))%:E * Q' t A =
    \sum_(t | Lp t) w' t * Q' t A + \sum_(t | ~~ Lp t) w' t * Q' t A.
  exact: (bigID Lp).
rewrite hX hY XL.
set c := \sum_(t | Lp t) w' t * Q' t A.
set a := \esum_(s in ~` L) w s * Q s A.
set b := \sum_(t | ~~ Lp t) w' t * Q' t A.
have a0 : 0 <= a by apply: esum_ge0 => s _; exact: F0.
have b0 : 0 <= b by apply: sume_ge0 => t _; exact: F'0.
have c0 : 0 <= c by apply: sume_ge0 => t _; exact: F'0.
have aD : a <= (1 - (1 - r) ^+ n)%:E.
  by rewrite -WC; apply: le_esum => s _; exact: Fle.
have bD : b <= (1 - (1 - r) ^+ n)%:E.
  rewrite -W'C -sumEFin; apply: lee_sum => t _; exact: F'le.
have cD : c <= ((1 - r) ^+ n)%:E.
  rewrite -Lq -sumEFin; apply: lee_sum => t _; exact: F'le.
have fin (x : \bar R) (y : R) : 0 <= x -> x <= y%:E -> x \is a fin_num.
  by move=> x0 xy; rewrite ge0_fin_numE // (le_lt_trans xy) ?ltry.
have af := fin _ _ a0 aD.
have bf := fin _ _ b0 bD.
have cf := fin _ _ c0 cD.
move: a0 b0 aD bD; rewrite -(fineK af) -(fineK bf) -(fineK cf) !lee_fin.
move=> a0 b0 aD bD.
by rewrite opprD addrACA subrr add0r ler_norml; apply/andP; split; lra.
Qed.

End label_weights.
