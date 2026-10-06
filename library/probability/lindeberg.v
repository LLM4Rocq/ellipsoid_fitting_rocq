From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.

(**md**************************************************************************)
(* # The Lindeberg replacement method                                         *)
(*                                                                            *)
(* Products of probability measures on tuples, that is the laws of tuples of  *)
(* independent random elements, and Lindeberg's replacement principle         *)
(* (lindeberg_replacement): if replacing the law of one coordinate changes    *)
(* the expectation of a bounded measurable function F by at most B_i,         *)
(* uniformly in the other coordinates, then replacing all the laws changes it *)
(* by at most the sum of the B_i.                                             *)
(*                                                                            *)
(* ```                                                                        *)
(*      tuple_cons p == the tuple p.1 :: p.2 of size n.+1, for                *)
(*                      p : T * n.-tuple T                                    *)
(*  tuple_prod mu n == the product of the probability measures mu 0, ...,     *)
(*                      mu n.-1 on n.-tuple T: the law of n independent       *)
(*                      random elements with laws mu 0, ..., mu n.-1          *)
(*   tuple_set x i t == the tuple x with its coordinate i replaced by t       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_prod.
Context d (T : measurableType d) (R : realType).

Definition tuple_cons n (p : T * n.-tuple T) : n.+1.-tuple T :=
  [tuple of p.1 :: p.2].

Lemma measurable_tuple_cons n : measurable_fun setT (@tuple_cons n).
Proof. exact: (measurable_cons measurable_fst measurable_snd). Qed.

HB.instance Definition _ n :=
  isMeasurableFun.Build _ _ _ _ (@tuple_cons n) (@measurable_tuple_cons n).

Fixpoint tuple_prod (mu : nat -> probability T R) n :
    probability (n.-tuple T) R :=
  match n with
  | 0 => dirac [tuple]
  | n'.+1 => distribution (mu 0%N \x tuple_prod (fun i => mu i.+1) n')%E
      (@tuple_cons n')
  end.

End tuple_prod.

Section tuple_set.
Context (T : Type).

Definition tuple_set n (x : n.-tuple T) (i : 'I_n) (t : T) : n.-tuple T :=
  [tuple (if j == i then t else tnth x j) | j < n].

Lemma tuple_set_cons0 n (t s : T) (ts : n.-tuple T) :
  tuple_set [tuple of t :: ts] ord0 s = [tuple of s :: ts].
Proof.
apply: eq_from_tnth => j; rewrite tnth_mktuple.
case: (unliftP ord0 j) => [k ->|->]; last by rewrite eqxx (tnth_nth s).
by rewrite eq_sym (negbTE (neq_lift _ _)) !tnthS.
Qed.

Lemma tuple_set_consS n (t s : T) (ts : n.-tuple T) (i : 'I_n) :
  tuple_set [tuple of t :: ts] (lift ord0 i) s =
    [tuple of t :: tuple_set ts i s].
Proof.
apply: eq_from_tnth => j; rewrite tnth_mktuple.
case: (unliftP ord0 j) => [k ->|->].
  by rewrite !tnthS tnth_mktuple (inj_eq (@lift_inj _ ord0)).
by rewrite (negbTE (neq_lift _ _)) !(tnth_nth s).
Qed.

End tuple_set.

Section lindeberg.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma bounded_integrable d' (U : measurableType d') (P : probability U R)
    (F : U -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C)%R ->
  P.-integrable setT (EFin \o F).
Proof.
move=> mF FC; apply: measurable_bounded_integrable => //.
  by apply: le_lt_trans (probability_le1 P measurableT) _; rewrite ltry.
exists C; split; first exact: num_real.
by move=> M CM x _ /=; exact: le_trans (FC x) (ltW CM).
Qed.

Lemma measurable_tuple_set n (x : n.-tuple T) (i : 'I_n) :
  measurable_fun setT (tuple_set x i).
Proof.
apply/measurable_fun_tnthP => j /=.
rewrite (_ : _ \o _ = fun t => if j == i then t else tnth x j).
  by apply/funext => t /=; rewrite tnth_mktuple.
by case: (j == i) => //; exact: measurable_cst.
Qed.

Lemma expectation_tuple_prod0 (mu : nat -> probability T R)
    (F : 0.-tuple T -> R) :
  measurable_fun setT F -> 'E_(tuple_prod mu 0)[F] = (F [tuple])%:E.
Proof.
move=> mF; rewrite unlock /= integral_dirac ?diracT ?mul1e //.
exact/measurable_EFinP.
Qed.

Lemma expectation_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C)%R ->
  'E_(tuple_prod mu n.+1)[F] = \int[mu 0%N]_t
    'E_(tuple_prod (fun i => mu i.+1) n)[fun ts => F (tuple_cons (t, ts))].
Proof.
move=> mF FC; have mFc : measurable_fun setT (F \o @tuple_cons _ T n).
  exact: (measurableT_comp mF (@measurable_tuple_cons _ T n)).
have iFc := bounded_integrable
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n)%E mFc (fun p => FC _).
rewrite unlock /= integral_distribution //; first exact/measurable_EFinP.
by rewrite -integral12_prod_meas1.
Qed.

Lemma expectation_tuple_prodS' (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C)%R ->
  'E_(tuple_prod mu n.+1)[F] = \int[tuple_prod (fun i => mu i.+1) n]_ts
    'E_(mu 0%N)[fun t => F (tuple_cons (t, ts))].
Proof.
move=> mF FC; have mFc : measurable_fun setT (F \o @tuple_cons _ T n).
  exact: (measurableT_comp mF (@measurable_tuple_cons _ T n)).
have iFc := bounded_integrable
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n)%E mFc (fun p => FC _).
rewrite unlock /= integral_distribution //; first exact/measurable_EFinP.
by rewrite -integral21_prod_meas1.
Qed.

End lindeberg.

Section bounded_Rintegral.
Context d (U : measurableType d) (R : realType) (P : probability U R).

Lemma EFin_Rintegral_bounded (F : U -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  (\int[P]_x F x)%:E = (\int[P]_x (F x)%:E)%E.
Proof.
move=> mF FC; rewrite fineK // integrable_fin_num //.
exact: (bounded_integrable P mF FC).
Qed.

Lemma Rintegral_bounded (F : U -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) -> `|\int[P]_x F x| <= C.
Proof.
move=> mF FC; have iF := bounded_integrable P mF FC.
have iC : P.-integrable setT (EFin \o (fun=> C)).
  by apply: (bounded_integrable P (measurable_cst C) (C := `|C|)) => x.
apply: le_trans (le_normr_Rintegral measurableT iF) _.
rewrite (le_trans (le_Rintegral _ (integrable_norm iF) iC _)) //.
  by move=> x _; exact: FC.
by rewrite Rintegral_cst // [X in C * fine X]probability_setT mulr1.
Qed.

End bounded_Rintegral.

Lemma measurable_partial_Rintegral d1 d2 (U : measurableType d1)
    (V : measurableType d2) (R : realType) (m : probability U R)
    (Q : probability V R) (G : U * V -> R) (C : R) :
  measurable_fun setT G -> (forall z, `|G z| <= C) ->
  measurable_fun setT (fun u => \int[Q]_v G (u, v)).
Proof.
move=> mG GC; have iG := bounded_integrable (m \x Q)%E mG GC.
exact: measurableT_comp (measurable_fubini_F iG).
Qed.

Section lindeberg_replacement.
Context d (T : measurableType d) (R : realType).

Lemma measurable_tuple_cons_l n (t : T) :
  measurable_fun setT (fun ts : n.-tuple T => tuple_cons (t, ts)).
Proof.
exact: (measurable_cons (measurable_cst t) (@measurable_id _ _ setT)).
Qed.

Lemma measurable_tuple_cons_r n (ts : n.-tuple T) :
  measurable_fun setT (fun t : T => tuple_cons (t, ts)).
Proof.
exact: (measurable_cons (@measurable_id _ _ setT) (measurable_cst ts)).
Qed.

Lemma Rintegral_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  \int[tuple_prod mu n.+1]_x F x = \int[mu 0%N]_t
    \int[tuple_prod (fun i => mu i.+1) n]_ts F (tuple_cons (t, ts)).
Proof.
move=> mF FC; have := expectation_tuple_prodS mu mF FC; rewrite unlock => E.
rewrite /Rintegral E; congr fine; apply: eq_integral => t _.
rewrite -(EFin_Rintegral_bounded _ _ (C := C)) //.
by apply: (measurableT_comp mF); exact: measurable_tuple_cons_l.
Qed.

Lemma Rintegral_tuple_prodS' (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> R) (C : R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  \int[tuple_prod mu n.+1]_x F x = \int[tuple_prod (fun i => mu i.+1) n]_ts
    \int[mu 0%N]_t F (tuple_cons (t, ts)).
Proof.
move=> mF FC; have := expectation_tuple_prodS' mu mF FC; rewrite unlock => E.
rewrite /Rintegral E; congr fine; apply: eq_integral => ts _.
rewrite -(EFin_Rintegral_bounded _ _ (C := C)) //.
by apply: (measurableT_comp mF); exact: measurable_tuple_cons_r.
Qed.

Lemma Rintegral_tuple_prod0 (mu : nat -> probability T R)
    (F : 0.-tuple T -> R) :
  measurable_fun setT F -> \int[tuple_prod mu 0]_x F x = F [tuple].
Proof.
move=> mF; have := expectation_tuple_prod0 mu mF.
by rewrite unlock /Rintegral => ->.
Qed.

(* Lindeberg's replacement principle. *)
Lemma lindeberg_replacement n (mu nu : nat -> probability T R)
    (F : n.-tuple T -> R) (C : R) (B : nat -> R) :
  measurable_fun setT F -> (forall x, `|F x| <= C) ->
  (forall (i : 'I_n) (x : n.-tuple T),
    `|\int[mu i]_t F (tuple_set x i t) - \int[nu i]_t F (tuple_set x i t)|
      <= B i) ->
  `|\int[tuple_prod mu n]_x F x - \int[tuple_prod nu n]_x F x|
    <= \sum_(i < n) B i.
Proof.
elim: n mu nu F B => [|n IH] mu nu F B mF FC HB.
  by rewrite !Rintegral_tuple_prod0 // subrr normr0 big_ord0.
have [t0 _] : exists t0 : T, True.
  apply: contrapT => noT; have T0 : [set: T] = set0.
    by apply/seteqP; split => // t _; apply: noT; exists t.
  have := @probability_setT _ _ _ (mu 0%N).
  by rewrite T0 measure0 => /esym/eqP; rewrite onee_eq0.
set mu' := fun i => mu i.+1; set nu' := fun i => nu i.+1.
(* The hybrid law: nu 0 for the first coordinate, mu for the others. *)
pose rho := fun i => if i is 0 then nu 0%N else mu i.
have Ea := Rintegral_tuple_prodS' mu mF FC.
have Eb1 := Rintegral_tuple_prodS' rho mF FC.
have Eb2 := Rintegral_tuple_prodS rho mF FC.
have Ec := Rintegral_tuple_prodS nu mF FC.
rewrite /= in Eb1 Eb2.
have Eb : \int[tuple_prod mu' n]_ts \int[nu 0%N]_t F (tuple_cons (t, ts)) =
    \int[nu 0%N]_t \int[tuple_prod mu' n]_ts F (tuple_cons (t, ts)).
  by rewrite -Eb1 Eb2.
apply: le_trans (ler_distD
  (\int[tuple_prod mu' n]_ts \int[nu 0%N]_t F (tuple_cons (t, ts))) _ _) _.
rewrite big_ord_recl lerD //.
  (* Replacing the first coordinate costs at most B 0. *)
  have mG : measurable_fun setT
      (fun p : n.-tuple T * T => F (tuple_cons (p.2, p.1))).
    apply: (measurableT_comp mF).
    exact: (measurable_cons measurable_snd measurable_fst).
  have mI (P : probability T R) : measurable_fun setT
      (fun ts : n.-tuple T => \int[P]_t F (tuple_cons (t, ts))).
    exact: (measurable_partial_Rintegral (tuple_prod mu' n) P mG
      (fun p => FC _)).
  have bI (P : probability T R) ts : `|\int[P]_t F (tuple_cons (t, ts))| <= C.
    apply: Rintegral_bounded => //.
    by apply: (measurableT_comp mF); exact: measurable_tuple_cons_r.
  rewrite Ea -RintegralB //; try exact: (bounded_integrable _ (mI _) (bI _)).
  apply: Rintegral_bounded => [|ts]; first exact: measurable_funB (mI _) (mI _).
  have := HB ord0 [tuple of t0 :: ts].
  have E t : tuple_set [tuple of t0 :: ts] ord0 t = tuple_cons (t, ts).
    by rewrite tuple_set_cons0.
  under eq_Rintegral do rewrite E.
  by under [X in _ - X]eq_Rintegral do rewrite E.
(* Replacing the other coordinates, for each value of the first one. *)
have mG : measurable_fun setT (fun p : T * n.-tuple T => F (tuple_cons p)).
  by apply: (measurableT_comp mF); exact: measurable_tuple_cons.
have mI (P : probability (n.-tuple T) R) :
    measurable_fun setT (fun t : T => \int[P]_ts F (tuple_cons (t, ts))).
  exact: (measurable_partial_Rintegral (mu 0%N) P mG (fun p => FC _)).
have bI (P : probability (n.-tuple T) R) t :
    `|\int[P]_ts F (tuple_cons (t, ts))| <= C.
  apply: Rintegral_bounded => //.
  by apply: (measurableT_comp mF); exact: measurable_tuple_cons_l.
rewrite Eb Ec -RintegralB //; try exact: (bounded_integrable _ (mI _) (bI _)).
apply: Rintegral_bounded => [|t]; first exact: measurable_funB (mI _) (mI _).
have -> : \sum_(i < n) B (lift ord0 i) = \sum_(i < n) B i.+1 by [].
apply: (IH mu' nu' (fun ts => F (tuple_cons (t, ts))) (fun i => B i.+1)).
- by apply: (measurableT_comp mF); exact: measurable_tuple_cons_l.
- by move=> x; exact: FC.
move=> i x; have := HB (lift ord0 i) [tuple of t :: x].
have E s : tuple_set [tuple of t :: x] (lift ord0 i) s =
    tuple_cons (t, tuple_set x i s).
  by rewrite tuple_set_consS.
under eq_Rintegral do rewrite E.
by under [X in _ - X]eq_Rintegral do rewrite E.
Qed.

End lindeberg_replacement.
