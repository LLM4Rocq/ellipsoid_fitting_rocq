(* The exact Gaussian product law is invariant under permutations of the
   coordinates, for every measurable event. For s : 'S_d the reindexed tuple
   paper_main_permute_tuple s x = [tuple tnth x (s i) | i < d] is a measurable
   function of x. The boxes [set x | forall i, A i (tnth x i)] with
   measurable A i form a pi-system that contains setT and generates the tuple
   sigma-algebra (every generator tnth_i^-1 A is a box). The law of a box is
   the product of the marginal laws (gpp_boxes), and the preimage of a box
   under the permutation is the box of A o s^-1, with the same product up to
   reindexing. Measure uniqueness on a generating pi-system
   (g_sigma_algebra_measure_unique) then gives
     gaussian_product_law d (paper_main_permute_tuple s @^-1` E) =
       gaussian_product_law d E
   for every measurable E, including d = 0. No expectation transport, no
   regularity of indicators and no invariance postulate is used. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

(* The permuted tuple. *)

Definition paper_main_permute_tuple {d : nat} (s : 'S_d) (x : d.-tuple T) : d.-tuple T :=
  [tuple tnth x (s i) | i < d].

Lemma paper_main_permute_tuple_tnth {d : nat} (s : 'S_d) (x : d.-tuple T) (i : 'I_d) :
  tnth (paper_main_permute_tuple s x) i = tnth x (s i).
Proof. exact: tnth_mktuple. Qed.

Lemma paper_main_permute_tuple_measurable d (s : 'S_d) :
  measurable_fun [set: d.-tuple T] (paper_main_permute_tuple s).
Proof.
apply/measurable_fun_tnthP => i.
have -> : (@tnth d T ^~ i \o paper_main_permute_tuple s) = (@tnth d T ^~ (s i)).
  by apply: funext => x /=; rewrite paper_main_permute_tuple_tnth.
exact: measurable_tnth.
Qed.

HB.instance Definition _ d (s : 'S_d) := isMeasurableFun.Build _ _ _ _
  (@paper_main_permute_tuple d s) (paper_main_permute_tuple_measurable d s).

(* Boxes. *)

Definition paper_main_permute_box {d : nat} (A : 'I_d -> set T) : set (d.-tuple T) :=
  [set x | forall i, A i (tnth x i)].

Definition paper_main_permute_boxes (d : nat) : set (set (d.-tuple T)) :=
  [set B | exists A : 'I_d -> set T, (forall i, measurable (A i)) /\
    B = paper_main_permute_box A].

Lemma paper_main_permute_box_measurable d (A : 'I_d -> set T) :
  (forall i, measurable (A i)) -> measurable (paper_main_permute_box A).
Proof.
move=> mA.
have -> : paper_main_permute_box A =
    \bigcap_(i in [set: 'I_d]) ((@tnth d T ^~ i) @^-1` A i).
  apply/seteqP; split=> x Hx.
  - by move=> i _; exact: Hx.
  - by move=> i; exact: (Hx i I).
apply: fin_bigcap_measurable; first exact: finite_finset.
move=> i _; have := measurable_tnth i measurableT (mA i).
by rewrite setTI.
Qed.

Lemma paper_main_permute_boxes_measurable d :
  paper_main_permute_boxes d `<=` measurable.
Proof. by move=> _ [A [mA ->]]; exact: paper_main_permute_box_measurable. Qed.

Lemma paper_main_permute_boxes_setI d : setI_closed (paper_main_permute_boxes d).
Proof.
move=> _ _ [A [mA ->]] [B [mB ->]].
exists (fun i => A i `&` B i); split; first by move=> i; exact: measurableI.
by apply/seteqP; split=> x; [move=> [HA HB] i; split | move=> H; split=> i; case: (H i)].
Qed.

Lemma paper_main_permute_boxes_setT d : paper_main_permute_boxes d [set: d.-tuple T].
Proof.
exists (fun _ => setT); split; first by move=> i; exact: measurableT.
by apply/seteqP; split.
Qed.

(* Boxes generate the tuple sigma-algebra. *)

Lemma paper_main_permute_boxes_generate d (E : set (d.-tuple T)) :
  measurable E -> <<s paper_main_permute_boxes d >> E.
Proof.
rewrite /measurable /= /g_sigma_preimage; apply: sub_sigma_algebra2.
case: d E => [|d] E; first by rewrite big_ord0.
rewrite -bigcup_mkord_ord => _ [i Ii [A mA <-]].
exists (fun j : 'I_d.+1 => if j == inord i then A else setT); split.
  by move=> j; case: ifP => _ //; exact: measurableT.
apply/seteqP; split=> x /=.
- by move=> [_ HA] j; case: ifP => [/eqP -> | _] //.
- move=> H; split=> //.
  by have := H (inord i); rewrite eqxx.
Qed.

(* The law of a box and of a permuted box. *)

Lemma paper_main_permute_box_law d (A : 'I_d -> set T) :
  (forall i, measurable (A i)) ->
  gaussian_product_law d (paper_main_permute_box A) =
    ((\prod_(i < d) fine (gaussian_law (A i)))%R)%:E.
Proof.
move=> mA.
pose A' : nat -> set T := fun k => oapp A setT (insub k).
have mA' : forall k, measurable (A' k).
  by move=> k; rewrite /A'; case: insubP => [i _ _ | _] /=; [exact: mA | exact: measurableT].
have -> : paper_main_permute_box A = gpp_box d A'.
  apply/seteqP; split=> x Hx.
  - move=> k Hk; rewrite /A' insubT /= gpp_nthE.
    by have := Hx (Ordinal Hk); rewrite (tnth_nth 0%R).
  - move=> i; have := Hx i (ltn_ord i); rewrite /A' valK /= gpp_nthE.
    by rewrite (tnth_nth 0%R).
rewrite (gpp_boxes d A' mA'); congr (_%:E).
by apply: eq_bigr => i _; rewrite /A' valK.
Qed.

Lemma paper_main_permute_box_preimage d (s : 'S_d) (A : 'I_d -> set T) :
  paper_main_permute_tuple s @^-1` paper_main_permute_box A =
  paper_main_permute_box (fun j => A ((s^-1)%g j)).
Proof.
apply/seteqP; split=> x Hx j /=.
- have := Hx ((s^-1)%g j); rewrite /= paper_main_permute_tuple_tnth permKV.
  by [].
- by rewrite paper_main_permute_tuple_tnth; have := Hx (s j); rewrite permK.
Qed.

(* The permutation law. *)

Theorem paper_main_permute_tuple_law d (s : 'S_d) (E : set (d.-tuple T)) :
  measurable E ->
  gaussian_product_law d (paper_main_permute_tuple s @^-1` E) = gaussian_product_law d E.
Proof.
move=> mE.
pose m2 := distribution (gaussian_product_law d) (paper_main_permute_tuple s).
have Hagree : forall B, paper_main_permute_boxes d B ->
    gaussian_product_law d B = m2 B.
  move=> _ [A [mA ->]].
  rewrite /m2 /distribution /pushforward paper_main_permute_box_preimage.
  rewrite (paper_main_permute_box_law _ _ mA).
  rewrite (paper_main_permute_box_law _ (fun j => A ((s^-1)%g j)) (fun j => mA _)).
  congr (_%:E); rewrite [RHS](reindex_inj (@perm_inj _ s)) /=.
  by apply: eq_bigr => i _; rewrite permK.
have Hfin : forall k : nat, (gaussian_product_law d [set: d.-tuple T] < +oo)%E.
  by move=> _; rewrite gpp_mass ltry.
have H := @g_sigma_algebra_measure_unique _ _ _ (paper_main_permute_boxes d)
  (paper_main_permute_boxes_measurable d) (fun _ => setT)
  (fun _ => paper_main_permute_boxes_setT d) (bigcup_const _ _)
  (gaussian_product_law d) m2 (paper_main_permute_boxes_setI d) Hagree
  Hfin E (paper_main_permute_boxes_generate d E mE).
by rewrite H.
Qed.
