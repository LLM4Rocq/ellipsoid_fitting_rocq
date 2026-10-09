From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum finmap.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import ereal topology normedtype sequences esum.
From mathcomp Require Import measure lebesgue_measure numfun lebesgue_integral.
From mathcomp Require Import probability.

(**md**************************************************************************)
(* # Atoms of a finite measure                                                *)
(*                                                                            *)
(* On a measurable type whose singletons are measurable, the atoms of a       *)
(* measure P are the points of nonzero mass. A finite measure has countably   *)
(* many atoms, and a countable set without atoms is null. Hence a set of      *)
(* pairs whose vertical and horizontal sections are countable is charged by   *)
(* a product of two probabilities only above countably many points of the     *)
(* first factor, and not at all when the first factor has no atom.            *)
(*                                                                            *)
(* ```                                                                        *)
(*   atoms P == the set of the points x with P [set x] != 0                   *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - atoms_countable: the atoms of a finite measure form a countable set;     *)
(* - countable_atomless_null: a countable set none of whose points is an atom *)
(*   is null;                                                                 *)
(* - sections_charge_countable: for sets S x with S x countable for every x   *)
(*   and [set x | S x y] countable for every y, the points x with             *)
(*   P (S x) != 0 form a countable set, for a finite measure P;               *)
(* - product_sections_null: for a measure P, a probability Q and a set A of   *)
(*   pairs with countable vertical and horizontal sections, there is a        *)
(*   countable set N with (P \x Q) (A `&` (~` N `*` setT)) = 0;               *)
(* - atomless_product_null: if moreover P is a probability without atoms and  *)
(*   A is measurable, then (P \x Q) A = 0.                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section atoms.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The atoms of a set function on T: the points of nonzero mass. *)
Definition atoms (P : set T -> \bar R) := [set x : T | P [set x] != 0].

Hypothesis mT1 : forall x : T, measurable [set x].

(* A countable set none of whose points is an atom is null. *)
Lemma countable_atomless_null (P : {measure set T -> \bar R}) (C : set T) :
  countable C -> (forall x, C x -> P [set x] = 0) -> P C = 0.
Proof.
have [->|/set0P[x0 Cx0]] := eqVneq C set0; first by rewrite measure0.
move=> /countable_injP [f injf] h0.
rewrite -(injpinv_image (fun=> x0) injf).
have -> : [set 'pinv_(fun=> x0) C f x | x in [set f x | x in C]] =
    \bigcup_(n in f @` C) [set 'pinv_(fun=> x0) C f n].
  rewrite eqEsubset; split => [r [n]|r [n]].
    by move=> [t Ct ftn] Cfnr; exists n => //=; exists t.
  by move=> [t Ct ftn] /= rCfn; exists n => //=; exists t.
rewrite measure_bigcup/=.
- by move=> ? _; exact: mT1.
- move=> i j [r Cr <-] [s Cs <-].
  by rewrite !pinvKV ?inE// => -[x [/= <- <-]].
rewrite eseries0 // => n _ /set_mem [t Ct <-].
by rewrite pinvKV ?inE // h0.
Qed.

Variable P : {finite_measure set T -> \bar R}.

(* The atoms of a finite measure: the points of mass > 1 / (k + 1) are at
   most (k + 1) P(T) for every k. *)
Lemma atoms_countable : countable (atoms P).
Proof.
have fT : P setT \is a fin_num by exact: fin_num_measure.
pose A (k : nat) := [set x : T | ((k.+1%:R)^-1)%:E < P [set x]].
have -> : atoms P = \bigcup_(k in [set: nat]) A k.
  apply/seteqP; split => x /=.
  - move=> hx.
    have fx : P [set x] \is a fin_num by exact: fin_num_measure.
    have px : (0 < fine (P [set x]))%R.
      by rewrite fine_gt0 // lt0e hx measure_ge0 /= ltey_eq fx.
    exists (archimedean.Num.truncn ((fine (P [set x]))^-1)%R) => //.
    rewrite /A /= -(fineK fx) lte_fin.
    rewrite -[X in (_ < X)%R]invrK ltf_pV2 ?posrE ?invr_gt0 ?ltr0n //.
    exact: archimedean.Num.Theory.truncnS_gt.
  - move=> [k _]; rewrite /A /= => hk; apply/eqP => h0; move: hk.
    by rewrite h0 lte_fin ltNge invr_ge0 ler0n.
apply: bigcup_countable => // k _.
apply: finite_set_countable.
pose n := ((archimedean.Num.truncn (fine (P setT))).+1 * k.+1)%N.
apply: contrapT => /(infinite_set_fset n) [B BA nB].
have hU : P (\bigcup_(x in [set` B]) [set x]) =
    \sum_(x \in [set` B]) P [set x].
  apply: measure_fin_bigcup => //.
  by move=> x y _ _ [z [/= <- <-]].
have mU : measurable (\bigcup_(x in [set` B]) [set x]).
  by apply: fin_bigcup_measurable => // x _; exact: mT1.
have hle : P (\bigcup_(x in [set` B]) [set x]) <= P setT.
  by apply: le_measure; rewrite ?inE.
have hsum : ((#|` B|%:R * (k.+1%:R)^-1)%R)%:E <=
    \sum_(x \in [set` B]) P [set x].
  rewrite fsbigop.fsbig_finite //= set_fsetK.
  apply: le_trans (_ : \sum_(x <- B) ((k.+1%:R)^-1)%:E <= _).
    by rewrite sumEFin lee_fin big_const_seq count_predT iter_addr addr0 mulr_natl.
  rewrite big_seq [X in _ <= X]big_seq; apply: lee_sum => x xB.
  by apply: ltW; exact: BA.
rewrite -hU in hsum.
have := le_trans hsum hle; rewrite -(fineK fT) lee_fin => h1.
have h2 : ((archimedean.Num.truncn (fine (P setT))).+1%:R <=
    #|` B|%:R / k.+1%:R :> R)%R.
  by rewrite ler_pdivlMr // -natrM ler_nat.
have h3 := archimedean.Num.Theory.truncnS_gt (fine (P setT)).
by have := le_lt_trans (le_trans h2 h1) h3; rewrite ltxx.
Qed.

(* The points x whose set S x has positive mass. *)
Lemma sections_charge_countable (X : Type) (S : X -> set T) :
  (forall x, countable (S x)) -> (forall y, countable [set x | S x y]) ->
  countable [set x | P (S x) != 0].
Proof.
move=> cS cX.
have cU : countable (\bigcup_(y in atoms P) [set x | S x y]).
  by apply: bigcup_countable => [|y _]; [exact: atoms_countable | exact: cX].
apply: sub_countable cU; apply: subset_card_le => x /= hx.
apply: contrapT => hn; move: hx; apply/negP; rewrite negbK; apply/eqP.
apply: countable_atomless_null => // y Sy.
apply/eqP; apply: contrapT => hy; apply: hn; exists y => //.
exact/negP.
Qed.

End atoms.

Section product_atoms.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).
Context (R : realType).
Local Open Scope ereal_scope.
Hypothesis mT2 : forall y : T2, measurable [set y].

(* A product charges a set of pairs with countable sections only above
   countably many points of the first factor. *)
Lemma product_sections_null (P : {measure set T1 -> \bar R})
    (Q : probability T2 R) (A : set (T1 * T2)) :
  (forall x, countable (xsection A x)) -> (forall y, countable (ysection A y)) ->
  exists N : set T1, countable N /\ (P \x Q) (A `&` (~` N `*` setT)) = 0.
Proof.
move=> cx cy; exists [set x | Q (xsection A x) != 0]; split.
  apply: (sections_charge_countable mT2); first exact: cx.
  by move=> y; rewrite (_ : [set x | xsection A x y] = ysection A y).
rewrite /product_measure1 /=; apply: integral0_eq => x _ /=.
rewrite xsectionI.
have [Nx|Nx] := boolP (Q (xsection A x) != 0).
  by rewrite notin_xsectionX ?setI0 ?measure0 // notin_setE /= Nx.
rewrite in_xsectionX.
  by apply/mem_set => /= h; move: Nx; rewrite h.
by rewrite setIT; move/negPn/eqP: Nx.
Qed.

(* A product whose first factor has no atom does not charge a measurable set
   of pairs with countable sections. *)
Lemma atomless_product_null (P : probability T1 R) (Q : probability T2 R)
    (A : set (T1 * T2)) :
  (forall x : T1, measurable [set x]) -> (forall x, P [set x] = 0) ->
  measurable A -> (forall x, countable (xsection A x)) ->
  (forall y, countable (ysection A y)) -> (P \x Q) A = 0.
Proof.
move=> mT1 P0 mA cx cy.
have [N [cN hN]] := product_sections_null P Q cx cy.
have mN : measurable N := countable_measurable mT1 cN.
have PN : P N = 0 by apply: (countable_atomless_null mT1) => // x _; exact: P0.
have mNT : measurable (N `*` [set: T2]) by exact: measurableX.
have mNc : measurable (~` N `*` [set: T2]).
  by apply: measurableX => //; exact: measurableC.
have hA : A = (A `&` (N `*` setT)) `|` (A `&` (~` N `*` setT)).
  apply/seteqP; split => [[x y] Axy|p [[]|[]] //].
  by have [Nx|Nx] := pselect (N x); [left|right].
have m1 : measurable (A `&` (N `*` setT)) by exact: measurableI.
have m2 : measurable (A `&` (~` N `*` setT)) by exact: measurableI.
have dj : (A `&` (N `*` setT)) `&` (A `&` (~` N `*` setT)) = set0.
  by apply/seteqP; split => // -[x y] [[_ [Nx _]] [_ [Nx' _]]]; exact: Nx'.
have hU : (P \x Q) ((A `&` (N `*` setT)) `|` (A `&` (~` N `*` setT))) =
    (P \x Q) (A `&` (N `*` setT)) + (P \x Q) (A `&` (~` N `*` setT)) :=
  measureU _ m1 m2 dj.
rewrite hA hU hN adde0; apply/eqP; rewrite eq_le measure_ge0 andbT.
apply: le_trans (_ : (P \x Q) (N `*` setT) <= _).
  by apply: le_measure; rewrite ?inE //; exact: subIsetr.
have hX : (P \x Q) (N `*` setT) = P N * Q setT :=
  product_measure1E _ _ mN measurableT.
by rewrite hX PN mul0e.
Qed.

End product_atoms.
