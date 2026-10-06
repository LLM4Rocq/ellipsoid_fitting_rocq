(* Elementary facts about gaussian_product_law d, the law of d independent
   standard normal coordinates on d-tuples. In dimension 0, integration is
   evaluation at nil (gpp_zero_integral). The coordinates are measurable
   (gpp_coordinate_measurable), and the box gpp_box d A of the tuples whose
   coordinate i lies in A i is measurable, with measure the product of the
   gaussian_law (A i) (gpp_boxes). gpp_cons_measurable transfers
   measurability from (S d)-tuples to pairs (head, tail). *)
From Stdlib Require Import Reals List.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import cardinality.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import measurable_realfun.
From EllipsoidFitting Require Import GaussianProbabilityDefinitions GaussianProbabilityProductDefinitions.
Import GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma gpp_zero_tuple (x : 0.-tuple (measurableTypeR R)) : tval x = nil.
Proof. by have := size_tuple x; case: (tval x). Qed.

Lemma gpp_zero_integral (F : list R -> R) :
  (\int[gaussian_product_law 0]_x (F (tval x))%:E = (F nil)%:E)%E.
Proof.
under eq_integral do rewrite gpp_zero_tuple.
by rewrite integral_dirac ?diracT ?mul1e //; exact: measurable_cst.
Qed.

Lemma gpp_nthE (xs : list R) i : List.nth i xs 0%R = nth 0%R xs i.
Proof. by elim: xs i => [|x xs IH] [|i] //=; exact: IH. Qed.

Lemma gpp_coordinate_measurable d i (hi : (i < d)%N) :
  measurable_fun [set: d.-tuple (measurableTypeR R)]
    ((fun x => List.nth i (tval x) 0%R) : _ -> measurableTypeR R).
Proof.
have -> : (fun x : d.-tuple (measurableTypeR R) => List.nth i (tval x) 0%R) =
  (fun x => tnth x (Ordinal hi)).
  by apply: funext => x; rewrite gpp_nthE (tnth_nth 0%R).
exact: measurable_tnth.
Qed.

Definition gpp_box d (A : nat -> set (measurableTypeR R)) :
    set (d.-tuple (measurableTypeR R)) :=
  [set x | forall i, (i < d)%N -> A i (List.nth i (tval x) 0%R)].

Lemma gpp_box_measurable d A :
  (forall i, measurable (A i)) -> measurable (gpp_box d A).
Proof.
move=> mA.
have -> : gpp_box d A = (\bigcap_(i : 'I_d) [set x : d.-tuple (measurableTypeR R) |
    A i (List.nth i (tval x) 0%R)])%classic.
  apply/seteqP; split=> x.
  - by move=> hx i _; apply: hx; exact: ltn_ord.
  - by move=> hx i hi; exact: (hx (Ordinal hi) I).
apply: fin_bigcap_measurable; first exact: finite_finset.
move=> i _; have hm := gpp_coordinate_measurable d i (ltn_ord i).
by have := hm measurableT (A i) (mA i); rewrite setTI; apply.
Qed.

Lemma gpp_box_cons d A :
  (gaussian_cons_tuple d @^-1` gpp_box d.+1 A) =
  (A 0%N `*` gpp_box d (fun i => A i.+1)).
Proof.
apply/seteqP; split.
- move=> [a xs] H; split; first exact: (H 0%N (ltn0Sn d)).
  by move=> i hi; exact: (H i.+1 hi).
- move=> [a xs] [ha hx] [|i] hi //=; exact: hx hi.
Qed.

Lemma gpp_boxes d A : (forall i, measurable (A i)) ->
  gaussian_product_law d (gpp_box d A) =
    ((\prod_(i < d) fine (gaussian_law (A i)))%R)%:E.
Proof.
elim: d A => [|d IH] A mA.
- have -> : gpp_box 0 A = setT.
    by apply/seteqP; split=> // x _ i; rewrite ltn0.
  by rewrite probability_setT big_ord0.
- change ((gaussian_pair_probability gaussian_law_probability (gaussian_product_law d))
    (gaussian_cons_tuple d @^-1` gpp_box d.+1 A) =
      ((\prod_(i < d.+1) fine (gaussian_law (A i)))%R)%:E).
  rewrite gpp_box_cons /gaussian_pair_probability.
  have E := @product_measure1E _ _ (measurableTypeR R)
    (d.-tuple (measurableTypeR R)) R gaussian_law_probability
    (gaussian_product_law d) (A 0%N) (gpp_box d (fun i => A i.+1))
    (mA 0%N) (gpp_box_measurable d _ (fun i => mA i.+1)).
  etransitivity; first exact: E.
  etransitivity; first exact: (congr1
    (fun z : \bar R => (gaussian_law_probability (A 0%N) * z)%E)
    (IH _ (fun i => mA i.+1))).
  rewrite big_ord_recl EFinM.
  congr (_ * _)%E.
  symmetry; apply: fineK; exact: fin_num_measure.
Qed.

Lemma gpp_mass d : gaussian_product_law d setT = 1%E.
Proof. exact: probability_setT. Qed.

Lemma gpp_cons_measurable d (F : list R -> R) :
  measurable_fun [set: d.+1.-tuple (measurableTypeR R)]
    (fun x => (F (tval x))%:E) ->
  measurable_fun [set: measurableTypeR R * d.-tuple (measurableTypeR R)]
    (fun p => (F (p.1 :: tval p.2))%:E).
Proof.
move=> mF.
apply: (@measurableT_comp _ _ _ _ _ _
  (fun x : d.+1.-tuple (measurableTypeR R) => (F (tval x))%:E)).
- exact: mF.
- exact: gaussian_cons_tuple_measurable.
Qed.
