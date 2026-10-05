(* From a tail bound for every good head to an unconditional bound. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  GaussianProbabilityProductMeasure PaperMainDefinitions PaperMainSampling PaperMainHeadLaw.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.
Local Notation T := (measurableTypeR R).

Lemma paper_main_head_good_section k m
    (E : set (k.-tuple T * m.-tuple T)) (H : set (k.-tuple T)) (h : k.-tuple T) :
  xsection (E `&` ((~` H) `*` [set: m.-tuple T])) h =
  if h \in H then set0 else xsection E h.
Proof.
case: (boolP (h \in H)) => hH.
- apply/seteqP; split=> t; last by case.
  move/xsectionP=> [he [hh _]]; exact: hh (set_mem hH).
- have hn : ~ H h.
    by move=> hh; have hm := mem_set hh; move: hH; rewrite hm.
  apply/seteqP; split=> t.
  + move/xsectionP=> [he _]; exact/xsectionP.
  + move/xsectionP=> he; apply/xsectionP; split=> //; by split.
Qed.

Theorem paper_main_head_exception_bound k m
    (E : set (k.-tuple T * m.-tuple T)) (H : set (k.-tuple T)) (p : \bar R) :
  measurable E -> measurable H -> (0 <= p)%E ->
  (forall h, ~ H h -> (gaussian_product_law m (xsection E h) <= p)%E) ->
  (gaussian_product_law (Nat.add k m)
    (paper_main_split_coordinates k m @^-1` E) <=
    p + gaussian_product_law k H)%E.
Proof.
move=> mE mH Hp0 Hp.
pose G := E `&` ((~` H) `*` [set: m.-tuple T]).
have mG : measurable G by apply: measurableI => //; apply: measurableX => //; exact: measurableC.
have mHT : measurable (H `*` [set: m.-tuple T]) by exact: measurableX.
pose Q := gaussian_pair_probability (gaussian_product_law k) (gaussian_product_law m).
have HG : (Q G <= p)%E.
  change (((gaussian_product_law k \x gaussian_product_law m)%E G) <= p)%E.
  rewrite -(paper_main_split_coordinates_law k m G mG).
  apply: paper_main_split_coordinates_section_bound => // h.
  rewrite /G paper_main_head_good_section.
  case: (boolP (h \in H)) => hh; first by rewrite measure0.
  apply: Hp; move=> hH; have hm := mem_set hH.
  by move: hh; rewrite hm.
have HU : E `<=` (G `|` (H `*` [set: m.-tuple T])).
  move=> [h t] he; case: (pselect (H h)) => hh.
  - by right; split.
  - left; split; first exact he.
    by split.
have HQU : (Q E <= Q G + Q (H `*` [set: m.-tuple T]))%E.
  apply: le_trans _ (measureU2 Q mG mHT).
  apply: le_measure; rewrite ?inE //; exact: measurableU.
have HQH : Q (H `*` [set: m.-tuple T]) = gaussian_product_law k H.
  change ((gaussian_product_law k \x gaussian_product_law m)%E
    (H `*` [set: m.-tuple T]) = gaussian_product_law k H).
  rewrite product_measure1E; first exact mH.
  - exact: measurableT.
  - etransitivity; first exact: (congr1
      (fun z : \bar R => (gaussian_product_law k H * z)%E) (gpp_mass m)).
    by rewrite mule1.
rewrite (paper_main_split_coordinates_law k m E mE).
change (Q E <= p + gaussian_product_law k H)%E.
apply: le_trans HQU _.
rewrite HQH; exact: leeD HG (lexx _).
Qed.

Corollary paper_main_split_points_section_bound k n d
    (E : set (paper_main_sample k d * paper_main_sample n d)) (p : \bar R) :
  measurable E ->
  (forall h, (paper_main_probability n d (xsection E h) <= p)%E) ->
  (paper_main_probability (k + n) d
    (paper_main_split_points k n d @^-1` E) <= p)%E.
Proof.
move=> mE Hp.
change (gaussian_product_law ((k + n) * d)%N
  (tcast (mulnDl k n d) @^-1`
    (paper_main_split_coordinates (k * d)%N (n * d)%N @^-1` E)) <= p)%E.
rewrite paper_main_tcast_law.
exact: paper_main_split_coordinates_section_bound.
Qed.

Corollary paper_main_head_points_exception_bound k n d
    (E : set (paper_main_sample k d * paper_main_sample n d))
    (H : set (paper_main_sample k d)) (p : \bar R) :
  measurable E -> measurable H -> (0 <= p)%E ->
  (forall h, ~ H h -> (paper_main_probability n d (xsection E h) <= p)%E) ->
  (paper_main_probability (k + n) d
    (paper_main_split_points k n d @^-1` E) <=
    p + paper_main_probability k d H)%E.
Proof.
move=> mE mH Hp0 Hp.
change (gaussian_product_law ((k + n) * d)%N
  (tcast (mulnDl k n d) @^-1`
    (paper_main_split_coordinates (k * d)%N (n * d)%N @^-1` E)) <=
    p + gaussian_product_law (k * d)%N H)%E.
rewrite paper_main_tcast_law.
exact: paper_main_head_exception_bound.
Qed.
