(* Linear forms in independent Gaussian coordinates. This is groundwork
   for almost-sure spanning, not a spanning theorem. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainGaussianNull.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Definition paper_main_gaussian_linear (m : nat) (c : 'I_m -> R)
    (x : m.-tuple (measurableTypeR R)) : R :=
  \sum_(i < m) c i * tnth x i.

Lemma paper_main_gaussian_linear_measurable (m : nat) (c : 'I_m -> R) :
  measurable_fun [set: m.-tuple (measurableTypeR R)]
    (fun x => (paper_main_gaussian_linear m c x : measurableTypeR R)).
Proof.
rewrite /paper_main_gaussian_linear.
apply: measurable_sum => i.
apply: measurable_funM; [exact: measurable_cst | exact: measurable_tnth].
Qed.

Lemma paper_main_gaussian_linear_cons (m : nat) (c : 'I_m.+1 -> R)
    (a : R) (x : m.-tuple (measurableTypeR R)) :
  paper_main_gaussian_linear m.+1 c (gaussian_cons_tuple m (a, x)) =
  c ord0 * a + paper_main_gaussian_linear m (fun i => c (lift ord0 i)) x.
Proof.
rewrite /paper_main_gaussian_linear big_ord_recl /gaussian_cons_tuple tnth0.
congr (_ + _).
apply: eq_bigr => i _.
by rewrite tnthS.
Qed.

Lemma paper_main_gaussian_null_sections (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R))) :
  measurable E ->
  (forall x : m.-tuple (measurableTypeR R),
    gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))] = 0%E) ->
  gaussian_product_law m.+1 E = 0%E.
Proof.
move=> mE hE.
have mA : measurable (gaussian_cons_tuple m @^-1` E).
  have h := gaussian_cons_tuple_measurable m measurableT E mE.
  by rewrite setTI in h.
change ((gaussian_law_probability \x gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` E) = 0%E).
transitivity ((gaussian_law_probability \x^ gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` E)).
- apply: product_measure_unique => // A B hA hB.
  by rewrite /= product_measure2E.
- rewrite /product_measure2.
  transitivity (\int[gaussian_product_law m]_x 0)%E; last exact: integral0.
  apply: eq_integral => x _.
  rewrite /ysection /=.
  transitivity (gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))]);
    last exact: hE.
  congr (gaussian_law_probability _).
  by apply/seteqP; split=> a /=; rewrite in_setE.
Qed.

Lemma paper_main_gaussian_linear_level_measurable (m : nat) (c : 'I_m -> R)
    (b : R) :
  measurable [set x : m.-tuple (measurableTypeR R) |
    paper_main_gaussian_linear m c x = b].
Proof.
have mb : measurable ([set b] : set (measurableTypeR R))
  by exact: measurable_set1.
have h := paper_main_gaussian_linear_measurable m c measurableT
  [set b] mb.
by rewrite setTI in h.
Qed.

Lemma paper_main_gaussian_null_tail_sections (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R))) :
  (forall a : R, gaussian_product_law m
    [set x | E (gaussian_cons_tuple m (a, x))] = 0%E) ->
  gaussian_product_law m.+1 E = 0%E.
Proof.
move=> hE.
change ((gaussian_law_probability \x gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` E) = 0%E).
rewrite /product_measure1.
transitivity (\int[gaussian_law_probability]_a 0)%E; last exact: integral0.
apply: eq_integral => a _.
rewrite /xsection /=.
transitivity (gaussian_product_law m [set x | E (gaussian_cons_tuple m (a, x))]);
  last exact: hE.
congr (gaussian_product_law m _).
by apply/seteqP; split=> x /=; rewrite in_setE.
Qed.

Lemma paper_main_gaussian_linear_null (m : nat) (c : 'I_m -> R) (b : R) :
  (exists i : 'I_m, c i != 0) ->
  gaussian_product_law m
    [set x | paper_main_gaussian_linear m c x = b] = 0%E.
Proof.
elim: m c => [c [i hi]|m IH c hc].
- by have := ltn_ord i; rewrite ltn0.
- case h0: (c ord0 == 0).
  + have c0 : c ord0 = 0 by exact/eqP.
    have ht : exists i : 'I_m, c (lift ord0 i) != 0.
      move: hc => [i hi].
      case: (unliftP ord0 i) => [j hij|hi0].
      * exists j; by rewrite -hij.
      * by rewrite hi0 c0 eqxx in hi.
    apply: paper_main_gaussian_null_tail_sections => a.
    rewrite (_ : [set x | paper_main_gaussian_linear m.+1 c
        (gaussian_cons_tuple m (a, x)) = b] =
      [set x | paper_main_gaussian_linear m (fun i => c (lift ord0 i)) x = b]).
    * by apply/seteqP; split=> x /=;
        rewrite paper_main_gaussian_linear_cons c0 mul0r add0r.
    * exact: IH _ ht.
  + apply: paper_main_gaussian_null_sections;
      first exact: paper_main_gaussian_linear_level_measurable.
    move=> x.
    have cn0 : c ord0 != 0 by rewrite h0.
    have hs : [set a | paper_main_gaussian_linear m.+1 c
        (gaussian_cons_tuple m (a, x)) = b] =
      [set ((b - paper_main_gaussian_linear m (fun i => c (lift ord0 i)) x) /
        c ord0)].
      apply/seteqP; split=> a /=; rewrite paper_main_gaussian_linear_cons.
      * move=> ha.
        by rewrite -ha addrK [c ord0 * a]mulrC mulfK.
      * move=> ->.
        by rewrite [c ord0 * _]mulrC divfK // subrK.
    rewrite hs.
    exact: paper_main_gaussian_singleton.
Qed.
