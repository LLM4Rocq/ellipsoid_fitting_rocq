(* Gaussian sections outside a null exceptional set. This will be used
   for polynomial zero sets and almost-sure spanning. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainGaussianLinear.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_gaussian_section_set (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R)))
    (x : m.-tuple (measurableTypeR R)) :
  ysection (gaussian_cons_tuple m @^-1` E) x =
    [set a | E (gaussian_cons_tuple m (a, x))].
Proof.
rewrite /ysection.
by apply/seteqP; split=> a /=; rewrite in_setE.
Qed.

Lemma paper_main_gaussian_section_measurable (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R))) :
  measurable E ->
  measurable_fun [set: m.-tuple (measurableTypeR R)]
    (fun x => gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))]).
Proof.
move=> mE.
have mA : measurable (gaussian_cons_tuple m @^-1` E).
  have h := gaussian_cons_tuple_measurable m measurableT E mE.
  by rewrite setTI in h.
have hfun : (fun x => gaussian_law_probability
    [set a | E (gaussian_cons_tuple m (a, x))]) =
    gaussian_law_probability \o ysection (gaussian_cons_tuple m @^-1` E).
  apply/funext => x.
  by rewrite /comp paper_main_gaussian_section_set.
rewrite hfun.
exact: measurable_fun_ysection.
Qed.

Lemma paper_main_gaussian_sections (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R))) :
  measurable E ->
  gaussian_product_law m.+1 E =
    (\int[gaussian_product_law m]_x
      gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))])%E.
Proof.
move=> mE.
have mA : measurable (gaussian_cons_tuple m @^-1` E).
  have h := gaussian_cons_tuple_measurable m measurableT E mE.
  by rewrite setTI in h.
change ((gaussian_law_probability \x gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` E) =
  (\int[gaussian_product_law m]_x
    gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))])%E).
transitivity ((gaussian_law_probability \x^ gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` E)).
- apply: product_measure_unique => // A B hA hB.
  by rewrite /= product_measure2E.
- rewrite /product_measure2.
  apply: eq_integral => x _.
  by rewrite /comp paper_main_gaussian_section_set.
Qed.

Lemma paper_main_gaussian_null_sections_except (m : nat)
    (E : set (m.+1.-tuple (measurableTypeR R)))
    (B : set (m.-tuple (measurableTypeR R))) :
  measurable E -> measurable B -> gaussian_product_law m B = 0%E ->
  (forall x : m.-tuple (measurableTypeR R), ~ B x ->
    gaussian_law_probability [set a | E (gaussian_cons_tuple m (a, x))] = 0%E) ->
  gaussian_product_law m.+1 E = 0%E.
Proof.
move=> mE mB B0 hE.
rewrite paper_main_gaussian_sections //.
transitivity (\int[gaussian_product_law m]_x 0)%E; last exact: integral0.
apply: ae_eq_integral => //; first exact: paper_main_gaussian_section_measurable.
exists B; split => //.
move=> x hx.
apply: contrapT => nx.
apply: hx => _.
exact: hE.
Qed.
