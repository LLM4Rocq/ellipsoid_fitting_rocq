(* A joint Gaussian exception yields a small conditional exception for most samples. *)
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

Lemma paper_main_split_coordinates_fubini_reverse k m (E : set (k.-tuple T * m.-tuple T)) :
  measurable E ->
  gaussian_product_law (Nat.add k m) (paper_main_split_coordinates k m @^-1` E) =
  (\int[gaussian_product_law m]_x gaussian_product_law k (ysection E x))%E.
Proof.
move=> mE.
rewrite paper_main_split_coordinates_fubini //.
have H := indic_fubini_tonelli (gaussian_product_law k) (gaussian_product_law m) mE.
by rewrite indic_fubini_tonelli_FE // indic_fubini_tonelli_GE // in H.
Qed.

Definition paper_main_conditional_exception_reverse k m
    (E : set (k.-tuple T * m.-tuple T)) (tau : R) : set (m.-tuple T) :=
  [set x | (tau%:E <= gaussian_product_law k (ysection E x))%E].

Lemma paper_main_conditional_exception_reverse_measurable k m E tau :
  measurable E -> measurable (paper_main_conditional_exception_reverse k m E tau).
Proof.
move=> mE; rewrite /paper_main_conditional_exception_reverse -[X in measurable X]setTI.
apply: measurable_lee => //; exact: measurable_fun_ysection.
Qed.

Theorem paper_main_conditional_exception_reverse_markov k m E tau :
  measurable E -> 0 < tau ->
  (tau%:E * gaussian_product_law m (paper_main_conditional_exception_reverse k m E tau) <=
    gaussian_product_law (Nat.add k m) (paper_main_split_coordinates k m @^-1` E))%E.
Proof.
move=> mE Htau.
have mf : measurable_fun [set: m.-tuple T]
    (fun x => gaussian_product_law k (ysection E x)).
  exact: measurable_fun_ysection.
have Habs : (fun x => `|gaussian_product_law k (ysection E x)|%E) =
    (fun x => gaussian_product_law k (ysection E x)).
  apply/funext => x; exact: gee0_abs (measure_ge0 _ _).
have H := le_integral_abse (gaussian_product_law m) measurableT mf Htau.
rewrite setTI in H.
rewrite Habs in H.
have HE : [set x | (tau%:E <= `|gaussian_product_law k (ysection E x)|)%E] =
    paper_main_conditional_exception_reverse k m E tau.
{ exact: (congr1 (fun f => [set x | (tau%:E <= f x)%E]) Habs). }
rewrite HE in H.
by rewrite paper_main_split_coordinates_fubini_reverse.
Qed.

Corollary paper_main_conditional_exception_reverse_bound k m E tau p :
  measurable E -> 0 < tau ->
  (gaussian_product_law (Nat.add k m) (paper_main_split_coordinates k m @^-1` E) <= p)%E ->
  (gaussian_product_law m (paper_main_conditional_exception_reverse k m E tau) <= tau^-1%:E * p)%E.
Proof.
move=> mE Htau Hp; rewrite lee_pdivlMl //.
exact: le_trans (paper_main_conditional_exception_reverse_markov k m E tau mE Htau) Hp.
Qed.
