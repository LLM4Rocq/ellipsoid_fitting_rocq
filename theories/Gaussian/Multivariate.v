(* Internal certificates for polynomial functions on finite real tuples. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Gaussian.Null Gaussian.Sections Gaussian.Polynomial.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.
Local Notation RT := (measurableTypeR R).

Fixpoint paper_main_polynomial_function (m : nat) :
    (m.-tuple RT -> R) -> Prop :=
  match m as k return (k.-tuple RT -> R) -> Prop with
  | O => fun _ => True
  | S k => fun f => exists N (c : 'I_N -> k.-tuple RT -> R),
      (forall i, paper_main_polynomial_function k (c i)) /\
      forall a x, f (gaussian_cons_tuple k (a, x)) =
        \sum_(i < N) c i x * a ^+ i
  end.

Lemma paper_main_multivariate_measurable (m : nat) (f : m.-tuple RT -> R) :
  paper_main_polynomial_function m f ->
  measurable_fun [set: m.-tuple RT] (fun x => (f x : RT)).
Proof.
elim: m f => [f _|m IH f [N [c [hc hf]]]].
- have ef : (fun x : 0.-tuple RT => f x) = (fun _ => f [tuple]).
    apply/funext => x.
    congr (f _); apply/val_inj.
    exact: Gaussian.ProductLawBasics.gpp_zero_tuple.
  rewrite ef.
  exact: measurable_cst.
- have ef : f = (fun x : m.+1.-tuple RT =>
      \sum_(i < N) c i [tuple of behead x] * (thead x) ^+ i).
    apply/funext => x.
    have h := hf (thead x) [tuple of behead x].
    have ex : gaussian_cons_tuple m (thead x, [tuple of behead x]) = x.
      apply/val_inj.
      exact (congr1 (fun t : m.+1.-tuple RT => val t) (esym (@tuple_eta m RT x))).
    by rewrite ex in h.
  rewrite ef.
  apply: measurable_sum => i.
  apply: measurable_funM.
  + apply: measurableT_comp;
      [exact: IH (c i) (hc i) | exact: measurable_behead].
  + apply: measurable_funX.
    exact: measurable_tnth.
Qed.

Lemma paper_main_multivariate_zero_measurable (m : nat) (f : m.-tuple RT -> R) :
  paper_main_polynomial_function m f -> measurable [set x | f x = 0].
Proof.
move=> pf.
have mb : measurable ([set 0] : set RT) by exact: measurable_set1.
have h := paper_main_multivariate_measurable m f pf measurableT [set 0] mb.
by rewrite setTI in h.
Qed.

Lemma paper_main_gaussian_multivariate_null (m : nat) (f : m.-tuple RT -> R) :
  paper_main_polynomial_function m f -> (exists x, f x != 0) ->
  gaussian_product_law m [set x | f x = 0] = 0%E.
Proof.
elim: m f => [f _ [w hw]|m IH f pf [w hw]].
- have he : [set x : 0.-tuple RT | f x = 0] = set0.
    apply/seteqP; split=> x /=; last by [].
    have ex : x = w.
      apply/val_inj; change (tval x = tval w).
      by rewrite !Gaussian.ProductLawBasics.gpp_zero_tuple.
    rewrite ex => h.
    by rewrite h eqxx in hw.
  by rewrite he measure0.
- have [N [c [hc hf]]] := pf.
  pose y : m.-tuple RT := [tuple of behead w].
  have ew : gaussian_cons_tuple m (thead w, y) = w.
    apply/val_inj.
    exact (congr1 (fun t : m.+1.-tuple RT => val t) (esym (@tuple_eta m RT w))).
  have ec : exists i : 'I_N, c i y != 0.
    case: (pselect (exists i : 'I_N, c i y != 0)) => // hn.
    have cz : forall i : 'I_N, c i y = 0.
      move=> i; case: (eqVneq (c i y) 0) => // hi.
      exfalso; apply: hn; by exists i.
    have f0 : f w = 0.
      rewrite -ew hf.
      apply: big1 => i _.
      by rewrite cz mul0r.
    by rewrite f0 eqxx in hw.
  move: ec => [i hi].
  apply: (paper_main_gaussian_null_sections_except m _ [set x | c i x = 0]).
  + exact: paper_main_multivariate_zero_measurable pf.
  + exact: paper_main_multivariate_zero_measurable (hc i).
  + apply: (IH (c i) (hc i)).
    by exists y.
  + move=> x hx.
    pose cc (j : nat) := if (insub j : option 'I_N) is Some k then c k x else 0.
    have ccE (j : 'I_N) : cc j = c j x by rewrite /cc valK.
    pose p := \poly_(j < N) cc j.
    have cp : p`_i = c i x by rewrite /p coef_poly (ltn_ord i) ccE.
    have np : p != 0.
      apply/eqP => ep; apply: hx.
      by rewrite /= -cp ep coef0.
    have ep (a : R) : p.[a] = f (gaussian_cons_tuple m (a, x)).
      rewrite /p horner_poly hf.
      apply: eq_bigr => j _.
      by rewrite ccE.
    have he : [set a | [set x0 | f x0 = 0] (gaussian_cons_tuple m (a, x))] =
        [set a | p.[a] = 0].
      by apply/seteqP; split=> a /=; rewrite ep.
    rewrite he.
    exact: paper_main_gaussian_polynomial_null np.
Qed.
