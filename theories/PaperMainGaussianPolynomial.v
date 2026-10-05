(* Nonzero scalar polynomials vanish with Gaussian probability zero. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainGaussianNull.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma paper_main_polynomial_measurable (p : {poly R}) :
  measurable_fun [set: measurableTypeR R]
    (fun a => (p.[a] : measurableTypeR R)).
Proof.
elim/poly_ind: p => [|p c IHp].
- have -> : (fun a : measurableTypeR R => (0 : {poly R}).[a]) =
      (fun _ => (0 : measurableTypeR R))
    by apply/funext => a; rewrite horner0.
  exact: measurable_cst.
- have -> : (fun a : measurableTypeR R => (p * 'X + c%:P).[a]) =
      (fun a => (p.[a] * a + c : measurableTypeR R))
    by apply/funext => a; rewrite hornerD hornerM hornerX hornerC.
  apply: measurable_funD; last exact: measurable_cst.
  apply: measurable_funM => //; exact: measurable_id.
Qed.

Lemma paper_main_polynomial_zero_measurable (p : {poly R}) :
  measurable [set a : measurableTypeR R | p.[a] = 0].
Proof.
have mb : measurable ([set 0] : set (measurableTypeR R))
  by exact: measurable_set1.
have h := paper_main_polynomial_measurable p measurableT [set 0] mb.
by rewrite setTI in h.
Qed.

Lemma paper_main_gaussian_polynomial_null (p : {poly R}) :
  p != 0 -> gaussian_law_probability [set a | p.[a] = 0] = 0%E.
Proof.
have H : forall n (q : {poly R}), (size q <= n)%N -> q != 0 ->
    gaussian_law_probability [set a | q.[a] = 0] = 0%E.
  elim=> [q hq nq|n IH q hq nq].
  - by move: hq; rewrite leqn0 size_poly_eq0 (negbTE nq).
  - case: (pselect (exists a : R, root q a)) => [[a ha]|ha].
    + have [r er] := (elimT (factor_theorem q a) ha).
      have nr : r != 0.
        apply/eqP => r0.
        by rewrite er r0 mul0r eqxx in nq.
      have hr : (size r <= n)%N.
        move: hq; rewrite er size_Mmonic ?monicXsubC // size_XsubC addnC.
        auto with real arith.
      have rz := IH r hr nr.
      have he : [set x : measurableTypeR R | q.[x] = 0] =
          [set x : measurableTypeR R | r.[x] = 0] `|` [set a].
        apply/seteqP; split=> x /=.
        * move/eqP; rewrite -rootE er rootM root_XsubC =>
            /orP [/eqP hx|/eqP hx]; [by left | by right].
        * move=> [hx|hx]; apply/eqP; rewrite -rootE er rootM root_XsubC;
            [by rewrite rootE hx eqxx | by rewrite hx eqxx orbT].
      rewrite he.
      refine (@null_set_setU _ (measurableTypeR R) R gaussian_law_probability
        [set x | r.[x] = 0] [set a] _ _ rz _).
      * exact: paper_main_polynomial_zero_measurable.
      * exact: measurable_set1.
      * exact: paper_main_gaussian_singleton.
    + have he : [set x : measurableTypeR R | q.[x] = 0] = set0.
        apply/seteqP; split=> x /=; last by [].
        move=> hx; apply: ha.
        exists x; exact/eqP.
      by rewrite he measure0.
exact: H (size p) p (leqnn _).
Qed.
