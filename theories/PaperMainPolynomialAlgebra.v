(* Arithmetic closure of the internal finite polynomial expansions. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum poly matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainGaussianMultivariate.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.
Local Notation RT := (measurableTypeR R).

Lemma paper_main_polynomial_constant (m : nat) (a : R) :
  paper_main_polynomial_function m (fun _ => a).
Proof.
elim: m => [//|m IH].
exists 1%N, (fun (_ : 'I_1) (_ : m.-tuple RT) => a); split => //.
by move=> b x; rewrite big_ord1 /= expr0 mulr1.
Qed.

Lemma paper_main_polynomial_expand (m N : nat) (f : m.+1.-tuple RT -> R)
    (p : m.-tuple RT -> {poly R}) :
  (forall x, (size (p x) <= N)%N) ->
  (forall j : nat, paper_main_polynomial_function m (fun x => (p x)`_j)) ->
  (forall a x, f (gaussian_cons_tuple m (a, x)) = (p x).[a]) ->
  paper_main_polynomial_function m.+1 f.
Proof.
move=> hp hc hf.
exists N, (fun i : 'I_N => fun x => (p x)`_i); split => // a x.
by rewrite hf -horner_coef_wide.
Qed.

Lemma paper_main_polynomial_coefficients (m : nat) (f : m.+1.-tuple RT -> R) :
  paper_main_polynomial_function m.+1 f ->
  exists N (p : m.-tuple RT -> {poly R}),
    (forall x, (size (p x) <= N)%N) /\
    (forall j : nat, paper_main_polynomial_function m (fun x => (p x)`_j)) /\
    (forall a x, f (gaussian_cons_tuple m (a, x)) = (p x).[a]).
Proof.
move=> [N [c [hc hf]]].
pose cc (j : nat) (x : m.-tuple RT) :=
  if (insub j : option 'I_N) is Some i then c i x else 0.
pose p (x : m.-tuple RT) := \poly_(j < N) cc j x.
exists N, p; split; first by move=> x; exact: size_poly.
split.
- move=> j.
  have ep : (fun x => (p x)`_j) = (fun x => if (j < N)%N then cc j x else 0)
    by apply/funext => x; rewrite /p coef_poly.
  rewrite ep; case: (j < N)%N; last exact: paper_main_polynomial_constant.
  rewrite /cc; case: (insub j : option 'I_N) => [i|];
    [exact: hc | exact: paper_main_polynomial_constant].
- move=> a x; rewrite hf /p horner_poly.
  apply: eq_bigr => i _.
  by rewrite /cc valK.
Qed.

Lemma paper_main_polynomial_sum_rule (m : nat)
    (Hadd : forall f g : m.-tuple RT -> R,
      paper_main_polynomial_function m f -> paper_main_polynomial_function m g ->
      paper_main_polynomial_function m (fun x => f x + g x))
    (I : Type) (s : seq I) (h : I -> m.-tuple RT -> R) :
  (forall i, paper_main_polynomial_function m (h i)) ->
  paper_main_polynomial_function m (fun x => \sum_(i <- s) h i x).
Proof.
move=> hc; elim: s => [|i s IH].
- under eq_fun do rewrite big_nil.
  exact: paper_main_polynomial_constant.
- under eq_fun do rewrite big_cons.
  apply: Hadd; [exact: hc | exact: IH].
Qed.

Lemma paper_main_polynomial_arithmetic (m : nat) :
  (forall f g : m.-tuple RT -> R,
    paper_main_polynomial_function m f -> paper_main_polynomial_function m g ->
    paper_main_polynomial_function m (fun x => f x + g x)) /\
  (forall f g : m.-tuple RT -> R,
    paper_main_polynomial_function m f -> paper_main_polynomial_function m g ->
    paper_main_polynomial_function m (fun x => f x * g x)).
Proof.
elim: m => [|m [HD HM]]; first by split.
split=> f g pf pg;
  have [N [p [hp [pc pe]]]] := paper_main_polynomial_coefficients m f pf;
  have [M [q [hq [qc qe]]]] := paper_main_polynomial_coefficients m g pg.
- apply: (paper_main_polynomial_expand m (maxn N M) _ (fun x => p x + q x)).
  + move=> x; apply: leq_trans (size_polyD _ _) _.
    by rewrite geq_max !leq_max hp hq orbT.
  + move=> j.
    have -> : (fun x => (p x + q x)`_j) = (fun x => (p x)`_j + (q x)`_j)
      by apply/funext => x; rewrite coefD.
    exact: HD.
  + by move=> a x; rewrite pe qe hornerD.
- apply: (paper_main_polynomial_expand m (N + M)%N _ (fun x => p x * q x)).
  + move=> x; apply: leq_trans (size_polyMleq _ _) _.
    apply: leq_trans (leq_pred _) _.
    exact: leq_add.
  + move=> j; under eq_fun do rewrite coefM.
    apply: (paper_main_polynomial_sum_rule m HD).
    move=> i; exact: HM.
  + by move=> a x; rewrite pe qe hornerM.
Qed.

Lemma paper_main_polynomial_add (m : nat) (f g : m.-tuple RT -> R) :
  paper_main_polynomial_function m f -> paper_main_polynomial_function m g ->
  paper_main_polynomial_function m (fun x => f x + g x).
Proof. exact: (proj1 (paper_main_polynomial_arithmetic m)). Qed.

Lemma paper_main_polynomial_mul (m : nat) (f g : m.-tuple RT -> R) :
  paper_main_polynomial_function m f -> paper_main_polynomial_function m g ->
  paper_main_polynomial_function m (fun x => f x * g x).
Proof. exact: (proj2 (paper_main_polynomial_arithmetic m)). Qed.

Lemma paper_main_polynomial_sum (m : nat) (I : Type) (s : seq I)
    (h : I -> m.-tuple RT -> R) :
  (forall i, paper_main_polynomial_function m (h i)) ->
  paper_main_polynomial_function m (fun x => \sum_(i <- s) h i x).
Proof. exact: (paper_main_polynomial_sum_rule m (paper_main_polynomial_add m)). Qed.

Lemma paper_main_polynomial_product (m : nat) (I : Type) (s : seq I)
    (h : I -> m.-tuple RT -> R) :
  (forall i, paper_main_polynomial_function m (h i)) ->
  paper_main_polynomial_function m (fun x => \prod_(i <- s) h i x).
Proof.
move=> hc; elim: s => [|i s IH].
- under eq_fun do rewrite big_nil.
  exact: paper_main_polynomial_constant.
- under eq_fun do rewrite big_cons.
  apply: paper_main_polynomial_mul; [exact: hc | exact: IH].
Qed.

Lemma paper_main_polynomial_tnth (m : nat) (i : 'I_m) :
  paper_main_polynomial_function m (fun x => tnth x i).
Proof.
elim: m i => [i|m IH i]; first by have := ltn_ord i; rewrite ltn0.
case: (unliftP ord0 i) => [j ->|->].
- apply: (paper_main_polynomial_expand m 1 _ (fun x => (tnth x j)%:P)).
  + move=> x; exact: size_polyC_leq1.
  + move=> k; under eq_fun do rewrite coefC.
    case: (k == 0)%N; [exact: IH | exact: paper_main_polynomial_constant].
  + by move=> a x; rewrite /gaussian_cons_tuple tnthS hornerC.
- apply: (paper_main_polynomial_expand m 2 _ (fun _ => 'X)).
  + by move=> x; rewrite size_polyX.
  + move=> k; exact: paper_main_polynomial_constant.
  + by move=> a x; rewrite /gaussian_cons_tuple tnth0 hornerX.
Qed.

Lemma paper_main_polynomial_list_coordinate (m k : nat) :
  paper_main_polynomial_function m (fun x => List.nth k (tval x) 0).
Proof.
have en (s : seq R) (j : nat) : List.nth j s 0 = nth 0 s j
  by elim: s j => [|a s IH] [|j] //=.
have [km|km] := ltnP k m.
- have -> : (fun x : m.-tuple RT => List.nth k (tval x) 0) =
      (fun x => tnth x (Ordinal km))
    by apply/funext => x; rewrite en (tnth_nth 0).
  exact: paper_main_polynomial_tnth.
- have -> : (fun x : m.-tuple RT => List.nth k (tval x) 0) = (fun _ => 0).
    apply/funext => x; rewrite en nth_default //.
    by rewrite size_tuple.
  exact: paper_main_polynomial_constant.
Qed.

Lemma paper_main_polynomial_determinant (m d : nat) (A : m.-tuple RT -> 'M[R]_d) :
  (forall i j, paper_main_polynomial_function m (fun x => A x i j)) ->
  paper_main_polynomial_function m (fun x => \det (A x)).
Proof.
move=> hA; rewrite /determinant.
apply: paper_main_polynomial_sum => s.
apply: paper_main_polynomial_mul; first exact: paper_main_polynomial_constant.
apply: paper_main_polynomial_product => i.
exact: hA.
Qed.
