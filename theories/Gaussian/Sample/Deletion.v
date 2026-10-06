(* Internal deletion-of-observations lemmas for the exact product law. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  PaperMainDefinitions Asymptotics.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.

Local Notation T := (measurableTypeR R).

Definition paper_main_tail_coordinate (m : nat) (x : m.+1.-tuple T) :
    m.-tuple T := [tuple of behead x].

Lemma paper_main_tail_coordinate_measurable (m : nat) :
  measurable_fun [set: m.+1.-tuple T] (paper_main_tail_coordinate m).
Proof. exact: measurable_behead. Qed.

Lemma paper_main_tail_coordinate_law (m : nat) (E : set (m.-tuple T)) :
  measurable E ->
  gaussian_product_law m.+1 (paper_main_tail_coordinate m @^-1` E) =
  gaussian_product_law m E.
Proof.
move=> mE.
change ((gaussian_law_probability \x gaussian_product_law m)%E
  (gaussian_cons_tuple m @^-1` (paper_main_tail_coordinate m @^-1` E)) =
  gaussian_product_law m E).
have -> : (gaussian_cons_tuple m @^-1` (paper_main_tail_coordinate m @^-1` E)) =
    (setT `*` E).
  apply/seteqP; split.
  - move=> [a xs] h; split; first exact I.
    have ex : paper_main_tail_coordinate m (gaussian_cons_tuple m (a, xs)) = xs
      by apply/val_inj.
    change (E (paper_main_tail_coordinate m (gaussian_cons_tuple m (a, xs)))) in h.
    by rewrite ex in h.
  - move=> [a xs] [_ h].
    change (E (paper_main_tail_coordinate m (gaussian_cons_tuple m (a, xs)))).
    have -> : paper_main_tail_coordinate m (gaussian_cons_tuple m (a, xs)) = xs
      by apply/val_inj.
    exact h.
rewrite product_measure1E //.
have hp : gaussian_law_probability setT = 1%E by exact: probability_setT.
etransitivity; first exact: (congr1
  (fun z : \bar R => (z * gaussian_product_law m E)%E) hp).
by rewrite mul1e.
Qed.

Fixpoint paper_main_drop_coordinates (k m : nat) :
    (Nat.add k m).-tuple T -> m.-tuple T :=
  match k return (Nat.add k m).-tuple T -> m.-tuple T with
  | O => fun x => x
  | S k' => fun x => paper_main_drop_coordinates k' m
      (paper_main_tail_coordinate (Nat.add k' m) x)
  end.

Lemma paper_main_drop_coordinates_measurable (k m : nat) :
  measurable_fun [set: (Nat.add k m).-tuple T] (paper_main_drop_coordinates k m).
Proof.
elim: k => [|k IH]; first exact: measurable_id.
exact: (measurableT_comp IH (paper_main_tail_coordinate_measurable _)).
Qed.

Lemma paper_main_drop_coordinates_law (k m : nat) (E : set (m.-tuple T)) :
  measurable E ->
  gaussian_product_law (Nat.add k m) (paper_main_drop_coordinates k m @^-1` E) =
  gaussian_product_law m E.
Proof.
move=> mE; elim: k => [|k IH]; first by [].
change (gaussian_product_law (Nat.add k m).+1
  (paper_main_tail_coordinate (Nat.add k m) @^-1`
    (paper_main_drop_coordinates k m @^-1` E)) = gaussian_product_law m E).
etransitivity; last exact IH.
apply: paper_main_tail_coordinate_law.
have hm := paper_main_drop_coordinates_measurable k m.
by have := hm measurableT E mE; rewrite setTI.
Qed.

Lemma paper_main_drop_coordinates_nth (k m : nat)
    (x : (Nat.add k m).-tuple T) (i : nat) :
  List.nth i (tval (paper_main_drop_coordinates k m x)) 0 =
  List.nth (Nat.add k i) (tval x) 0.
Proof.
elim: k x => [|k IH] x; first by [].
change (List.nth i (tval (paper_main_drop_coordinates k m
  (paper_main_tail_coordinate (Nat.add k m) x))) 0 =
  List.nth (S (Nat.add k i)) (tval x) 0).
rewrite IH.
change (List.nth (Nat.add k i) (behead (tval x)) 0 =
  List.nth (S (Nat.add k i)) (tval x) 0).
by case: (tval x) => [|a xs] //=; case: (Nat.add k i).
Qed.

Lemma paper_main_tcast_measurable (n m : nat) (h : n = m) :
  measurable_fun [set: n.-tuple T] (@tcast T n m h).
Proof. by case: m / h; exact: measurable_id. Qed.

Lemma paper_main_tcast_law (n m : nat) (h : n = m) (E : set (m.-tuple T)) :
  gaussian_product_law n (tcast h @^-1` E) = gaussian_product_law m E.
Proof. by case: m / h E. Qed.

Definition paper_main_drop_points (k n d : nat) (x : paper_main_sample (k + n) d) :
    paper_main_sample n d :=
  paper_main_drop_coordinates (k * d)%N (n * d)%N (tcast (mulnDl k n d) x).

Lemma paper_main_drop_points_measurable (k n d : nat) :
  measurable_fun [set: paper_main_sample (k + n) d] (paper_main_drop_points k n d).
Proof.
exact: (measurableT_comp (paper_main_drop_coordinates_measurable _ _)
  (paper_main_tcast_measurable _ _ _)).
Qed.

Lemma paper_main_drop_points_law (k n d : nat) (E : set (paper_main_sample n d)) :
  measurable E ->
  paper_main_probability (k + n) d (paper_main_drop_points k n d @^-1` E) =
  paper_main_probability n d E.
Proof.
move=> mE.
change (gaussian_product_law ((k + n) * d)
  (tcast (mulnDl k n d) @^-1`
    (paper_main_drop_coordinates (k * d) (n * d) @^-1` E)) =
  gaussian_product_law (n * d) E).
rewrite paper_main_tcast_law.
exact: paper_main_drop_coordinates_law _ _ _ mE.
Qed.

Lemma paper_main_drop_points_point (k n d i : nat)
    (x : paper_main_sample (k + n) d) :
  paper_main_point (paper_main_drop_points k n d x) i =
  paper_main_point x (k + i)%N.
Proof.
apply/matrixP => a b.
rewrite /paper_main_point !mxE /paper_main_drop_points
  paper_main_drop_coordinates_nth val_tcast.
congr (List.nth _ (tval x) 0).
change (k * d + (i * d + a) = (k + i) * d + a)%N.
by rewrite mulnDl addnA.
Qed.

Lemma paper_main_drop_points_fit (k n d : nat) :
  paper_main_fit_event (k + n) d `<=`
  paper_main_drop_points k n d @^-1` paper_main_fit_event n d.
Proof.
move=> x [S [HS Hfit]].
exists S; split; first exact HS.
move=> i; rewrite paper_main_drop_points_point.
exact: (Hfit (rshift k i)).
Qed.

Lemma paper_main_drop_points_conditioned (k n d : nat) (lm lp : R) :
  paper_main_conditioned_event (k + n) d lm lp `<=`
  paper_main_drop_points k n d @^-1` paper_main_conditioned_event n d lm lp.
Proof.
move=> x [S [HS [Hfit Hrest]]].
exists S; split; first exact HS.
split; last exact Hrest.
move=> i; rewrite paper_main_drop_points_point.
exact: (Hfit (rshift k i)).
Qed.

Lemma paper_main_drop_points_probability_le (k n d : nat)
    (E : set (paper_main_sample (k + n) d))
    (F : set (paper_main_sample n d)) :
  measurable E -> measurable F -> E `<=` paper_main_drop_points k n d @^-1` F ->
  (paper_main_probability (k + n) d E <= paper_main_probability n d F)%E.
Proof.
move=> mE mF EF.
rewrite -[leRHS](paper_main_drop_points_law k n d F mF).
apply: paper_main_probability_mono => //.
have hm := paper_main_drop_points_measurable k n d.
by have := hm measurableT F mF; rewrite setTI.
Qed.

Lemma paper_main_fit_probability_antitone_add (k n d : nat) :
  measurable (paper_main_fit_event (k + n) d) ->
  measurable (paper_main_fit_event n d) ->
  (paper_main_probability (k + n) d (paper_main_fit_event (k + n) d) <=
   paper_main_probability n d (paper_main_fit_event n d))%E.
Proof.
move=> mE mF; apply: paper_main_drop_points_probability_le => //.
exact: paper_main_drop_points_fit.
Qed.

Lemma paper_main_conditioned_probability_antitone_add (k n d : nat) (lm lp : R) :
  measurable (paper_main_conditioned_event (k + n) d lm lp) ->
  measurable (paper_main_conditioned_event n d lm lp) ->
  (paper_main_probability (k + n) d (paper_main_conditioned_event (k + n) d lm lp) <=
   paper_main_probability n d (paper_main_conditioned_event n d lm lp))%E.
Proof.
move=> mE mF; apply: paper_main_drop_points_probability_le => //.
exact: paper_main_drop_points_conditioned.
Qed.
