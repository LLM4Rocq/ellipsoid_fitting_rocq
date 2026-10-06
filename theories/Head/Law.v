(* Independence of consecutive blocks of coordinates under the Gaussian
   product law. The map paper_main_split_coordinates, which splits a tuple
   of k + m coordinates into its first k and its last m coordinates, is
   measurable and sends gaussian_product_law (k + m) to the product of
   gaussian_product_law k and gaussian_product_law m.
   - paper_main_split_coordinates_rectangle: the probability of the
     preimage of A x B is P(A) P(B), by induction on k, writing the product
     law of k + 1 coordinates as the product of the normal law and the law
     of the last k coordinates.
   - paper_main_split_coordinates_law: the image law is the product measure,
     by uniqueness of product measures. paper_main_split_coordinates_fubini:
     the probability of an event is the integral of the probabilities of
     its sections.
   - paper_main_take_coordinates_law: the first k coordinates have the law
     gaussian_product_law k.
   - paper_main_split_coordinates_section_bound: a bound on the probability
     of every section bounds the probability of the event.
   - paper_main_split_points_law, paper_main_split_points_rectangle: the
     same for a sample of k + n points of R^d, split into its first k and
     its last n points (paper_main_split_points). *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution measurable_realfun.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions
  Gaussian.Law.ProductBasics PaperMainDefinitions Gaussian.Sample.Deletion.
Import Order.TTheory GRing.Theory Num.Theory.
Open Scope ring_scope.
Open Scope classical_set_scope.
Local Notation T := (measurableTypeR R).

Fixpoint paper_main_take_coordinates (k m : nat) :
    (Nat.add k m).-tuple T -> k.-tuple T :=
  match k return (Nat.add k m).-tuple T -> k.-tuple T with
  | O => fun _ => [tuple]
  | S k' => fun x => gaussian_cons_tuple k'
      (tnth x ord0, paper_main_take_coordinates k' m
        (paper_main_tail_coordinate (Nat.add k' m) x))
  end.

Lemma paper_main_take_coordinates_measurable k m :
  measurable_fun [set: (Nat.add k m).-tuple T] (paper_main_take_coordinates k m).
Proof.
elim: k => [|k IH]; first exact: measurable_cst.
apply: measurable_cons; first exact: measurable_tnth.
exact: (measurableT_comp IH (paper_main_tail_coordinate_measurable _)).
Qed.

Definition paper_main_split_coordinates k m (x : (Nat.add k m).-tuple T) :=
  (paper_main_take_coordinates k m x, paper_main_drop_coordinates k m x).

Lemma paper_main_split_coordinates_measurable k m :
  measurable_fun [set: (Nat.add k m).-tuple T] (paper_main_split_coordinates k m).
Proof.
apply: measurable_fun_pair.
- exact: paper_main_take_coordinates_measurable.
- exact: paper_main_drop_coordinates_measurable.
Qed.

HB.instance Definition _ k m := isMeasurableFun.Build _ _ _ _
  (paper_main_split_coordinates k m) (paper_main_split_coordinates_measurable k m).

Lemma paper_main_take_coordinates_cons k m (a : T) (x : (Nat.add k m).-tuple T) :
  paper_main_take_coordinates k.+1 m (gaussian_cons_tuple (Nat.add k m) (a, x)) =
  gaussian_cons_tuple k (a, paper_main_take_coordinates k m x).
Proof.
change (gaussian_cons_tuple k
 (tnth (gaussian_cons_tuple (Nat.add k m) (a, x)) ord0,
  paper_main_take_coordinates k m
   (paper_main_tail_coordinate (Nat.add k m)
    (gaussian_cons_tuple (Nat.add k m) (a, x)))) =
 gaussian_cons_tuple k (a, paper_main_take_coordinates k m x)).
have -> : paper_main_tail_coordinate (Nat.add k m)
    (gaussian_cons_tuple (Nat.add k m) (a, x)) = x by apply/val_inj.
by rewrite /gaussian_cons_tuple tnth0.
Qed.

Lemma paper_main_drop_coordinates_cons k m (a : T) (x : (Nat.add k m).-tuple T) :
  paper_main_drop_coordinates k.+1 m (gaussian_cons_tuple (Nat.add k m) (a, x)) =
  paper_main_drop_coordinates k m x.
Proof.
change (paper_main_drop_coordinates k m
 (paper_main_tail_coordinate (Nat.add k m)
  (gaussian_cons_tuple (Nat.add k m) (a, x))) =
 paper_main_drop_coordinates k m x).
congr (paper_main_drop_coordinates k m _); exact/val_inj.
Qed.

Lemma paper_main_split_coordinates_rectangle k m
    (A : set (k.-tuple T)) (B : set (m.-tuple T)) :
  measurable A -> measurable B ->
  gaussian_product_law (Nat.add k m)
    (paper_main_split_coordinates k m @^-1` (A `*` B)) =
  (gaussian_product_law k A * gaussian_product_law m B)%E.
Proof.
move=> mA mB; elim: k A mA => [|k IH] A mA.
- change (gaussian_product_law m [set x | A [tuple] /\ B x] =
    (dirac [tuple] A * gaussian_product_law m B)%E).
  rewrite /dirac /numfun.indic /=.
  case: (boolP ([tuple] \in A)) => hA.
  + have h : A [tuple] := (set_mem hA).
    have -> : [set x : m.-tuple T | A [tuple] /\ B x] = B.
      by apply/seteqP; split=> x; [case|split].
    by rewrite mul1e.
  + have h : ~ A [tuple].
      move=> h; have hmem : [tuple] \in A := mem_set h.
      by move: hA; rewrite hmem.
    have -> : [set x : m.-tuple T | A [tuple] /\ B x] = set0.
      by apply/seteqP; split=> x; [case=> /h|case].
    by rewrite measure0 mul0e.
- pose C := gaussian_cons_tuple k @^-1` A.
  have mC : measurable C.
    by have := gaussian_cons_tuple_measurable k measurableT A mA; rewrite setTI.
  have ms a : measurable (xsection C a) by exact: measurable_xsection.
  change ((gaussian_law_probability \x gaussian_product_law (Nat.add k m))%E
    (gaussian_cons_tuple (Nat.add k m) @^-1`
      (paper_main_split_coordinates k.+1 m @^-1` (A `*` B))) =
    ((gaussian_law_probability \x gaussian_product_law k)%E C *
      gaussian_product_law m B)%E).
  rewrite /product_measure1 /=.
  have hs a : xsection
      (gaussian_cons_tuple (Nat.add k m) @^-1`
        (paper_main_split_coordinates k.+1 m @^-1` (A `*` B))) a =
      paper_main_split_coordinates k m @^-1` (xsection C a `*` B).
    apply/seteqP; split=> x.
    - move/xsectionP=> h.
      change (A (paper_main_take_coordinates k.+1 m
        (gaussian_cons_tuple (Nat.add k m) (a, x))) /\
        B (paper_main_drop_coordinates k.+1 m
        (gaussian_cons_tuple (Nat.add k m) (a, x)))) in h.
      rewrite paper_main_take_coordinates_cons paper_main_drop_coordinates_cons in h.
      case: h => ha hb; split; last exact hb.
      by apply/xsectionP.
    - move=> [/xsectionP ha hb]; apply/xsectionP.
      change (A (paper_main_take_coordinates k.+1 m
        (gaussian_cons_tuple (Nat.add k m) (a, x))) /\
        B (paper_main_drop_coordinates k.+1 m
        (gaussian_cons_tuple (Nat.add k m) (a, x)))).
      by rewrite paper_main_take_coordinates_cons paper_main_drop_coordinates_cons; split.
  under eq_integral do rewrite hs (IH _ (ms _)).
  apply: ge0_integralZr => //.
  exact: measurable_fun_xsection.
Qed.

Theorem paper_main_split_coordinates_law k m (E : set (k.-tuple T * m.-tuple T)) :
  measurable E ->
  gaussian_product_law (Nat.add k m) (paper_main_split_coordinates k m @^-1` E) =
  (gaussian_product_law k \x gaussian_product_law m)%E E.
Proof.
move=> mE.
pose Q := distribution (gaussian_product_law (Nat.add k m))
  (paper_main_split_coordinates k m).
have H : forall X, measurable X ->
    (gaussian_product_law k \x gaussian_product_law m)%E X = Q X.
  apply: product_measure_unique => A B mA mB.
  exact: paper_main_split_coordinates_rectangle.
exact: esym (H E mE).
Qed.

Theorem paper_main_split_coordinates_fubini k m (E : set (k.-tuple T * m.-tuple T)) :
  measurable E ->
  gaussian_product_law (Nat.add k m) (paper_main_split_coordinates k m @^-1` E) =
  (\int[gaussian_product_law k]_h gaussian_product_law m (xsection E h))%E.
Proof. by move=> mE; rewrite paper_main_split_coordinates_law. Qed.

Lemma paper_main_take_coordinates_law k m (A : set (k.-tuple T)) :
  measurable A ->
  gaussian_product_law (Nat.add k m) (paper_main_take_coordinates k m @^-1` A) =
  gaussian_product_law k A.
Proof.
move=> mA.
have H := paper_main_split_coordinates_rectangle k m A setT mA measurableT.
rewrite probability_setT mule1 in H.
have HE : paper_main_split_coordinates k m @^-1` (A `*` [set: m.-tuple T]) =
    paper_main_take_coordinates k m @^-1` A.
  by apply/seteqP; split=> x; [case|move=> h; split].
by rewrite HE in H.
Qed.

Lemma paper_main_split_coordinates_section_bound k m
    (E : set (k.-tuple T * m.-tuple T)) (p : \bar R) :
  measurable E ->
  (forall h, (gaussian_product_law m (xsection E h) <= p)%E) ->
  (gaussian_product_law (Nat.add k m)
    (paper_main_split_coordinates k m @^-1` E) <= p)%E.
Proof.
move=> mE Hp.
have mf : measurable_fun [set: k.-tuple T]
    (fun h => gaussian_product_law m (xsection E h)).
  exact: measurable_fun_xsection.
have HC : (\int[gaussian_product_law k]_h p = p)%E.
  rewrite integral_cst; first exact: measurableT.
  etransitivity; first exact: (congr1 (fun z : \bar R => (p * z)%E) (gpp_mass k)).
  by rewrite mule1.
rewrite paper_main_split_coordinates_fubini // -HC.
apply: ge0_le_integral => //.
Qed.

Definition paper_main_take_points k n d (x : paper_main_sample (k + n) d) :
    paper_main_sample k d :=
  paper_main_take_coordinates (k * d)%N (n * d)%N (tcast (mulnDl k n d) x).

Definition paper_main_split_points k n d (x : paper_main_sample (k + n) d) :
    paper_main_sample k d * paper_main_sample n d :=
  paper_main_split_coordinates (k * d)%N (n * d)%N (tcast (mulnDl k n d) x).

Lemma paper_main_split_pointsE k n d (x : paper_main_sample (k + n) d) :
  paper_main_split_points k n d x =
  (paper_main_take_points k n d x, paper_main_drop_points k n d x).
Proof. by []. Qed.

Lemma paper_main_split_points_measurable k n d :
  measurable_fun [set: paper_main_sample (k + n) d] (paper_main_split_points k n d).
Proof.
exact: (measurableT_comp (paper_main_split_coordinates_measurable _ _)
  (paper_main_tcast_measurable _ _ _)).
Qed.

Theorem paper_main_split_points_law k n d
    (E : set (paper_main_sample k d * paper_main_sample n d)) :
  measurable E ->
  paper_main_probability (k + n) d (paper_main_split_points k n d @^-1` E) =
  (gaussian_product_law (k * d)%N \x gaussian_product_law (n * d)%N)%E E.
Proof.
move=> mE.
change (gaussian_product_law ((k + n) * d)%N
  (tcast (mulnDl k n d) @^-1`
    (paper_main_split_coordinates (k * d)%N (n * d)%N @^-1` E)) =
  (gaussian_product_law (k * d)%N \x gaussian_product_law (n * d)%N)%E E).
rewrite paper_main_tcast_law.
exact: paper_main_split_coordinates_law.
Qed.

Corollary paper_main_split_points_rectangle k n d
    (A : set (paper_main_sample k d)) (B : set (paper_main_sample n d)) :
  measurable A -> measurable B ->
  paper_main_probability (k + n) d
    (paper_main_split_points k n d @^-1` (A `*` B)) =
  (paper_main_probability k d A * paper_main_probability n d B)%E.
Proof.
move=> mA mB.
rewrite (paper_main_split_points_law k n d _ (measurableX mA mB)).
exact: product_measure1E.
Qed.
