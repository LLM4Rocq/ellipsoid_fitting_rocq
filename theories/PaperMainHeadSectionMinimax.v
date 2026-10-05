(* The compact head-section minimax value and its measurability. Let Y be a
   fixed nonempty set of unit vectors y : nat -> R for paper_main_gordon_dot q
   (the dual coordinates), V i and W k matrix-valued data, and
     f(y) = paper_main_head_support (sum_(i < q) y_i V_i)
              (paper_main_head_section kappa W),
     minimax = inf_(y in Y) f(y)            (paper_main_head_section_minimax).
   - The support is 1-Lipschitz in the matrix for the unit-norm section,
     also when the section is empty (both supports are 0)
     (paper_main_head_section_support_lipschitz). So f is Lipschitz in y
     with constant sum_(i < q) |V_i|_F
     (paper_main_head_section_value_lipschitz), and |f(y)| is at most
     sum_(i < q) |V_i|_F when every |y_i| <= 1
     (paper_main_head_section_value_bound).
   - Measurability (paper_main_head_section_minimax_measurable). On any
     measurable space with entrywise measurable W k and V i, each f(., y)
     is measurable (PaperMainHeadSectionMeasurable). With fixed finite
     1/(j+1)-nets of Y (paper_main_gordon_finite_net_exists), c <= minimax
     holds iff c <= f(v) for every net point v, by the Lipschitz bound. So
     every threshold event is a countable intersection of measurable
     events, and the minimax value is a measurable function. The nets do
     not depend on the point of the space, so no measurable selection is
     needed, and sections may be empty. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums
  PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometryHeadFrobenius PaperMainGeometryHeadWidth PaperMainMatrixDuality
  PaperMainGordonProcessCovariance PaperMainGordonNets PaperMainGordonNetExistence
  PaperMainMeasurabilityBox PaperMainFiniteSupportSelector PaperMainHeadSectionMeasurable.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Notation T := (measurableTypeR R).

Definition paper_main_head_section_combination {d : nat} (q : nat) (y : nat -> R)
    (V : nat -> 'M[R]_d) : 'M[R]_d :=
  \sum_(i < q) y i *: V i.

Definition paper_main_head_section_minimax {d m : nat} (kappa : R) (q : nat)
    (Y : (nat -> R) -> Prop) (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) : R :=
  inf [set paper_main_head_support (paper_main_head_section_combination q y V)
    (paper_main_head_section kappa W) | y in Y].

(* The support is 1-Lipschitz in the matrix. *)

Lemma paper_main_head_section_support_le {d m : nat} (kappa : R) (W : 'I_m -> 'M[R]_d)
    (Z1 Z2 : 'M[R]_d) :
  (exists S, paper_main_head_section kappa W S) ->
  paper_main_head_support Z1 (paper_main_head_section kappa W) <=
    paper_main_head_support Z2 (paper_main_head_section kappa W) +
      paper_main_frobenius (Z1 - Z2).
Proof.
move=> [S0 HS0].
have Hunit := @paper_main_head_section_unit d m kappa W.
apply: ge_sup; first by exists (paper_main_pairing Z1 S0), S0.
move=> _ [S HS <-].
have HB := pmh_pairing_frobenius_bound _ (Z1 - Z2) S.
rewrite (Hunit S HS) mulr1 in HB.
have H2 := pmh_support_ge _ Z2 _ S Hunit HS.
have -> : paper_main_pairing Z1 S = paper_main_pairing Z2 S + paper_main_pairing (Z1 - Z2) S.
  by rewrite pmh_pairingBl addrC subrK.
apply: lerD => //; exact: le_trans (ler_norm _) HB.
Qed.

Theorem paper_main_head_section_support_lipschitz {d m : nat} (kappa : R)
    (W : 'I_m -> 'M[R]_d) (Z1 Z2 : 'M[R]_d) :
  `|paper_main_head_support Z1 (paper_main_head_section kappa W) -
    paper_main_head_support Z2 (paper_main_head_section kappa W)| <=
  paper_main_frobenius (Z1 - Z2).
Proof.
have [HNE | HE] := pselect (exists S, paper_main_head_section kappa W S); last first.
  rewrite !paper_main_head_section_support_empty // subrr normr0.
  exact: pmh_frobenius_ge0.
have H1 := paper_main_head_section_support_le kappa W Z1 Z2 HNE.
have H2 := paper_main_head_section_support_le kappa W Z2 Z1 HNE.
rewrite pmh_frobeniusB in H2.
rewrite ler_norml; apply/andP; split.
- by rewrite lerNl opprB lerBlDr addrC.
- by rewrite lerBlDl.
Qed.

(* The Frobenius norm of combinations. *)

Lemma paper_main_head_section_frobenius_sum {d : nat} (q : nat) (F : 'I_q -> 'M[R]_d) :
  paper_main_frobenius (\sum_(i < q) F i) <= \sum_(i < q) paper_main_frobenius (F i).
Proof.
elim/big_rec2: _ => [|i a B _ IH]; first by rewrite pmh_frobenius0.
apply: le_trans (pmh_frobenius_triangle _ _ _) _.
by rewrite lerD2l.
Qed.

Lemma paper_main_head_section_combination_diff {d : nat} q (y y' : nat -> R)
    (V : nat -> 'M[R]_d) :
  paper_main_frobenius (paper_main_head_section_combination q y V -
    paper_main_head_section_combination q y' V) <=
  \sum_(i < q) `|y i - y' i| * paper_main_frobenius (V i).
Proof.
rewrite /paper_main_head_section_combination -sumrB.
have -> : \sum_(i < q) (y i *: V i - y' i *: V i) = \sum_(i < q) ((y i - y' i) *: V i).
  by apply: eq_bigr => i _; rewrite scalerBl.
apply: le_trans (paper_main_head_section_frobenius_sum _ _) _.
by apply: ler_sum => i _; rewrite pmh_frobeniusZ.
Qed.

Lemma paper_main_head_section_combination_norm {d : nat} q (y : nat -> R)
    (V : nat -> 'M[R]_d) :
  paper_main_frobenius (paper_main_head_section_combination q y V) <=
  \sum_(i < q) `|y i| * paper_main_frobenius (V i).
Proof.
rewrite /paper_main_head_section_combination.
apply: le_trans (paper_main_head_section_frobenius_sum _ _) _.
by apply: ler_sum => i _; rewrite pmh_frobeniusZ.
Qed.

(* Coordinates of unit vectors and of net distances. *)

Lemma paper_main_head_section_coord_le q (u : nat -> R) (eps : R) (i : nat) :
  (i < q)%N -> 0 <= eps ->
  paper_main_gordon_dot q u u <= eps ^+ 2 -> `|u i| <= eps.
Proof.
move=> Hi He Hd.
have Hsq : u i ^+ 2 <= paper_main_gordon_dot q u u.
  rewrite /paper_main_gordon_dot paper_main_finite_sum_public.
  under eq_bigr do rewrite RmultE.
  rewrite (bigD1 (Ordinal Hi)) //= -expr2 lerDl.
  by apply: sumr_ge0 => j _; rewrite -expr2 sqr_ge0.
have H := le_trans Hsq Hd.
by rewrite -(ger0_norm He) -sqrtr_sqr -[`|eps|]sqrtr_sqr; apply: ler_wsqrtr.
Qed.

(* Lipschitz bounds in y. *)

Definition paper_main_head_section_tail_norm {d : nat} (q : nat) (V : nat -> 'M[R]_d) : R :=
  \sum_(i < q) paper_main_frobenius (V i).

Lemma paper_main_head_section_tail_norm_ge0 {d : nat} q (V : nat -> 'M[R]_d) :
  0 <= paper_main_head_section_tail_norm q V.
Proof. by apply: sumr_ge0 => i _; exact: pmh_frobenius_ge0. Qed.

Lemma paper_main_head_section_value_lipschitz {d m : nat} (kappa : R) q
    (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) (y y' : nat -> R) (eps : R) :
  0 <= eps -> (forall i, (i < q)%N -> `|y i - y' i| <= eps) ->
  `|paper_main_head_support (paper_main_head_section_combination q y V)
      (paper_main_head_section kappa W) -
    paper_main_head_support (paper_main_head_section_combination q y' V)
      (paper_main_head_section kappa W)| <=
  eps * paper_main_head_section_tail_norm q V.
Proof.
move=> He Hy.
apply: le_trans (paper_main_head_section_support_lipschitz _ _ _ _) _.
apply: le_trans (paper_main_head_section_combination_diff q y y' V) _.
rewrite /paper_main_head_section_tail_norm mulr_sumr.
apply: ler_sum => i _; apply: ler_wpM2r; first exact: pmh_frobenius_ge0.
exact: (Hy i (ltn_ord i)).
Qed.

Lemma paper_main_head_section_value_bound {d m : nat} (kappa : R) q
    (W : 'I_m -> 'M[R]_d) (V : nat -> 'M[R]_d) (y : nat -> R) :
  (forall i, (i < q)%N -> `|y i| <= 1) ->
  `|paper_main_head_support (paper_main_head_section_combination q y V)
      (paper_main_head_section kappa W)| <= paper_main_head_section_tail_norm q V.
Proof.
move=> Hy.
apply: le_trans (paper_main_head_section_support_bound _ _ _) _.
apply: le_trans (paper_main_head_section_combination_norm q y V) _.
apply: ler_sum => i _.
rewrite -[X in _ <= X]mul1r; apply: ler_wpM2r; first exact: pmh_frobenius_ge0.
exact: (Hy i (ltn_ord i)).
Qed.

Lemma paper_main_head_section_unit_coord q (y : nat -> R) (i : nat) :
  (i < q)%N -> paper_main_gordon_dot q y y = 1 -> `|y i| <= 1.
Proof.
move=> Hi H1.
apply: (paper_main_head_section_coord_le q y 1 i Hi ler01).
by rewrite H1 expr1n.
Qed.

(* Measurability on any measurable space. *)

(* The combinations sum_(i < q) y_i V_i are measurable. *)

Lemma paper_main_head_section_combination_measurable {dX : measure_display}
    {X : measurableType dX} {d : nat} q (y : nat -> R) (V : nat -> X -> 'M[R]_d) :
  (forall i a b, measurable_fun [set: X] ((fun x => V i x a b) : X -> T)) ->
  forall a b, measurable_fun [set: X]
    ((fun x => paper_main_head_section_combination q y (fun i => V i x) a b) : X -> T).
Proof.
move=> mV a b.
have -> : (fun x => paper_main_head_section_combination q y (fun i => V i x) a b) =
    (fun x => \sum_(i < q) y i * V i x a b).
  by apply: funext => x; rewrite /paper_main_head_section_combination summxE;
    apply: eq_bigr => i _; rewrite mxE.
by apply: measurable_sum => i; apply: measurable_funM; [exact: measurable_cst | exact: mV].
Qed.

Lemma paper_main_head_section_imp_guard {dX : measure_display} {X : measurableType dX}
    (b : bool) (A : set X) :
  measurable A -> measurable [set x | b -> A x].
Proof.
case: b => mA.
  have -> : [set x | true -> A x] = A.
    by apply/seteqP; split=> x /=; [move=> H; exact: (H isT) | move=> H _; exact: H].
  exact: mA.
have -> : [set x | false -> A x] = setT by apply/seteqP; split=> x //.
exact: measurableT.
Qed.

Lemma paper_main_head_section_seq_lt (t s : nat) : List.In t (List.seq 0 s) <-> (t < s)%N.
Proof.
rewrite List.in_seq; split.
- by move=> [_ H]; apply/ssrnat.ltP; lia.
- by move=> /ssrnat.ltP H; lia.
Qed.

Lemma paper_main_head_section_eps_le (c a B : R) :
  0 <= B -> (forall j : nat, c - j.+1%:R^-1 * B <= a) -> c <= a.
Proof.
move=> HB H; apply: pm_le_of_eps => eps Heps.
have HB1 : 0 < B + 1 by rewrite addrC; exact: ltr_wpDr HB ltr01.
have He : 0 < eps / (B + 1) by rewrite divr_gt0.
have [j Hj] := pm_inv_small _ He.
have Hjb : j.+1%:R^-1 * B < eps.
  have Hj' : j.+1%:R^-1 * (B + 1) < eps by rewrite -ltr_pdivlMr.
  apply: le_lt_trans Hj'; apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  by rewrite lerDl ler01.
have := H j; rewrite lerBlDr => Hc.
apply: le_lt_trans Hc _; by rewrite ltrD2l.
Qed.

Theorem paper_main_head_section_minimax_ge_measurable {dX : measure_display}
    {X : measurableType dX} n m (kappa : R) q (Y : (nat -> R) -> Prop)
    (W : 'I_m -> X -> 'M[R]_(S n)) (V : nat -> X -> 'M[R]_(S n)) (c : R) :
  1 <= kappa -> (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot q y y = 1) ->
  (forall k a b, measurable_fun [set: X] ((fun x => W k x a b) : X -> T)) ->
  (forall i a b, measurable_fun [set: X] ((fun x => V i x a b) : X -> T)) ->
  measurable [set x | c <= paper_main_head_section_minimax kappa q Y
    (fun k => W k x) (fun i => V i x)].
Proof.
move=> Hk HYne HY mW mV.
have Hnets : forall j : nat, exists sv : nat * (nat -> nat -> R),
    paper_main_gordon_finite_net q Y sv.2 (List.seq 0 sv.1) (j.+1%:R^-1).
  move=> j.
  have He : Rlt 0 (j.+1%:R^-1) by apply/RltP; rewrite invr_gt0 ltr0n.
  have [s [v [_ Hnet]]] := paper_main_gordon_finite_net_exists q Y _ He HYne HY.
  by exists (s, v).
have [sv Hsv] := choice Hnets.
pose s := fun j => (sv j).1.
pose v := fun j => (sv j).2.
pose f := fun x y => paper_main_head_support
  (paper_main_head_section_combination q y (fun i => V i x))
  (paper_main_head_section kappa (fun k => W k x)).
have Hf : forall y, measurable_fun [set: X] ((fun x => f x y) : X -> T).
  move=> y.
  exact: (paper_main_head_section_support_measurable n m kappa W
    (fun x => paper_main_head_section_combination q y (fun i => V i x)) Hk mW
    (paper_main_head_section_combination_measurable q y V mV)).
have HvY : forall j t, (t < s j)%N -> Y (v j t).
  move=> j t Ht; apply: (proj1 (Hsv j)).
  exact/(paper_main_head_section_seq_lt t (s j)).
have Hbd : forall x y, Y y ->
    `|f x y| <= paper_main_head_section_tail_norm q (fun i => V i x).
  move=> x y Hy; apply: paper_main_head_section_value_bound => i Hi.
  exact: paper_main_head_section_unit_coord Hi (HY y Hy).
have Hchar : forall x, c <= paper_main_head_section_minimax kappa q Y
    (fun k => W k x) (fun i => V i x) <-> (forall j t, (t < s j)%N -> c <= f x (v j t)).
  move=> x.
  set B := paper_main_head_section_tail_norm q (fun i => V i x).
  set E := [set f x y | y in Y].
  have Hlb : has_lbound E.
    exists (- B) => _ [y Hy <-].
    by have := Hbd x y Hy; rewrite ler_norml => /andP [].
  have [y0 Hy0] := HYne.
  have HE : E !=set0 by exists (f x y0), y0.
  split.
  - move=> Hc j t Ht.
    apply: le_trans Hc _.
    by apply: (ge_inf Hlb); exists (v j t) => //; exact: HvY.
  - move=> H; apply: lb_le_inf HE _ => _ [y Hy <-].
    have HB0 : 0 <= B by exact: paper_main_head_section_tail_norm_ge0.
    apply: (paper_main_head_section_eps_le _ _ B HB0) => j.
    have [t [Ht Hdist]] := (proj2 (Hsv j)) y Hy.
    have Ht' : (t < s j)%N by exact/(paper_main_head_section_seq_lt t (s j)).
    have Hj0 : 0 <= j.+1%:R^-1 :> R by rewrite invr_ge0 ler0n.
    have Hcoord : forall i, (i < q)%N -> `|y i - v j t i| <= j.+1%:R^-1.
      move=> i Hi.
      apply: (paper_main_head_section_coord_le q (fun i => y i - v j t i) _ i Hi Hj0).
      by apply/RleP; rewrite -RpowE.
    have HL := paper_main_head_section_value_lipschitz kappa q (fun k => W k x)
      (fun i => V i x) y (v j t) _ Hj0 Hcoord.
    have Hcv := H j t Ht'.
    move: HL; rewrite ler_norml => /andP [HL1 _].
    move: HL1; rewrite lerNl opprB lerBlDl => HL1.
    rewrite lerBlDr; apply: le_trans Hcv _.
    by rewrite -lerBlDr; move: HL1; rewrite lerBlDl addrC.
have -> : [set x | c <= paper_main_head_section_minimax kappa q Y
      (fun k => W k x) (fun i => V i x)] =
    \bigcap_(j : nat) \bigcap_(t : nat) [set x | (t < s j)%N -> c <= f x (v j t)].
  apply/seteqP; split=> x Hx.
  - by move=> j _ t _ Ht; exact: ((Hchar x).1 Hx j t Ht).
  - by apply/(Hchar x) => j t Ht; exact: (Hx j I t I Ht).
apply: bigcapT_measurable => j; apply: bigcapT_measurable => t.
apply: paper_main_head_section_imp_guard.
apply: paper_main_head_section_le_measurable; last exact: Hf.
exact: measurable_cst.
Qed.

Theorem paper_main_head_section_minimax_measurable {dX : measure_display}
    {X : measurableType dX} n m (kappa : R) q (Y : (nat -> R) -> Prop)
    (W : 'I_m -> X -> 'M[R]_(S n)) (V : nat -> X -> 'M[R]_(S n)) :
  1 <= kappa -> (exists y, Y y) -> (forall y, Y y -> paper_main_gordon_dot q y y = 1) ->
  (forall k a b, measurable_fun [set: X] ((fun x => W k x a b) : X -> T)) ->
  (forall i a b, measurable_fun [set: X] ((fun x => V i x a b) : X -> T)) ->
  measurable_fun [set: X] ((fun x => paper_main_head_section_minimax kappa q Y
    (fun k => W k x) (fun i => V i x)) : X -> T).
Proof.
move=> Hk HYne HY mW mV.
apply: paper_main_head_section_measurable_fun_ge => c.
exact: paper_main_head_section_minimax_ge_measurable.
Qed.
