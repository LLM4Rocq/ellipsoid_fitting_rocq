From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.

(**md**************************************************************************)
(* # Conditioning a product law on a set of coordinates                       *)
(*                                                                            *)
(* Under the product law tuple_prod mu n of n independent coordinates, the    *)
(* coordinates outside a set S may be resampled independently of those in S   *)
(* (ge0_integral_tuple_prod_merge). This gives, without conditional           *)
(* expectations, the tools of a proof that reveals the coordinates in         *)
(* stages, as the proof of Proposition 3.4 of Koehler and Sohn (arXiv         *)
(* 2608.27372, lines 3610-3805) does. An event E depends only on the          *)
(* coordinates in S when replacing the others does not change it:             *)
(* E (tuple_merge S x y) = E x for all x and y.                               *)
(* - tuple_prod_box, measure_tuple_box_unique: the measure of a box is the    *)
(*   product of the measures of its sides, and two finite measures on the     *)
(*   n-tuples that agree on the boxes agree.                                  *)
(* - tuple_prod_merge: resampling the coordinates outside S does not change   *)
(*   tuple_prod mu n.                                                         *)
(* - tuple_prod_cond_le: if H depends only on the coordinates in S and, for   *)
(*   every x in H, resampling the coordinates of x outside S puts it in E     *)
(*   with probability at most c x, then P(E and H) <= int_H c.                *)
(* - tuple_prod_indepS, tuple_prod_indep_big: events that depend on           *)
(*   pairwise disjoint sets of coordinates are independent.                   *)
(* - tuple_prod_chain_le: if the coordinates are revealed in nested sets      *)
(*   S 0, S 1, ..., the event A l depends only on the coordinates in S l.+1   *)
(*   and, given the coordinates in S l of a tuple of the earlier events, has  *)
(*   probability at most c l, then the A l, l < L, occur together with        *)
(*   probability at most the product of the c l.                              *)
(* - tuple_prod_pick: for an injective f, the coordinates f 0, ..., f (k - 1) *)
(*   of tuple_prod mu n have the product law of their laws.                   *)
(*                                                                            *)
(* ```                                                                        *)
(*       tuple_box A == the n-tuples x with x_i in A i for every i            *)
(* tuple_merge S x y == the n-tuple with the coordinates of x in S and those  *)
(*                      of y outside S                                        *)
(*    tuple_pick f x == the k-tuple (x_(f 0), ..., x_(f (k - 1)))             *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_box.
Context d (T : measurableType d) (n : nat).

(* The product of the sets A i. *)
Definition tuple_box (A : 'I_n -> set T) : set (n.-tuple T) :=
  [set x | forall i, A i (tnth x i)].

Definition tuple_boxes : set (set (n.-tuple T)) :=
  [set tuple_box A | A in [set A | forall i, measurable (A i)]].

Lemma tuple_boxE (A : 'I_n -> set T) :
  tuple_box A = \bigcap_(i in [set: 'I_n]) ((@tnth n T)^~ i @^-1` A i).
Proof. by apply/seteqP; split => x /= h i; [move=> _|]; exact: h. Qed.

Lemma measurable_tuple_box (A : 'I_n -> set T) :
  (forall i, measurable (A i)) -> measurable (tuple_box A).
Proof.
move=> mA; rewrite tuple_boxE.
apply: fin_bigcap_measurable; first exact: finite_finset.
move=> i _; have := measurable_tnth i measurableT (mA i).
by rewrite setTI.
Qed.

Lemma measurable_tuple_boxes : @measurable _ (n.-tuple T) = <<s tuple_boxes >>.
Proof.
apply/seteqP; split; last first.
  apply: smallest_sub; first exact: sigma_algebra_measurable.
  by move=> _ [A mA <-]; exact: measurable_tuple_box.
apply: smallest_sub; first exact: smallest_sigma_algebra.
rewrite -bigcup_seq; apply: bigcup_sub => i _ _ [B mB <-]; rewrite setTI.
apply: sub_sigma_algebra.
exists (fun j => if j == i then B else [set: T]).
  by move=> j; case: ifP.
apply/seteqP; split=> x /=.
  by move=> /(_ i); rewrite eqxx.
by move=> xB j; case: ifPn => // /eqP ->.
Qed.

Lemma setI_closed_tuple_boxes : setI_closed tuple_boxes.
Proof.
move=> _ _ [A mA <-] [B mB <-].
exists (fun i => A i `&` B i); first by move=> i; exact: measurableI.
by apply/seteqP; split => x /=; [move=> h; split => i; case: (h i)|
  move=> [hA hB] i; split].
Qed.

(* Two finite measures that agree on the boxes agree. *)
Lemma measure_tuple_box_unique (R : realType)
    (mu1 mu2 : {measure set (n.-tuple T) -> \bar R}) :
  (mu1 [set: n.-tuple T] < +oo)%E ->
  (forall A, (forall i, measurable (A i)) ->
    mu1 (tuple_box A) = mu2 (tuple_box A)) ->
  forall X, measurable X -> mu1 X = mu2 X.
Proof.
move=> mu1T mu12.
have boxT : tuple_box (fun=> [set: T]) = [set: n.-tuple T].
  by apply/seteqP; split.
apply: (measure_unique tuple_boxes (fun=> [set: n.-tuple T])).
- exact: measurable_tuple_boxes.
- exact: setI_closed_tuple_boxes.
- by move=> _; rewrite -boxT; exists (fun _ => [set: T]).
- by rewrite bigcup_const.
- by move=> _ [A mA <-]; exact: mu12.
- by move=> _.
Qed.

End tuple_box.

Section tuple_prod_box.
Context d (T : measurableType d) (R : realType).

(* tuple_prod mu n gives a box the product of the measures of its sides. *)
Lemma tuple_prod_box (mu : nat -> probability T R) n (A : 'I_n -> set T) :
  (forall i, measurable (A i)) ->
  tuple_prod mu n (tuple_box A) = (\prod_(i < n) mu i (A i))%E.
Proof.
elim: n mu A => [|n IH] mu A mA.
  rewrite big_ord0 /= (_ : tuple_box A = [set: 0.-tuple T]).
    by apply/seteqP; split => // x _ [].
  by rewrite diracE in_setT.
rewrite /= /distribution /= (_ : @tuple_cons d T n @^-1` tuple_box A =
    A ord0 `*` tuple_box (fun i => A (lift ord0 i))).
  apply/seteqP; split => [[t v] /= H|[t v] [/= H0 H1] i].
    split; first by have := H ord0.
    by move=> i; have := H (lift ord0 i); rewrite /tuple_cons tnthS.
  case: (unliftP ord0 i) => [j ->|->] //.
  by rewrite /tuple_cons tnthS; exact: H1.
rewrite product_measure1E //; last first.
  rewrite big_ord_recl; congr (_ * _)%E.
  exact: (IH (fun i => mu i.+1) (fun i : 'I_n => A (lift ord0 i))
    (fun i => mA _)).
by apply: measurable_tuple_box => i; exact: mA.
Qed.

End tuple_prod_box.

Section tuple_merge.
Context d (T : measurableType d) (R : realType) (n : nat).
Variable S : {pred 'I_n}.

(* The coordinates in S from x, the others from y. *)
Definition tuple_merge (x y : n.-tuple T) : n.-tuple T :=
  [tuple if i \in S then tnth x i else tnth y i | i < n].

Lemma tnth_merge x y i :
  tnth (tuple_merge x y) i = if i \in S then tnth x i else tnth y i.
Proof. by rewrite tnth_mktuple. Qed.

Lemma measurable_tuple_merge :
  measurable_fun setT (fun p : n.-tuple T * n.-tuple T => tuple_merge p.1 p.2).
Proof.
apply/measurable_fun_tnthP => i.
have -> : (tnth (T:=T))^~ i \o
    (fun p : n.-tuple T * n.-tuple T => tuple_merge p.1 p.2) =
    (fun p : n.-tuple T * n.-tuple T =>
      if i \in S then tnth p.1 i else tnth p.2 i).
  by apply: boolp.funext => p; rewrite /= tnth_merge.
case: (i \in S).
  exact: (measurableT_comp (measurable_tnth i) measurable_fst).
exact: (measurableT_comp (measurable_tnth i) measurable_snd).
Qed.

Local Open Scope ereal_scope.

(* Resampling the coordinates outside S does not change a product law. *)
Lemma tuple_prod_merge (mu : nat -> probability T R) (X : set (n.-tuple T)) :
  measurable X ->
  (tuple_prod mu n \x tuple_prod mu n)
    ((fun p : n.-tuple T * n.-tuple T => tuple_merge p.1 p.2) @^-1` X) =
  tuple_prod mu n X.
Proof.
move=> mX.
pose g : {mfun (n.-tuple T * n.-tuple T)%type >-> n.-tuple T} :=
  HB.pack (fun p : n.-tuple T * n.-tuple T => tuple_merge p.1 p.2)
    (isMeasurableFun.Build _ _ _ _ _ measurable_tuple_merge).
have h := @measure_tuple_box_unique d T n R
  (distribution (tuple_prod mu n \x tuple_prod mu n) g) (tuple_prod mu n).
apply: h => //; first by rewrite (le_lt_trans (probability_le1 _ _)) ?ltry.
move=> A mA.
have m1 i : d.-measurable (if i \in S then A i else [set: T]).
  by case: ifP.
have m2 i : d.-measurable (if i \in S then [set: T] else A i).
  by case: ifP.
have mb1 := measurable_tuple_box m1; have mb2 := measurable_tuple_box m2.
rewrite /= /distribution /= (_ : _ @^-1` _ =
  tuple_box (fun i => if i \in S then A i else [set: T]) `*`
  tuple_box (fun i => if i \in S then [set: T] else A i)).
  apply/seteqP; split => [[x y] /= h1|[x y] [/= h1 h2] i].
    by split => i; have := h1 i; rewrite tnth_merge; case: (i \in S).
  by rewrite tnth_merge; have := h1 i; have := h2 i; case: (i \in S).
rewrite product_measure1E //.
apply: eq_trans (congr2 (fun a b => (a * b)%E) (tuple_prod_box mu m1)
  (tuple_prod_box mu m2)) _.
rewrite (tuple_prod_box mu mA) -big_split /=; apply: eq_bigr => i _.
by case: (i \in S); rewrite probability_setT ?mule1 ?mul1e.
Qed.

End tuple_merge.

Section tuple_condition.
Context d (T : measurableType d) (R : realType) (n : nat).
Variable S : {pred 'I_n}.
Local Open Scope ereal_scope.

(* The coordinates outside S may be resampled independently. *)
Lemma ge0_integral_tuple_prod_merge (mu : nat -> probability T R)
    (F : n.-tuple T -> \bar R) :
  measurable_fun setT F -> (forall x, 0 <= F x) ->
  \int[tuple_prod mu n]_x F x =
  \int[tuple_prod mu n]_x \int[tuple_prod mu n]_y F (tuple_merge S x y).
Proof.
move=> mF F0.
have mFm : measurable_fun setT
    (fun p : n.-tuple T * n.-tuple T => F (tuple_merge S p.1 p.2)).
  exact: measurableT_comp mF (measurable_tuple_merge S).
rewrite (@ge0_integral_image _ _ _ _ R (tuple_prod mu n \x tuple_prod mu n)
  (tuple_prod mu n) (fun p => tuple_merge S p.1 p.2) F) //.
- exact: measurable_tuple_merge.
- by move=> A mA; symmetry; exact: tuple_prod_merge.
have := @fubini_tonelli1 _ _ _ _ R (tuple_prod mu n) (tuple_prod mu n) _ mFm
  (fun p => F0 _).
by move=> ->.
Qed.

Lemma measurable_merge_section (E : set (n.-tuple T)) (x : n.-tuple T) :
  measurable E -> measurable [set y | E (tuple_merge S x y)].
Proof.
move=> mE.
have mm : measurable_fun setT (fun y : n.-tuple T => tuple_merge S x y).
  apply: (eq_measurable_fun
    ((fun p : n.-tuple T * n.-tuple T => tuple_merge S p.1 p.2) \o
     (fun y : n.-tuple T => (x, y)))) => //.
  apply: measurableT_comp; first exact: measurable_tuple_merge.
  exact: pair1_measurable.
by have := mm measurableT E mE; rewrite setTI.
Qed.

(* If H depends only on the coordinates in S and, for x in H, resampling
   the coordinates outside S puts the tuple in E with probability at most
   c x, then E and H occur together with probability at most the integral
   of c over H. *)
Lemma tuple_prod_cond_le (mu : nat -> probability T R)
    (E H : set (n.-tuple T)) (c : n.-tuple T -> \bar R) :
  measurable E -> measurable H -> measurable_fun setT c ->
  (forall x, 0 <= c x) ->
  (forall x y, H (tuple_merge S x y) = H x) ->
  (forall x, H x -> tuple_prod mu n [set y | E (tuple_merge S x y)] <= c x) ->
  tuple_prod mu n (E `&` H) <= \int[tuple_prod mu n]_(x in H) c x.
Proof.
move=> mE mH mc c0 HS hc.
have mEH := measurableI _ _ mE mH.
have mI : measurable_fun setT (fun z => (\1_(E `&` H) z : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have mIm : measurable_fun setT (fun p : n.-tuple T * n.-tuple T =>
    (\1_(E `&` H) (tuple_merge S p.1 p.2) : R)%:E).
  exact: measurableT_comp mI (measurable_tuple_merge S).
have I0 (p : n.-tuple T * n.-tuple T) :
    (0 <= (\1_(E `&` H) (tuple_merge S p.1 p.2) : R)%:E)%E.
  by rewrite lee_fin.
rewrite -[X in tuple_prod mu n X]setIT -integral_indic //.
rewrite ge0_integral_tuple_prod_merge //.
rewrite [X in _ <= X]integral_mkcond.
apply: ge0_le_integral => //.
- by move=> x _; apply: integral_ge0 => y _; rewrite lee_fin.
- have := @measurable_fun_fubini_tonelli_F _ _ _ _ R (tuple_prod mu n) _
    mIm I0.
  by apply.
- by apply/(measurable_restrictT _ _).1 => //; exact: measurable_funTS.
move=> x _; rewrite patchE; case: ifPn => [xH|xH].
  move: xH; rewrite inE => xH.
  apply: le_trans (hc x xH).
  have mEx := measurable_merge_section x mE.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  transitivity (\int[tuple_prod mu n]_y
      (\1_[set y | E (tuple_merge S x y)] y : R)%:E).
    apply: eq_integral => y _; rewrite !indicE; congr ((_%:R)%:E).
    case: (pselect (E (tuple_merge S x y))) => hE;
      [rewrite !mem_set //; split => //; rewrite HS|
       rewrite !memNset // => -[]].
      exact: xH.
    by move=> /hE.
  by rewrite integral_indic // setIT.
have -> : (\int[tuple_prod mu n]_y
    (\1_(E `&` H) (tuple_merge S x y) : R)%:E = 0)%E.
  apply: integral0_eq => y _; rewrite indicE memNset //.
  move=> [_]; rewrite HS => Hx; move/negP: xH; apply.
  exact: mem_set.
by [].
Qed.

(* Events that depend on the coordinates in S and outside S are
   independent. *)
Lemma tuple_prod_indepS (mu : nat -> probability T R)
    (E F : set (n.-tuple T)) :
  measurable E -> measurable F ->
  (forall x y, E (tuple_merge S x y) = E x) ->
  (forall x y, F (tuple_merge S x y) = F y) ->
  tuple_prod mu n (E `&` F) = tuple_prod mu n E * tuple_prod mu n F.
Proof.
move=> mE mF ES FS.
have mEF := measurableI _ _ mE mF.
have mI : measurable_fun setT (fun z => (\1_(E `&` F) z : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have mIE : measurable_fun setT (fun z => (\1_E z : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
have mIF : measurable_fun setT (fun z => (\1_F z : R)%:E).
  by apply/measurable_EFinP; exact: measurable_indic.
rewrite -[X in tuple_prod mu n X]setIT -integral_indic //.
rewrite ge0_integral_tuple_prod_merge //.
transitivity (\int[tuple_prod mu n]_x ((\1_E x : R)%:E * tuple_prod mu n F)).
  apply: eq_integral => x _.
  transitivity (\int[tuple_prod mu n]_y ((\1_E x : R)%:E * (\1_F y : R)%:E)).
    apply: eq_integral => y _; rewrite -EFinM !indicE.
    case: (pselect (E x)) => hE; case: (pselect (F y)) => hF.
    - by rewrite !mem_set ?mulr1 //; split; rewrite ?ES ?FS.
    - by rewrite memNset ?(memNset hF) ?mulr0 // => -[_]; rewrite FS.
    - by rewrite memNset ?(memNset hE) ?mul0r // => -[]; rewrite ES.
    - by rewrite memNset ?(memNset hE) ?mul0r // => -[]; rewrite ES.
  by rewrite ge0_integralZl // integral_indic // setIT.
by rewrite ge0_integralZr // integral_indic // setIT.
Qed.

End tuple_condition.

Section tuple_dep.
Context d (T : measurableType d) (n : nat).

Lemma tuple_merge_id (S : {pred 'I_n}) (x y : n.-tuple T) :
  (forall i, i \in S -> tnth x i = tnth y i) -> tuple_merge S x y = y.
Proof.
move=> h; apply: eq_from_tnth => i; rewrite tnth_merge.
by case: ifPn => // /h.
Qed.

(* An event that depends only on the coordinates in S depends only on the
   coordinates in any U that contains S. *)
Lemma tuple_merge_dep_sub (S U : {pred 'I_n}) (E : set (n.-tuple T)) :
  (forall x y, E (tuple_merge S x y) = E x) -> {subset S <= U} ->
  forall x y, E (tuple_merge U x y) = E x.
Proof.
move=> ES SU x y.
have h : tuple_merge S (tuple_merge U x y) x = x.
  by apply: tuple_merge_id => i iS; rewrite tnth_merge (SU _ iS).
by rewrite -[in RHS]h ES.
Qed.

(* It does not depend on the coordinates in a U disjoint from S. *)
Lemma tuple_merge_dep_disj (S U : {pred 'I_n}) (E : set (n.-tuple T)) :
  (forall x y, E (tuple_merge S x y) = E x) ->
  (forall i, i \in S -> i \notin U) ->
  forall x y, E (tuple_merge U x y) = E y.
Proof.
move=> ES SU x y.
have h : tuple_merge S (tuple_merge U x y) y = y.
  by apply: tuple_merge_id => i iS; rewrite tnth_merge (negbTE (SU _ iS)).
by rewrite -[in RHS]h ES.
Qed.

End tuple_dep.

Section tuple_indep.
Context d (T : measurableType d) (R : realType) (n : nat).
Local Open Scope ereal_scope.

(* Events that depend on pairwise disjoint sets of coordinates are
   independent. *)
Lemma tuple_prod_indep_big (mu : nat -> probability T R) k
    (S : nat -> {pred 'I_n}) (E : nat -> set (n.-tuple T)) :
  (forall j, (j < k)%N -> measurable (E j)) ->
  (forall j j' i, (j < k)%N -> (j' < k)%N -> j != j' -> i \in S j ->
     i \notin S j') ->
  (forall j x y, (j < k)%N -> E j (tuple_merge (S j) x y) = E j x) ->
  tuple_prod mu n (\bigcap_(j < k) E j) = \prod_(j < k) tuple_prod mu n (E j).
Proof.
elim: k => [|k IH] mE dS ES.
  by rewrite bigcap_mkord !big_ord0 probability_setT.
rewrite bigcap_mkord big_ord_recr /= -bigcap_mkord big_ord_recr /=.
pose U : {pred 'I_n} := [pred i | [exists j : 'I_k, i \in S j]].
have mI : measurable (\bigcap_(j < k) E j).
  rewrite bigcap_mkord; apply: big_ind => //; first exact: measurableI.
  by move=> j _; apply: mE; rewrite ltnS ltnW.
rewrite (@tuple_prod_indepS d T R n U mu) //; last 3 first.
- move=> x y; apply/propext.
  have hU j : (j < k)%N -> E j (tuple_merge U x y) = E j x.
    move=> jk; have jk' : (j < k.+1)%N by rewrite ltnS ltnW.
    apply: (tuple_merge_dep_sub (fun a b => ES j a b jk')).
    by move=> i iS; apply/existsP; exists (Ordinal jk).
  by split => h j /= jk; [rewrite -hU|rewrite hU] => //; exact: h.
- apply: (tuple_merge_dep_disj (fun a b => ES k a b (ltnSn k))) => i iS.
  apply/existsP => -[j ijS].
  have kj : k != j by rewrite eq_sym ltn_eqF.
  have := dS k j i (ltnSn k) (ltnW (ltn_ord j)) kj iS.
  by rewrite ijS.
- congr (_ * _); apply: IH => [j jk|j j' i jk j'k|j x y jk].
  + by apply: mE; rewrite ltnS ltnW.
  + by apply: dS; rewrite ltnS ltnW.
  + by apply: ES; rewrite ltnS ltnW.
- exact: mE.
Qed.

(* Revealing the coordinates in nested sets S 0, S 1, ...: if the event A l
   depends only on the coordinates in S l.+1 and, given the coordinates in
   S l of a tuple of the earlier events, has probability at most c l, then
   the events A l, l < L, occur together with probability at most the
   product of the c l. *)
Lemma tuple_prod_chain_le (mu : nat -> probability T R) L
    (S : nat -> {pred 'I_n}) (A : nat -> set (n.-tuple T)) (c : nat -> R) :
  (forall l, (l < L)%N -> measurable (A l)) ->
  (forall l, {subset S l <= S l.+1}) ->
  (forall l x y, (l < L)%N -> A l (tuple_merge (S l.+1) x y) = A l x) ->
  (forall l, (l < L)%N -> (0 <= c l)%R) ->
  (forall l x, (l < L)%N -> (\bigcap_(r < l) A r) x ->
     tuple_prod mu n [set y | A l (tuple_merge (S l) x y)] <= (c l)%:E) ->
  tuple_prod mu n (\bigcap_(l < L) A l) <= (\prod_(l < L) c l)%:E.
Proof.
move=> mA SS AS c0 hc.
have Smono a b : (a <= b)%N -> {subset S a <= S b}.
  move=> /subnK <-; elim: (b - a)%N => // k IHk i /IHk.
  by rewrite addSn; exact: SS.
elim: L mA AS c0 hc => [|L IH] mA AS c0 hc.
  by rewrite bigcap_mkord !big_ord0 probability_setT.
have mH : measurable (\bigcap_(r < L) A r).
  rewrite bigcap_mkord; apply: big_ind => //; first exact: measurableI.
  by move=> j _; apply: mA; rewrite ltnS ltnW.
have HS x y : (\bigcap_(r < L) A r) (tuple_merge (S L) x y) =
    (\bigcap_(r < L) A r) x.
  apply/propext.
  have hU r : (r < L)%N -> A r (tuple_merge (S L) x y) = A r x.
    move=> rL; have rL' : (r < L.+1)%N by rewrite ltnS ltnW.
    exact: (tuple_merge_dep_sub (fun a b => AS r a b rL') (Smono _ _ rL)).
  by split => h r /= rL; [rewrite -hU|rewrite hU] => //; exact: h.
rewrite bigcap_mkord big_ord_recr /= -bigcap_mkord setIC big_ord_recr /=.
apply: le_trans (@tuple_prod_cond_le d T R n (S L) mu (A L) _
  (fun=> (c L)%:E) (mA L (ltnSn L)) mH (measurable_cst _) _ HS _) _.
- by move=> _; rewrite lee_fin c0.
- by move=> x hx; exact: hc.
rewrite integral_cst // EFinM muleC.
apply: lee_wpmul2r; first by rewrite lee_fin c0.
apply: IH => [l lL|l x y lL|l lL|l x lL hx].
- by apply: mA; rewrite ltnS ltnW.
- by apply: AS; rewrite ltnS ltnW.
- by apply: c0; rewrite ltnS ltnW.
- by apply: hc => //; rewrite ltnS ltnW.
Qed.

End tuple_indep.

Section tuple_pick.
Context d (T : measurableType d) (R : realType) (n k : nat).
Variable f : 'I_k -> 'I_n.

(* The coordinates f 0, ..., f (k - 1) of x. *)
Definition tuple_pick (x : n.-tuple T) : k.-tuple T :=
  [tuple tnth x (f i) | i < k].

Lemma measurable_tuple_pick : measurable_fun setT tuple_pick.
Proof.
apply/measurable_fun_tnthP => i.
have -> : (tnth (T:=T))^~ i \o tuple_pick = (tnth (T:=T))^~ (f i).
  by apply: boolp.funext => x; rewrite /= tnth_mktuple.
exact: measurable_tnth.
Qed.

(* For an injective f, the coordinates f 0, ..., f (k - 1) of a product law
   have the product law of their laws. *)
Lemma tuple_prod_pick (mu nu : nat -> probability T R)
    (B : set (k.-tuple T)) :
  injective f -> (forall i : 'I_k, nu i = mu (f i)) -> measurable B ->
  tuple_prod mu n (tuple_pick @^-1` B) = tuple_prod nu k B.
Proof.
move=> finj hnu mB.
pose g : {mfun n.-tuple T >-> k.-tuple T} :=
  HB.pack tuple_pick (isMeasurableFun.Build _ _ _ _ _ measurable_tuple_pick).
have h := @measure_tuple_box_unique d T k R
  (distribution (tuple_prod mu n) g) (tuple_prod nu k).
apply: h => //; first by rewrite (le_lt_trans (probability_le1 _ _)) ?ltry.
move=> A mA.
pose A' (l : 'I_n) : set T := [set t | forall i, f i = l -> A i t].
have mA' l : measurable (A' l).
  rewrite (_ : A' l = \bigcap_(i in [set i | f i = l]) A i).
    by apply/seteqP; split => t /= h i; [move=> /h|move=> /(h i)].
  apply: fin_bigcap_measurable => [|i _]; last exact: mA.
  by apply: (sub_finite_set (subsetT _)); exact: finite_finset.
transitivity (tuple_prod mu n (tuple_box A')).
  rewrite [LHS](_ : _ = tuple_prod mu n (g @^-1` tuple_box A)) //.
  congr (tuple_prod mu n _); apply/seteqP; split => x /= h.
    by move=> l i <-; have := h i; rewrite /tuple_pick tnth_mktuple.
  by move=> i; rewrite /tuple_pick tnth_mktuple; exact: h.
apply: eq_trans (tuple_prod_box mu mA') _.
apply: eq_trans _ (esym (tuple_prod_box nu mA)).
rewrite [RHS](partition_big f predT) //=.
apply: eq_bigr => l _.
have [[i0 fi0]|nf] := pselect (exists i, f i = l).
  have e : (fun i : 'I_k => f i == l) =1 pred1 i0.
    by move=> i /=; apply/eqP/eqP => [fil|->//]; apply: finj; rewrite fil fi0.
  rewrite (big_pred1 i0) // hnu fi0; congr (mu l _).
  apply/seteqP; split => t /= h; first exact: h.
  by move=> i fil; rewrite (finj i i0 _) // fil fi0.
have e : (fun i : 'I_k => f i == l) =1 xpred0.
  by move=> i /=; apply/eqP => fil; apply: nf; exists i.
rewrite big_pred0 // (_ : A' l = setT) ?probability_setT //.
by apply/seteqP; split => // t _ i fil; exfalso; apply: nf; exists i.
Qed.

End tuple_pick.
