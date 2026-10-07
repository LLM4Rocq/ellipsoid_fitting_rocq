From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg.

(**md**************************************************************************)
(* # Product laws by blocks                                                   *)
(*                                                                            *)
(* A tuple of n * d coordinates read as n rows of d coordinates, row i being  *)
(* made of the coordinates i * d + j for j < d, as the samples of the         *)
(* ellipsoid fitting papers are read.                                         *)
(*                                                                            *)
(* ```                                                                        *)
(*   row_index i j == the index i * d + j of 'I_(n * d), for i : 'I_n and     *)
(*                    j : 'I_d                                                *)
(* tuple_rows n d x == the n rows of length d of the (n * d)-tuple x          *)
(*    tuple_map g x == [tuple g i (tnth x i) | i < n], for x : n.-tuple T and *)
(*                     g : nat -> T -> T'                                     *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - ge0_integral_tuple_prodS, integral_tuple_prodS: Fubini for the first     *)
(*   coordinate, \int[tuple_prod mu n.+1] F =                                 *)
(*   \int[mu 0]_t \int[tuple_prod (fun i => mu i.+1) n]_ts F (t :: ts), for F *)
(*   nonnegative and measurable, or integrable (integrable_tuple_prodS); the  *)
(*   lemmas of lindeberg.v state it for bounded F;                            *)
(* - ge0_integral_tuple_prod_prod: independent coordinates, the integral of   *)
(*   \prod_i f_i (x_i) against tuple_prod mu n is the product of the          *)
(*   integrals of the f_i against the mu i, for f_i nonnegative and           *)
(*   measurable;                                                              *)
(* - ge0_integral_image: the integral against a law mu that is the image of   *)
(*   nu under a measurable g is the integral of f \o g against nu;            *)
(* - coordinatewise maps preserve independence: if mu i is the image of nu i  *)
(*   under a measurable g i for every i, then tuple_prod mu n is the image of *)
(*   tuple_prod nu n under tuple_map g (tuple_prod_map), so that the integral *)
(*   of a measurable G against tuple_prod mu n is the integral of             *)
(*   x |-> G (tuple_map g x) against tuple_prod nu n (ge0_integral_tuple_map, *)
(*   integral_tuple_map, Rintegral_tuple_map), and integrable_tuple_map;      *)
(* - blocks: Fubini for the first a and the last b coordinates,               *)
(*   \int[tuple_prod mu (a + b)] F =                                          *)
(*   \int[tuple_prod mu a]_x \int[tuple_prod (fun i => mu (a + i)) b]_y       *)
(*   F [tuple of x ++ y] (ge0_integral_tuple_prod_cat), so disjoint blocks    *)
(*   are independent with the product laws of their coordinates;              *)
(* - rows: the image of tuple_prod mu (n * m) under tuple_rows n m is the     *)
(*   product over i < n of the laws tuple_prod (fun j => mu (i * m + j)) m of *)
(*   the rows (tuple_prod_rows, ge0_integral_tuple_rows,                      *)
(*   integral_tuple_rows);                                                    *)
(* - eq_tuple_prod: tuple_prod mu n depends only on mu 0, ..., mu (n - 1).    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section tuple_rows.
Context (T : Type) (n d : nat).

Lemma row_index_subproof (i : 'I_n) (j : 'I_d) : (i * d + j < n * d)%N.
Proof.
rewrite (@leq_trans (i * d + d)) ?ltn_add2l // -mulSnr.
by rewrite leq_mul2r ltn_ord orbT.
Qed.

Definition row_index (i : 'I_n) (j : 'I_d) : 'I_(n * d) :=
  Ordinal (row_index_subproof i j).

Definition tuple_rows (x : (n * d).-tuple T) : n.-tuple (d.-tuple T) :=
  [tuple [tuple tnth x (row_index i j) | j < d] | i < n].

End tuple_rows.
Arguments tuple_rows {T} n d x.

Section tuple_prod_integral.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* Fubini for the first coordinate, for nonnegative functions. *)
Lemma ge0_integral_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  measurable_fun [set: n.+1.-tuple T] F -> (forall x, 0 <= F x) ->
  \int[tuple_prod mu n.+1]_x F x =
  \int[mu 0%N]_t
    \int[tuple_prod (fun i => mu i.+1) n]_ts F (tuple_cons (t, ts)).
Proof.
move=> mF F0 /=.
rewrite [LHS](@ge0_integral_distribution _ _ _ _ _
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
rewrite fubini_tonelli1//; first exact: measurableT_comp.
by move=> ?; exact: F0.
Qed.

Lemma integrable_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  measurable_fun [set: n.+1.-tuple T] F ->
  (tuple_prod mu n.+1).-integrable [set: n.+1.-tuple T] F <->
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n).-integrable
    [set: T * n.-tuple T] (F \o @tuple_cons _ T n).
Proof.
move=> mF.
have mFc : measurable_fun [set: T * n.-tuple T] (F \o @tuple_cons _ T n).
  exact: measurableT_comp.
have E : \int[tuple_prod mu n.+1]_x `|F x| =
    \int[mu 0%N \x tuple_prod (fun i => mu i.+1) n]_p
      `|(F \o @tuple_cons _ T n) p|.
  rewrite [LHS](@ge0_integral_distribution _ _ _ _ _
    (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
  exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

(* Fubini for the first coordinate, for integrable functions. *)
Lemma integral_tuple_prodS (mu : nat -> probability T R) n
    (F : n.+1.-tuple T -> \bar R) :
  (tuple_prod mu n.+1).-integrable [set: n.+1.-tuple T] F ->
  \int[tuple_prod mu n.+1]_x F x =
  \int[mu 0%N]_t
    \int[tuple_prod (fun i => mu i.+1) n]_ts F (tuple_cons (t, ts)).
Proof.
move=> Fi; have mF := measurable_int _ Fi.
have Fci := (integrable_tuple_prodS mu mF).1 Fi.
rewrite [LHS](@integral_distribution _ _ _ _ _
  (mu 0%N \x tuple_prod (fun i => mu i.+1) n) (@tuple_cons _ T n))//.
by rewrite -(integral12_prod_meas1 Fci).
Qed.

(* Independent coordinates: the integral of a product of nonnegative
   functions of the coordinates is the product of the integrals. *)
Lemma ge0_integral_tuple_prod_prod (mu : nat -> probability T R) n
    (f : nat -> T -> R) :
  (forall i, measurable_fun [set: T] (f i)) -> (forall i t, (0 <= f i t)%R) ->
  \int[tuple_prod mu n]_x (\prod_(i < n) f i (tnth x i))%:E =
  \prod_(i < n) \int[mu i]_t (f i t)%:E.
Proof.
elim: n mu f => [|n IH] mu f mf f0.
  rewrite big_ord0; under eq_integral do rewrite big_ord0.
  by rewrite integral_cst//= probability_setT mul1e.
have mprod m (g : nat -> T -> R) : (forall i, measurable_fun [set: T] (g i)) ->
    measurable_fun [set: m.-tuple T]
      (fun x => (\prod_(i < m) g i (tnth x i))%:E).
  move=> mg; apply/measurable_EFinP; apply: measurable_prod => i _.
  exact: measurableT_comp (mg i) (measurable_tnth i).
have p0 m (g : nat -> T -> R) : (forall i t, (0 <= g i t)%R) ->
    forall x : m.-tuple T, 0 <= (\prod_(i < m) g i (tnth x i))%:E.
  by move=> g0 x; rewrite lee_fin prodr_ge0.
rewrite ge0_integral_tuple_prodS//; [exact: mprod|exact: p0|].
transitivity (\int[mu 0%N]_t ((f 0%N t)%:E *
    \prod_(i < n) \int[mu i.+1]_u (f i.+1 u)%:E)).
  apply: eq_integral => t _.
  transitivity (\int[tuple_prod (fun i => mu i.+1) n]_v
      ((f 0%N t)%:E * (\prod_(i < n) f i.+1 (tnth v i))%:E)).
    apply: eq_integral => v _; rewrite big_ord_recl EFinM.
    by under eq_bigr do rewrite tnthS.
  rewrite ge0_integralZl_EFin//.
  - by move=> x _; exact: (p0 n (fun i => f i.+1) (fun i => f0 i.+1)).
  - exact: (mprod n (fun i => f i.+1) (fun i => mf i.+1)).
  - congr (_ * _).
    exact: (IH (fun i => mu i.+1) (fun i => f i.+1) (fun i => mf i.+1)
      (fun i => f0 i.+1)).
have I0 : 0 <= \prod_(i < n) \int[mu i.+1]_u (f i.+1 u)%:E.
  by apply: prode_ge0 => i _; apply: integral_ge0 => t _; rewrite lee_fin.
have mf0 : measurable_fun [set: T] (fun t => (f 0%N t)%:E).
  by apply/measurable_EFinP; exact: mf.
rewrite ge0_integralZr//; first by move=> t _; rewrite lee_fin.
by rewrite [in RHS]big_ord_recl.
Qed.

End tuple_prod_integral.

Section image_law.
Context d1 d2 (V : measurableType d1) (W : measurableType d2) (R : realType).
Local Open Scope ereal_scope.

(* The integral against a law mu that is the image of nu under g. *)
Lemma ge0_integral_image (nu : probability V R) (mu : probability W R)
    (g : V -> W) (f : W -> \bar R) :
  measurable_fun setT g -> (forall A, measurable A -> mu A = nu (g @^-1` A)) ->
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int[mu]_y f y = \int[nu]_x f (g x).
Proof.
move=> mg mug mf f0.
pose gp : {mfun V >-> W} := HB.pack g (isMeasurableFun.Build _ _ _ _ g mg).
transitivity (\int[distribution nu gp]_y f y).
  by apply: eq_measure_integral => A mA _; exact: mug.
by rewrite ge0_integral_distribution.
Qed.

End image_law.

Section tuple_map.
Context d d' (T : measurableType d) (T' : measurableType d') (R : realType).
Local Open Scope ereal_scope.

(* The coordinatewise map x |-> [tuple g i (x_i) | i < n]. *)
Definition tuple_map (g : nat -> T -> T') {n} (x : n.-tuple T) : n.-tuple T' :=
  [tuple g i (tnth x i) | i < n].

Lemma measurable_tuple_map (g : nat -> T -> T') n :
  (forall i, measurable_fun setT (g i)) -> measurable_fun setT (@tuple_map g n).
Proof.
move=> mg; apply/measurable_fun_tnthP => j /=.
apply: (eq_measurable_fun (fun x : n.-tuple T => g j (tnth x j))).
  by move=> x _; rewrite /= tnth_mktuple.
exact: measurableT_comp (mg j) (measurable_tnth j).
Qed.

Lemma tuple_map_cons (g : nat -> T -> T') n (t : T) (ts : n.-tuple T) :
  tuple_map g (tuple_cons (t, ts)) =
  tuple_cons (g 0%N t, tuple_map (fun i => g i.+1) ts).
Proof.
apply: eq_from_tnth => j; rewrite /tuple_cons /= tnth_mktuple.
case: (unliftP ord0 j) => [k ->|->]; last by rewrite !(tnth_nth (g 0%N t)).
by rewrite !tnthS tnth_mktuple lift0.
Qed.

(* Coordinatewise maps preserve independence: if mu i is the image of nu i
   under g i for every i, then tuple_prod mu n is the image of
   tuple_prod nu n under tuple_map g. *)
Lemma ge0_integral_tuple_map (nu : nat -> probability T R)
    (mu : nat -> probability T' R) (g : nat -> T -> T') n
    (G : n.-tuple T' -> \bar R) :
  (forall i, measurable_fun setT (g i)) ->
  (forall i A, measurable A -> mu i A = nu i (g i @^-1` A)) ->
  measurable_fun setT G -> (forall y, 0 <= G y) ->
  \int[tuple_prod mu n]_y G y = \int[tuple_prod nu n]_x G (tuple_map g x).
Proof.
elim: n nu mu g G => [|n IH] nu mu g G mg mug mG G0.
  have mGg : measurable_fun setT (fun x : 0.-tuple T => G (tuple_map g x)).
    by apply: measurableT_comp mG _; exact: measurable_tuple_map.
  rewrite /= !integral_dirac //.
  by rewrite !diracT (tuple0 (tuple_map g [tuple])).
pose g' := fun i => g i.+1.
have mg' i : measurable_fun setT (g' i) by exact: mg.
have mGm : measurable_fun setT (fun x : n.+1.-tuple T => G (tuple_map g x)).
  by apply: measurableT_comp mG _; exact: measurable_tuple_map.
rewrite ge0_integral_tuple_prodS // [RHS]ge0_integral_tuple_prodS //.
transitivity (\int[mu 0%N]_t \int[tuple_prod (fun i => nu i.+1) n]_ts
    G (tuple_cons (t, tuple_map g' ts))).
  apply: eq_integral => t _.
  apply: (IH (fun i => nu i.+1) (fun i => mu i.+1) g'
    (fun ts => G (tuple_cons (t, ts)))) => //.
  - by move=> i A mA; exact: mug.
  - exact: measurableT_comp mG (measurable_tuple_cons_l t).
under [RHS]eq_integral do under eq_integral do rewrite tuple_map_cons.
have mH : measurable_fun setT
    (fun p : T' * n.-tuple T => G (tuple_cons (p.1, tuple_map g' p.2))).
  apply: measurableT_comp mG _.
  apply: measurableT_comp (@measurable_tuple_cons _ T' n) _.
  apply: measurable_fun_pair => //; apply: measurableT_comp _ measurable_snd.
  exact: measurable_tuple_map.
have mH' : measurable_fun setT
    (fun p : T * n.-tuple T => G (tuple_cons (g 0%N p.1, tuple_map g' p.2))).
  apply: measurableT_comp mG _.
  apply: measurableT_comp (@measurable_tuple_cons _ T' n) _.
  apply: measurable_fun_pair.
    exact: measurableT_comp (mg 0%N) measurable_fst.
  by apply: measurableT_comp _ measurable_snd; exact: measurable_tuple_map.
transitivity (\int[tuple_prod (fun i => nu i.+1) n]_y
    \int[mu 0%N]_x G (tuple_cons (x, tuple_map g' y))).
  exact: (fubini_tonelli (m1 := mu 0%N) (m2 := tuple_prod (fun i => nu i.+1) n)
    _ mH (fun p => G0 _)).
transitivity (\int[tuple_prod (fun i => nu i.+1) n]_y
    \int[nu 0%N]_s G (tuple_cons (g 0%N s, tuple_map g' y))).
  apply: eq_integral => y _.
  apply: (ge0_integral_image (mg 0%N) (mug 0%N)) => //.
  exact: measurableT_comp mG (measurable_tuple_cons_r _).
symmetry.
exact: (fubini_tonelli (m1 := nu 0%N) (m2 := tuple_prod (fun i => nu i.+1) n)
  _ mH' (fun p => G0 _)).
Qed.

Lemma tuple_prod_map (nu : nat -> probability T R)
    (mu : nat -> probability T' R) (g : nat -> T -> T') n
    (A : set (n.-tuple T')) :
  (forall i, measurable_fun setT (g i)) ->
  (forall i B, measurable B -> mu i B = nu i (g i @^-1` B)) ->
  measurable A -> tuple_prod mu n A = tuple_prod nu n (tuple_map g @^-1` A).
Proof.
move=> mg mug mA.
have mgA : measurable (tuple_map g @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: (measurable_tuple_map mg).
transitivity (\int[tuple_prod mu n]_y (\1_A y)%:E).
  by rewrite integral_indic // setIT.
transitivity (\int[tuple_prod nu n]_x (\1_(tuple_map g @^-1` A) x)%:E);
  last by rewrite integral_indic // setIT.
rewrite (ge0_integral_tuple_map mg mug).
- by apply/measurable_EFinP; exact: measurable_indic.
- by move=> y; rewrite lee_fin indicE.
by apply: eq_integral => x _; rewrite !indicE.
Qed.

(* The same for every measurable G with values in \bar R, integrable or
   not. *)
Lemma integral_tuple_map (nu : nat -> probability T R)
    (mu : nat -> probability T' R) (g : nat -> T -> T') n
    (G : n.-tuple T' -> \bar R) :
  (forall i, measurable_fun setT (g i)) ->
  (forall i A, measurable A -> mu i A = nu i (g i @^-1` A)) ->
  measurable_fun setT G ->
  \int[tuple_prod mu n]_y G y = \int[tuple_prod nu n]_x G (tuple_map g x).
Proof.
move=> mg mug mG; rewrite integralE [RHS]integralE.
rewrite (ge0_integral_tuple_map mg mug (measurable_funepos mG)) //.
rewrite (ge0_integral_tuple_map mg mug (measurable_funeneg mG)) //.
by congr (_ - _)%E; apply: eq_integral => x _; rewrite ?funeposE ?funenegE.
Qed.

Lemma integrable_tuple_map (nu : nat -> probability T R)
    (mu : nat -> probability T' R) (g : nat -> T -> T') n
    (G : n.-tuple T' -> \bar R) :
  (forall i, measurable_fun setT (g i)) ->
  (forall i A, measurable A -> mu i A = nu i (g i @^-1` A)) ->
  measurable_fun setT G ->
  (tuple_prod mu n).-integrable setT G <->
  (tuple_prod nu n).-integrable setT (fun x => G (tuple_map g x)).
Proof.
move=> mg mug mG.
have mGg : measurable_fun setT (fun x => G (tuple_map g x)).
  by apply: measurableT_comp mG _; exact: measurable_tuple_map.
have E : \int[tuple_prod mu n]_y `|G y| =
    \int[tuple_prod nu n]_x `|G (tuple_map g x)|.
  by apply: ge0_integral_tuple_map => //; exact: measurableT_comp.
by split => /integrableP[_ Gi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

Lemma Rintegral_tuple_map (nu : nat -> probability T R)
    (mu : nat -> probability T' R) (g : nat -> T -> T') n
    (G : n.-tuple T' -> R) :
  (forall i, measurable_fun setT (g i)) ->
  (forall i A, measurable A -> mu i A = nu i (g i @^-1` A)) ->
  measurable_fun setT G ->
  (\int[tuple_prod mu n]_y G y = \int[tuple_prod nu n]_x G (tuple_map g x))%R.
Proof.
move=> mg mug mG; rewrite /Rintegral (integral_tuple_map mg mug) //.
exact/measurable_EFinP.
Qed.

End tuple_map.

Section tuple_cat.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

Lemma measurable_tuple_cat a b :
  measurable_fun setT
    (fun p : a.-tuple T * b.-tuple T => [tuple of p.1 ++ p.2]).
Proof.
apply/measurable_fun_tnthP => k /=; case: (splitP k) => [i ki|j kj].
  have -> : k = lshift b i by exact: val_inj.
  apply: (eq_measurable_fun (fun p : a.-tuple T * b.-tuple T => tnth p.1 i)).
    by move=> p _; rewrite /= tnth_lshift.
  exact: measurableT_comp (measurable_tnth i) measurable_fst.
have -> : k = rshift a j by exact: val_inj.
apply: (eq_measurable_fun (fun p : a.-tuple T * b.-tuple T => tnth p.2 j)).
  by move=> p _; rewrite /= tnth_rshift.
exact: measurableT_comp (measurable_tnth j) measurable_snd.
Qed.

(* Fubini for blocks: the first a coordinates and the last b coordinates
   of tuple_prod mu (a + b) are independent, with the product laws of their
   coordinates. *)
Lemma ge0_integral_tuple_prod_cat (mu : nat -> probability T R) a b
    (F : (a + b).-tuple T -> \bar R) :
  measurable_fun setT F -> (forall z, 0 <= F z) ->
  \int[tuple_prod mu (a + b)]_z F z =
  \int[tuple_prod mu a]_x
    \int[tuple_prod (fun i => mu (a + i)%N) b]_y F [tuple of x ++ y].
Proof.
elim: a mu F => [|a IH] mu F mF F0.
  have mFc : measurable_fun setT
      (fun p : 0.-tuple T * b.-tuple T => F [tuple of p.1 ++ p.2]).
    by apply: measurableT_comp mF _; exact: measurable_tuple_cat.
  rewrite /= integral_dirac.
  - exact: measurableT.
  - exact: (measurable_fun_fubini_tonelli_F
      (m2 := tuple_prod (fun i : nat => mu (0 + i)%N) b) _ mFc (fun p => F0 _)).
  rewrite diracT mul1e; apply: eq_integral => y _.
  by congr F; exact: val_inj.
rewrite (@ge0_integral_tuple_prodS _ _ _ mu (a + b) F) //.
have mFc : measurable_fun setT
    (fun p : a.+1.-tuple T * b.-tuple T => F [tuple of p.1 ++ p.2]).
  by apply: measurableT_comp mF _; exact: measurable_tuple_cat.
rewrite [RHS]ge0_integral_tuple_prodS.
- exact: (measurable_fun_fubini_tonelli_F
    (m2 := tuple_prod (fun i : nat => mu (a.+1 + i)%N) b) _ mFc
    (fun p => F0 _)).
- by move=> x; apply: integral_ge0 => y _; exact: F0.
apply: eq_integral => t _.
rewrite (IH (fun i => mu i.+1) (fun z => F (tuple_cons (t, z)))).
- exact: measurableT_comp mF (measurable_tuple_cons_l t).
- by move=> z; exact: F0.
apply: eq_integral => x _; apply: eq_integral => y _.
by congr F; exact: val_inj.
Qed.

Lemma measurable_tuple_rows n m :
  measurable_fun [set: (n * m).-tuple T] (tuple_rows n m).
Proof.
apply/measurable_fun_tnthP => i /=; apply/measurable_fun_tnthP => j /=.
apply: (eq_measurable_fun (fun x : (n * m).-tuple T => tnth x (row_index i j))).
  by move=> x _; rewrite /= !tnth_mktuple.
exact: measurable_tnth.
Qed.

Lemma tuple_rows_cat n m (x : m.-tuple T) (y : (n * m).-tuple T) :
  tuple_rows n.+1 m [tuple of x ++ y] = tuple_cons (x, tuple_rows n m y).
Proof.
apply: eq_from_tnth => i; rewrite /tuple_cons /= tnth_mktuple.
case: (unliftP ord0 i) => [k ->|->].
  rewrite tnthS tnth_mktuple; apply: eq_from_tnth => j; rewrite !tnth_mktuple.
  have -> : row_index (lift ord0 k) j = rshift m (row_index k j).
    by apply: val_inj; rewrite /= /bump leq0n add1n mulSn addnA.
  by rewrite tnth_rshift.
rewrite (tnth_nth x) /=; apply: eq_from_tnth => j; rewrite tnth_mktuple.
have -> : row_index ord0 j = lshift (n * m) j by exact: val_inj.
by rewrite tnth_lshift.
Qed.

(* The rows of tuple_prod mu (n * m) are independent: tuple_rows n m maps it
   to the product over i < n of the laws of the rows. *)
Lemma ge0_integral_tuple_rows (mu : nat -> probability T R) n m
    (G : n.-tuple (m.-tuple T) -> \bar R) :
  measurable_fun setT G -> (forall y, 0 <= G y) ->
  \int[tuple_prod mu (n * m)]_x G (tuple_rows n m x) =
  \int[tuple_prod (fun i => tuple_prod (fun j => mu (i * m + j)%N) m) n]_y G y.
Proof.
elim: n mu G => [|n IH] mu G mG G0.
  rewrite /= !integral_dirac //.
  - by apply: measurableT_comp mG _; exact: measurable_tuple_rows.
  - by rewrite !diracT (tuple0 (tuple_rows 0 m [tuple])).
have mGr : measurable_fun setT
    (fun z : (m + n * m).-tuple T => G (tuple_rows n.+1 m z)).
  by apply: measurableT_comp mG _; exact: (@measurable_tuple_rows n.+1 m).
rewrite (@ge0_integral_tuple_prod_cat mu m (n * m) _ mGr (fun z => G0 _)).
under eq_integral do under eq_integral do rewrite tuple_rows_cat.
rewrite [RHS]ge0_integral_tuple_prodS //.
have -> : (fun i => tuple_prod (fun j => mu (i.+1 * m + j)%N) m) =
    (fun i => tuple_prod (fun j => mu (m + (i * m + j))%N) m).
  apply/funext => i.
  have -> : (fun j => mu (i.+1 * m + j)%N) = (fun j => mu (m + (i * m + j))%N).
    by apply/funext => j; rewrite mulSn addnA.
  by [].
apply: eq_integral => x _.
apply: (IH (fun k => mu (m + k)%N) (fun Y => G (tuple_cons (x, Y)))).
- exact: measurableT_comp mG (measurable_tuple_cons_l x).
- by move=> Y; exact: G0.
Qed.

Lemma integral_tuple_rows (mu : nat -> probability T R) n m
    (G : n.-tuple (m.-tuple T) -> \bar R) :
  measurable_fun setT G ->
  \int[tuple_prod mu (n * m)]_x G (tuple_rows n m x) =
  \int[tuple_prod (fun i => tuple_prod (fun j => mu (i * m + j)%N) m) n]_y G y.
Proof.
move=> mG; rewrite integralE [RHS]integralE.
rewrite -(ge0_integral_tuple_rows mu (measurable_funepos mG)) //.
rewrite -(ge0_integral_tuple_rows mu (measurable_funeneg mG)) //.
by congr (_ - _)%E; apply: eq_integral => x _; rewrite ?funeposE ?funenegE.
Qed.

Lemma tuple_prod_rows (mu : nat -> probability T R) n m
    (A : set (n.-tuple (m.-tuple T))) : measurable A ->
  tuple_prod (fun i => tuple_prod (fun j => mu (i * m + j)%N) m) n A =
  tuple_prod mu (n * m) (tuple_rows n m @^-1` A).
Proof.
move=> mA; have mrA : measurable (tuple_rows n m @^-1` A).
  by rewrite -[X in measurable X]setTI; exact: measurable_tuple_rows.
transitivity (\int[tuple_prod (fun i => tuple_prod
    (fun j => mu (i * m + j)%N) m) n]_y (\1_A y)%:E).
  by rewrite integral_indic // setIT.
transitivity (\int[tuple_prod mu (n * m)]_x
    (\1_(tuple_rows n m @^-1` A) x)%:E);
  last by rewrite integral_indic // setIT.
rewrite -ge0_integral_tuple_rows.
- by apply/measurable_EFinP; exact: measurable_indic.
- by move=> y; rewrite lee_fin indicE.
by apply: eq_integral => x _; rewrite !indicE.
Qed.

(* tuple_prod mu n depends only on mu 0, ..., mu (n - 1). *)
Lemma eq_tuple_prod (mu mu' : nat -> probability T R) n :
  (forall i, (i < n)%N -> mu i = mu' i) -> tuple_prod mu n = tuple_prod mu' n.
Proof.
elim: n mu mu' => [//|n IH] mu mu' e /=.
have -> : mu 0%N = mu' 0%N by exact: e.
by rewrite (IH (fun i => mu i.+1) (fun i => mu' i.+1)) // => i i_lt; exact: e.
Qed.

End tuple_cat.
