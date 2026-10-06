From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum.
From mathcomp Require Import matrix arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import reals ereal interval interval_inference topology.
From mathcomp Require Import normedtype sequences exp numfun measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral probability.
From GaussianAnalysis Require Import measurable_matrix normal_integral.

(**md**************************************************************************)
(* # The standard Gaussian measure on row vectors                             *)
(*                                                                            *)
(* gauss n is the law of a row vector of n independent standard normal        *)
(* coordinates: the n-fold product of normal_prob 0 1 on 'rV[R]_n, with the   *)
(* sigma-algebra of measurable_matrix.v. It is defined by recursion on n,     *)
(* the first coordinate being drawn first (gaussS). The measure of a box is   *)
(* the product of the measures of its sides (gauss_box), and this property    *)
(* characterizes gauss n among all measures (gauss_unique). Measurable        *)
(* functions of polynomial growth are integrable (integrable_gauss_poly).     *)
(*                                                                            *)
(* The vectors are rows because the linear algebra of MathComp writes them    *)
(* so, with linear maps acting on the right: if x has law gauss n and A is an *)
(* n x m matrix, then x *m A is a centered Gaussian vector with covariance    *)
(* A^T *m A.                                                                  *)
(*                                                                            *)
(* ```                                                                        *)
(*   rV_cons p == the row vector of size n.+1 with first coordinate p.1, and  *)
(*                then the coordinates of p.2 : 'rV_n                         *)
(*     gauss n == the standard Gaussian measure on 'rV[R]_n                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section integral_image.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (mu : {measure set T1 -> \bar R}) (nu : {measure set T2 -> \bar R}).
Variable g : T1 -> T2.
Hypothesis mg : measurable_fun [set: T1] g.
Hypothesis gnu : forall A, measurable A -> mu (g @^-1` A) = nu A.

(* If nu is the image of mu under g, integrating f against nu is integrating
   f \o g against mu. *)
Lemma integrable_image (f : T2 -> \bar R) :
  nu.-integrable [set: T2] f -> mu.-integrable [set: T1] (f \o g).
Proof.
move=> fi; have mf := measurable_int _ fi.
have E : (\int[pushforward mu g]_y `|f y| = \int[nu]_y `|f y|)%E.
  by apply: eq_measure_integral => A mA _; exact: gnu.
apply/integrableP; split; first exact: measurableT_comp.
have -> : (\int[mu]_x `|(f \o g) x| = \int[pushforward mu g]_y `|f y|)%E.
  by rewrite ge0_integral_pushforward //; exact: measurableT_comp.
by rewrite E; case/integrableP: fi.
Qed.

Lemma integral_image (f : T2 -> \bar R) :
  nu.-integrable [set: T2] f -> (\int[mu]_x f (g x) = \int[nu]_y f y)%E.
Proof.
move=> fi; have mf := measurable_int _ fi; have fgi := integrable_image fi.
transitivity (\int[pushforward mu g]_y f y)%E.
  by rewrite integral_pushforward.
by apply: eq_measure_integral => A mA _; exact: gnu.
Qed.

End integral_image.

Section rV_cons.
Context {R : realType} (n : nat).

Definition rV_cons (p : measurableTypeR R * 'rV[R]_n) : 'rV[R]_n.+1 :=
  row_mx (const_mx (p.1 : R) : 'rV_1) p.2.

Lemma rV_cons0 p : rV_cons p 0 ord0 = p.1.
Proof.
have -> : ord0 = lshift n (ord0 : 'I_1) by exact: val_inj.
by rewrite /rV_cons /row_mx mxE; case: splitP => // j _; rewrite mxE.
Qed.

Lemma rV_consS p (j : 'I_n) : rV_cons p 0 (lift ord0 j) = p.2 0 j.
Proof.
have -> : lift ord0 j = rshift 1 j by exact: val_inj.
by rewrite /rV_cons /row_mx mxE (unsplitK (inr _ j)).
Qed.

Lemma measurable_rV_cons :
  measurable_fun [set: measurableTypeR R * 'rV[R]_n] rV_cons.
Proof.
apply: (@measurable_row_mx _ _ R _ 1 1 n); last exact: measurable_snd.
by apply: measurableT_comp; [exact: measurable_const_mx|exact: measurable_fst].
Qed.

HB.instance Definition _ :=
  isMeasurableFun.Build _ _ _ _ rV_cons measurable_rV_cons.

End rV_cons.

Section gauss.
Context {R : realType}.
Local Open Scope ereal_scope.

Fixpoint gauss n : probability 'rV[R]_n R :=
  if n is n'.+1 then
    distribution (normal_prob 0 1 \x gauss n') (@rV_cons R n')
  else \d_(0%R : 'rV[R]_0).

End gauss.

Section gauss_box.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma gaussS n X : gauss n.+1 X = (N \x gauss n)%E (@rV_cons R n @^-1` X).
Proof. by []. Qed.

Lemma gauss_box n (A : 'I_n -> set R) : (forall i, measurable (A i)) ->
  gauss n [set x : 'rV[R]_n | forall i, A i (x 0 i)] =
    (\prod_(i < n) N (A i))%E.
Proof.
elim: n A => [|n IH] A mA.
  rewrite big_ord0 (_ : [set _ | _] = setT) ?probability_setT//.
  by apply/seteqP; split => // x _ [].
rewrite gaussS.
have -> : @rV_cons R n @^-1` [set x | forall i, A i (x 0 i)] =
    A ord0 `*` [set v : 'rV_n | forall i, A (lift ord0 i) (v 0 i)].
  apply/seteqP; split => [[t v] /= H|[t v] [/= H0 H1] i].
    split; first by have := H ord0; rewrite rV_cons0.
    by move=> i; have := H (lift ord0 i); rewrite rV_consS.
  case: (unliftP ord0 i) => [j ->|->]; last by rewrite rV_cons0.
  by rewrite rV_consS; exact: H1.
rewrite product_measure1E.
- exact: mA.
- by apply: (@measurable_rowbox _ R n (fun i => A (lift ord0 i))) => i;
    exact: mA.
rewrite big_ord_recl; congr (_ * _)%E.
exact: (IH (fun i => A (lift ord0 i)) (fun i => mA _)).
Qed.

(* A measure that gives every box the product of the normal measures of its
   sides is gauss n. The hypothesis at A = fun=> setT makes it a probability. *)
Lemma gauss_unique n (P : {measure set 'rV[R]_n -> \bar R}) :
  (forall A : 'I_n -> set R, (forall i, measurable (A i)) ->
     P [set x : 'rV[R]_n | forall i, A i (x 0 i)] =
       (\prod_(i < n) N (A i))%E) ->
  forall X, measurable X -> P X = gauss n X.
Proof.
move=> PA; apply: measure_rowbox_unique.
  have -> : [set: 'rV[R]_n] = [set x : 'rV[R]_n | forall i, [set: R] (x 0 i)].
    by apply/seteqP; split=> [x _ i|x _]; exact: I.
  rewrite (PA (fun=> setT) (fun=> measurableT)) big1 ?ltry// => i _.
  exact: probability_setT.
move=> A mA; transitivity (\prod_(i < n) N (A i))%E; first exact: PA.
by symmetry; exact: gauss_box.
Qed.

End gauss_box.

Section gauss_integral.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Open Scope ereal_scope.

Lemma ge0_integral_gauss_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  measurable_fun [set: 'rV[R]_n.+1] f -> (forall x, 0 <= f x) ->
  \int[gauss n.+1]_x f x = \int[N]_t \int[gauss n]_v f (rV_cons (t, v)).
Proof.
move=> mf f0.
rewrite [LHS](@ge0_integral_distribution _ _ _ _ _ (N \x gauss n)
  (@rV_cons R n))//.
rewrite fubini_tonelli1//; first exact: measurableT_comp.
by move=> ?; exact: f0.
Qed.

Lemma integrable_gauss_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  measurable_fun [set: 'rV[R]_n.+1] f ->
  (gauss n.+1).-integrable [set: 'rV[R]_n.+1] f <->
  (N \x gauss n).-integrable [set: measurableTypeR R * 'rV[R]_n]
    (f \o @rV_cons R n).
Proof.
move=> mf.
have mfc : measurable_fun [set: measurableTypeR R * 'rV[R]_n]
    (f \o @rV_cons R n).
  exact: measurableT_comp.
have E : \int[gauss n.+1]_x `|f x| =
    \int[N \x gauss n]_p `|(f \o @rV_cons R n) p|.
  rewrite (@ge0_integral_distribution _ _ _ _ _ (N \x gauss n)
    (@rV_cons R n))//.
  exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

Lemma integral_gauss_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  (gauss n.+1).-integrable [set: 'rV[R]_n.+1] f ->
  \int[gauss n.+1]_x f x = \int[N]_t \int[gauss n]_v f (rV_cons (t, v)).
Proof.
move=> fi; have mf := measurable_int _ fi.
have fci := (integrable_gauss_cons mf).1 fi.
rewrite [LHS](@integral_distribution _ _ _ _ _ (N \x gauss n) (@rV_cons R n))//.
by rewrite -(integral12_prod_meas1 fci).
Qed.

End gauss_integral.

Section gauss_invariance.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma gauss_col_perm n (s : 'S_n) (X : set 'rV[R]_n) : measurable X ->
  gauss n (col_perm s @^-1` X) = gauss n X.
Proof.
move=> mX; pose g : {mfun 'rV[R]_n >-> 'rV[R]_n} := HB.pack (col_perm s)
  (isMeasurableFun.Build _ _ _ _ (col_perm s) (measurable_col_perm s)).
apply: (@gauss_unique R n (distribution (gauss n) g) _ X mX) => A mA.
change (gauss n (g @^-1` [set x : 'rV_n | forall i, A i (x 0 i)]) =
  (\prod_(i < n) N (A i))%E).
have -> : g @^-1` [set x : 'rV_n | forall i, A i (x 0 i)] =
    [set x : 'rV_n | forall j, A ((s^-1)%g j) (x 0 j)].
  apply/seteqP; split => x /= H j.
    by have := H ((s^-1)%g j); rewrite mxE permKV.
  by rewrite mxE; have := H (s j); rewrite permK.
transitivity (\prod_(j < n) N (A ((s^-1)%g j)))%E.
  by apply: gauss_box => j; exact: mA.
by rewrite [RHS](reindex_inj (@perm_inj _ (s^-1)%g)).
Qed.

Lemma integral_gauss_col_perm n (s : 'S_n) (f : 'rV[R]_n -> \bar R) :
  (gauss n).-integrable [set: 'rV[R]_n] f ->
  (\int[gauss n]_x f (col_perm s x) = \int[gauss n]_x f x)%E.
Proof.
by apply: integral_image; [exact: measurable_col_perm|exact: gauss_col_perm].
Qed.

Lemma gauss_row_mx n m (X : set 'rV[R]_(n + m)) : measurable X ->
  gauss (n + m) X =
  (gauss n \x gauss m)%E
    ((fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1` X).
Proof.
move=> mX.
have mg : measurable_fun [set: 'rV[R]_n * 'rV[R]_m]
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
  exact: measurable_row_mx measurable_fst measurable_snd.
pose g : {mfun ('rV[R]_n * 'rV[R]_m)%type >-> 'rV[R]_(n + m)} :=
  HB.pack (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2)
    (isMeasurableFun.Build _ _ _ _ _ mg).
symmetry.
apply: (@gauss_unique R (n + m) (distribution (gauss n \x gauss m)%E g) _ X mX).
move=> A mA.
change ((gauss n \x gauss m)%E
  (g @^-1` [set x : 'rV_(n + m) | forall i, A i (x 0 i)]) =
  (\prod_(i < n + m) N (A i))%E).
have -> : g @^-1` [set x : 'rV_(n + m) | forall i, A i (x 0 i)] =
    [set x : 'rV_n | forall i, A (lshift m i) (x 0 i)] `*`
    [set y : 'rV_m | forall j, A (rshift n j) (y 0 j)].
  apply/seteqP; split => [[x y] /= H|[x y] [/= H1 H2] k].
    split => i; [have := H (lshift m i)|have := H (rshift n i)].
      by rewrite row_mxEl.
    by rewrite row_mxEr.
  by rewrite -[k]splitK; case: (fintype.split k) => i /=;
    rewrite ?row_mxEl ?row_mxEr.
rewrite product_measure1E.
- by apply: (@measurable_rowbox _ R n (fun i => A (lshift m i))) => i;
    exact: mA.
- by apply: (@measurable_rowbox _ R m (fun j => A (rshift n j))) => j;
    exact: mA.
rewrite big_split_ord; congr (_ * _)%E.
- by apply: gauss_box => i; exact: mA.
- by apply: gauss_box => j; exact: mA.
Qed.

Lemma gauss_lsubmx n m (X : set 'rV[R]_n) : measurable X ->
  gauss (n + m) (@lsubmx R 1 n m @^-1` X) = gauss n X.
Proof.
move=> mX.
have mlX : measurable (@lsubmx R 1 n m @^-1` X).
  by rewrite -[_ @^-1` _]setTI; exact: measurable_lsubmx.
rewrite gauss_row_mx//.
have -> : (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1`
    (lsubmx @^-1` X) = X `*` [set: 'rV[R]_m].
  by apply/seteqP; split => -[x y] /=; rewrite row_mxKl// => -[].
rewrite product_measure1E// -[RHS]mule1 -(probability_setT (gauss m)).
by congr (_ * _)%E.
Qed.

Lemma gauss_rsubmx n m (Y : set 'rV[R]_m) : measurable Y ->
  gauss (n + m) (@rsubmx R 1 n m @^-1` Y) = gauss m Y.
Proof.
move=> mY.
have mrY : measurable (@rsubmx R 1 n m @^-1` Y).
  by rewrite -[_ @^-1` _]setTI; exact: measurable_rsubmx.
rewrite gauss_row_mx//.
have -> : (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1`
    (rsubmx @^-1` Y) = [set: 'rV[R]_n] `*` Y.
  by apply/seteqP; split => -[x y] /=; rewrite row_mxKr// => -[].
rewrite product_measure1E// -[RHS]mul1e -(probability_setT (gauss n)).
by congr (_ * _)%E.
Qed.

Lemma integral_gauss_lsubmx n m (f : 'rV[R]_n -> \bar R) :
  (gauss n).-integrable [set: 'rV[R]_n] f ->
  (\int[gauss (n + m)]_x f (lsubmx x) = \int[gauss n]_x f x)%E.
Proof.
by apply: integral_image; [exact: measurable_lsubmx|exact: gauss_lsubmx].
Qed.

Lemma integral_gauss_rsubmx n m (f : 'rV[R]_m -> \bar R) :
  (gauss m).-integrable [set: 'rV[R]_m] f ->
  (\int[gauss (n + m)]_x f (rsubmx x) = \int[gauss m]_x f x)%E.
Proof.
by apply: integral_image; [exact: measurable_rsubmx|exact: gauss_rsubmx].
Qed.

Lemma gauss_coord n (i : 'I_n) (A : set R) : measurable A ->
  gauss n [set x : 'rV[R]_n | A (x 0 i)] = N A.
Proof.
move=> mA.
have -> : [set x : 'rV[R]_n | A (x 0 i)] =
    [set x : 'rV[R]_n | forall j, (if j == i then A else setT) (x 0 j)].
  apply/seteqP; split => x /= H; last by have := H i; rewrite eqxx.
  by move=> j; case: eqP => // ->.
transitivity (\prod_(j < n) N (if j == i then A else setT))%E.
  by apply: gauss_box => j; case: (j == i).
rewrite (bigD1 i)//= eqxx big1 ?mule1// => j /negbTE ->.
exact: probability_setT.
Qed.

Lemma ge0_integral_gauss_prod n (f : 'I_n -> R -> R) :
  (forall i, measurable_fun [set: R] (f i)) -> (forall i t, 0 <= f i t) ->
  (\int[gauss n]_x (\prod_(i < n) f i (x 0 i))%:E =
   \prod_(i < n) \int[N]_t (f i t)%:E)%E.
Proof.
have mprod m (g : 'I_m -> R -> R) : (forall i, measurable_fun [set: R] (g i)) ->
    measurable_fun [set: 'rV[R]_m] (fun x => (\prod_(i < m) g i (x 0 i))%:E).
  move=> mg; apply/measurable_EFinP; apply: measurable_prod => i _.
  exact: measurableT_comp (mg i) (measurable_mxentry 0 i).
elim: n f => [|n IH] f mf f0.
  rewrite big_ord0; under eq_integral do rewrite big_ord0.
  by rewrite integral_cst//= probability_setT mul1e.
have p0 m (g : 'I_m -> R -> R) : (forall i t, 0 <= g i t) ->
    forall x : 'rV[R]_m, (0 <= (\prod_(i < m) g i (x 0 i))%:E)%E.
  by move=> g0 x; rewrite lee_fin prodr_ge0.
have mf' i : measurable_fun [set: R] (f (lift ord0 i)) by [].
have f0' i t : 0 <= f (lift ord0 i) t by [].
have m1 := mprod _ _ mf; have q1 := p0 _ _ f0.
have m2 := mprod _ _ mf'; have q2 := p0 _ _ f0'.
rewrite ge0_integral_gauss_cons//.
transitivity (\int[N]_t ((f ord0 t)%:E *
    \prod_(i < n) \int[N]_u (f (lift ord0 i) u)%:E))%E.
  apply: eq_integral => t _.
  transitivity (\int[gauss n]_v
      ((f ord0 t)%:E * (\prod_(i < n) f (lift ord0 i) (v 0 i))%:E))%E.
    apply: eq_integral => v _; rewrite big_ord_recl rV_cons0 EFinM.
    by under eq_bigr do rewrite rV_consS.
  rewrite ge0_integralZl_EFin//.
  by rewrite (IH (fun i => f (lift ord0 i))).
have I0 : (0 <= \prod_(i < n) \int[N]_u (f (lift ord0 i) u)%:E)%E.
  by apply: prode_ge0 => i _; apply: integral_ge0 => t _; rewrite lee_fin.
have mf0 : measurable_fun [set: R] (fun t => (f ord0 t)%:E).
  by apply/measurable_EFinP; exact: mf.
have q0 t : [set: R] t -> (0 <= (f ord0 t)%:E)%E by rewrite lee_fin.
by rewrite ge0_integralZr// [in RHS]big_ord_recl.
Qed.

End gauss_invariance.

Section gauss_coord_integral.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Let measurable_coord n (i : 'I_n) :
  measurable_fun [set: 'rV[R]_n]
    (fun x : 'rV[R]_n => (x 0 i : measurableTypeR R)).
Proof. by move=> _ Y mY; exact: (measurable_mxentry 0 i measurableT mY). Qed.

Let coord n (i : 'I_n) : {mfun 'rV[R]_n >-> measurableTypeR R} :=
  HB.pack (fun x : 'rV[R]_n => (x 0 i : measurableTypeR R))
    (isMeasurableFun.Build _ _ _ _ _ (measurable_coord i)).

Local Open Scope ereal_scope.

Let distribution_coord n i A : measurable A ->
  distribution (gauss n) (coord i) A = N A.
Proof. exact: gauss_coord. Qed.

Lemma ge0_integral_gauss_coord n (i : 'I_n) (f : R -> \bar R) :
  measurable_fun [set: R] f -> (forall t, 0 <= f t) ->
  \int[gauss n]_x f (x 0%R i) = \int[N]_t f t.
Proof.
move=> mf f0.
rewrite -(@ge0_integral_distribution _ _ _ _ _ (gauss n) (coord i) f)//.
by apply: eq_measure_integral => A mA _; exact: distribution_coord.
Qed.

Lemma integrable_gauss_coord n (i : 'I_n) (f : R -> \bar R) :
  measurable_fun [set: R] f ->
  (gauss n).-integrable [set: 'rV[R]_n] (fun x => f (x 0%R i)) <->
  N.-integrable [set: R] f.
Proof.
move=> mf.
have mfi : measurable_fun [set: 'rV[R]_n] (fun x => f (x 0%R i)).
  by apply: measurableT_comp => //; exact: measurable_mxentry.
have E : \int[gauss n]_x `|f (x 0%R i)| = \int[N]_t `|f t|.
  by apply: ge0_integral_gauss_coord => //; exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //;
  [rewrite -E|rewrite E].
Qed.

Lemma integral_gauss_coord n (i : 'I_n) (f : R -> \bar R) :
  N.-integrable [set: R] f ->
  \int[gauss n]_x f (x 0%R i) = \int[N]_t f t.
Proof.
move=> fi; have mf := measurable_int _ fi.
rewrite -(@integral_distribution _ _ _ _ _ (gauss n) (coord i) f)//.
  exact/(integrable_gauss_coord i mf).
by apply: eq_measure_integral => A mA _; exact: distribution_coord.
Qed.

End gauss_coord_integral.

(* Polynomial bounds C * (1 + `|x| ^+ k), with `|x| the largest absolute
   value of a coordinate. *)
Section poly_bound.
Context {R : realType}.

Lemma exprn1D_le (a : R) k :
  0 <= a -> (1 + a) ^+ k <= 2 ^+ k * (1 + a ^+ k).
Proof.
move=> a0; have p2 : 0 <= (2 : R) ^+ k by rewrite exprn_ge0.
case: (leP a 1) => a1.
  apply: (le_trans (y := 2 ^+ k)).
    by rewrite lerXn2r ?nnegrE ?addr_ge0 //; lra.
  by rewrite ler_peMr // lerDl exprn_ge0.
apply: (le_trans (y := (2 * a) ^+ k)).
  by rewrite lerXn2r ?nnegrE ?addr_ge0 ?mulr_ge0 //; lra.
by rewrite exprMn ler_wpM2l // lerDr.
Qed.

Lemma exprn1S_le (a : R) k : 0 <= a -> 1 + a ^+ k <= 2 * (1 + a ^+ k.+1).
Proof.
move=> a0; have e0 := exprn_ge0 k.+1 a0.
have [h|h] : 1 + a ^+ k <= 2 \/ 1 + a ^+ k <= 1 + a ^+ k.+1.
- case: (lerP a 1) => a1; [left|right].
    by rewrite -[2]/(1 + 1) lerD2l exprn_ile1.
  by rewrite lerD2l ler_eXn2l.
- by apply: (le_trans h); rewrite -[X in X <= _]mulr1 ler_pM2l // lerDl.
- by apply: (le_trans h); rewrite ler_peMl ?addr_ge0 // ler1n.
Qed.

(* The constant of a polynomial bound is nonnegative. *)
Lemma poly_bound_ge0 (V : normedZmodType R) (G : V -> R) (C : R) (k : nat) :
  (forall x, `|G x| <= C * (1 + `|x| ^+ k)) -> 0 <= C.
Proof.
move=> GC; have := GC 0; rewrite normr0 expr0n => h.
by have := normr_ge0 (G 0); case: (k == 0%N) h => /= h; nra.
Qed.

(* Multiplying by a coordinate raises the degree of a polynomial bound by
   one. *)
Lemma entry_mul_bound m (i : 'I_m) (G : 'rV[R]_m -> R) (C : R) (k : nat) :
  (forall x, `|G x| <= C * (1 + `|x| ^+ k)) ->
  forall x : 'rV[R]_m, `|x 0 i * G x| <= (2 * C) * (1 + `|x| ^+ k.+1).
Proof.
move=> GC x; have C0 := poly_bound_ge0 GC.
rewrite normrM exprS; have hb := GC x; have a0 := normr_ge0 x.
have ae := mx_norm_entry_le x 0 i; have e0 := normr_ge0 (x 0 i).
have p0 := exprn_ge0 k a0; have b0 := normr_ge0 (G x).
have h1 : `|x 0 i| * `|G x| <= C * (`|x| + `|x| * `|x| ^+ k).
  by have := ler_wpM2r b0 ae; have := ler_wpM2l a0 hb; nra.
have h2 : `|x| <= 1 + `|x| * `|x| ^+ k.
  case: (leP `|x| 1) => x1; first by nra.
  have : 1 <= `|x| ^+ k by rewrite exprn_ege1// ltW.
  nra.
nra.
Qed.

End poly_bound.

Section gauss_integrable_poly.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma integrable_gauss_poly n (f : 'rV[R]_n -> R) (C : R) k :
  measurable_fun [set: 'rV[R]_n] f ->
  (forall x, `|f x| <= C * (1 + `|x| ^+ k)) ->
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o f).
Proof.
move=> mf fC; have C0 := poly_bound_ge0 fC.
have hi j : (gauss n).-integrable [set: 'rV[R]_n] (fun x => (`|x 0 j| ^+ k)%:E).
  apply/(integrable_gauss_coord j (f := fun t => (`|t| ^+ k)%:E)).
    by apply/measurable_EFinP; apply: measurable_funX; exact: normr_measurable.
  exact: integrable_normal_exprn.
have gi : (gauss n).-integrable [set: 'rV[R]_n]
    (fun x => (C * (2 + \sum_(j < n) `|x 0 j| ^+ k))%:E).
  under eq_fun do rewrite EFinM.
  apply: integrableZl => //; under eq_fun do rewrite EFinD.
  apply: integrableD => //; first exact: finite_measure_integrable_cst.
  under eq_fun do rewrite -sumEFin.
  by apply: integrable_sum => [|j _]; [exact: measurableT|exact: hi].
refine (le_integrable measurableT _ _ gi); first exact/measurable_EFinP.
move=> x _; rewrite /comp !abse_EFin lee_fin (le_trans (fC x))//.
have S0 : 0 <= \sum_(j < n) `|x 0 j| ^+ k.
  by apply: sumr_ge0 => j _; exact: exprn_ge0.
have h : `|x| ^+ k <= 1 + \sum_(j < n) `|x 0 j| ^+ k.
  have := mx_norm_exprn_le x k.
  by rewrite -(pair_bigA _ (fun i j => `|x i j| ^+ k)) big_ord1.
have p0 : 0 <= C * (2 + \sum_(j < n) `|x 0 j| ^+ k).
  by apply: mulr_ge0 => //; lra.
by rewrite (ger0_norm p0); apply: ler_wpM2l => //; lra.
Qed.

End gauss_integrable_poly.
