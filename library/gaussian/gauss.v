From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality reals ereal.
From mathcomp Require Import interval interval_inference topology normedtype.
From mathcomp Require Import sequences exp numfun measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability.
From GaussianAnalysis Require Import measurable_matrix normal_integral.

(**md**************************************************************************)
(* # The standard Gaussian measure on row vectors                             *)
(*                                                                            *)
(* gauss n is the law of a row vector of n independent standard normal        *)
(* coordinates: the n-fold product of normal_prob 0 1 on 'rV[R]_n, with the   *)
(* sigma-algebra of measurable_matrix.v. It is defined by recursion on n,     *)
(* the first coordinate being drawn first (gauss_cons). The measure of a box  *)
(* is the product of the measures of its sides (gauss_box), and this          *)
(* property characterizes gauss n (gaussE).                                   *)
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
  gauss n [set x : 'rV[R]_n | forall i, A i (x 0 i)] = (\prod_(i < n) N (A i))%E.
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
- by apply: (@measurable_rowbox _ R n (fun i => A (lift ord0 i))) => i; exact: mA.
rewrite big_ord_recl; congr (_ * _)%E.
exact: (IH (fun i => A (lift ord0 i)) (fun i => mA _)).
Qed.

Lemma gaussE n (P : probability 'rV[R]_n R) :
  (forall A : 'I_n -> set R, (forall i, measurable (A i)) ->
     P [set x : 'rV[R]_n | forall i, A i (x 0 i)] = (\prod_(i < n) N (A i))%E) ->
  forall X, measurable X -> P X = gauss n X.
Proof.
move=> PA; apply: measure_rowbox_unique.
  by have := probability_le1 P measurableT => /le_lt_trans; apply; rewrite ltry.
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
rewrite [LHS](@ge0_integral_distribution _ _ _ _ _ (N \x gauss n) (@rV_cons R n))//.
rewrite fubini_tonelli1//; first exact: measurableT_comp.
by move=> ?; exact: f0.
Qed.

Lemma integrable_gauss_cons n (f : 'rV[R]_n.+1 -> \bar R) :
  measurable_fun [set: 'rV[R]_n.+1] f ->
  (gauss n.+1).-integrable [set: 'rV[R]_n.+1] f <->
  (N \x gauss n).-integrable [set: measurableTypeR R * 'rV[R]_n] (f \o @rV_cons R n).
Proof.
move=> mf.
have mfc : measurable_fun [set: measurableTypeR R * 'rV[R]_n] (f \o @rV_cons R n).
  exact: measurableT_comp.
have E : \int[gauss n.+1]_x `|f x| = \int[N \x gauss n]_p `|(f \o @rV_cons R n) p|.
  rewrite (@ge0_integral_distribution _ _ _ _ _ (N \x gauss n) (@rV_cons R n))//.
  exact: measurableT_comp.
by split=> /integrableP[_ fi]; apply/integrableP; split => //; [rewrite -E|rewrite E].
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
apply: (@gaussE R n (distribution (gauss n) g) _ X mX) => A mA.
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

Lemma gauss_row_mx n m (X : set 'rV[R]_(n + m)) : measurable X ->
  gauss (n + m) X =
  (gauss n \x gauss m)%E ((fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2) @^-1` X).
Proof.
move=> mX.
have mg : measurable_fun [set: 'rV[R]_n * 'rV[R]_m]
    (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2).
  exact: measurable_row_mx measurable_fst measurable_snd.
pose g : {mfun ('rV[R]_n * 'rV[R]_m)%type >-> 'rV[R]_(n + m)} :=
  HB.pack (fun p : 'rV[R]_n * 'rV[R]_m => row_mx p.1 p.2)
    (isMeasurableFun.Build _ _ _ _ _ mg).
symmetry.
apply: (@gaussE R (n + m) (distribution (gauss n \x gauss m)%E g) _ X mX) => A mA.
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
- by apply: (@measurable_rowbox _ R n (fun i => A (lshift m i))) => i; exact: mA.
- by apply: (@measurable_rowbox _ R m (fun j => A (rshift n j))) => j; exact: mA.
rewrite big_split_ord; congr (_ * _)%E.
- by apply: gauss_box => i; exact: mA.
- by apply: gauss_box => j; exact: mA.
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
  measurable_fun [set: 'rV[R]_n] (fun x : 'rV[R]_n => (x 0 i : measurableTypeR R)).
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
by split=> /integrableP[_ fi]; apply/integrableP; split => //; [rewrite -E|rewrite E].
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

Section gauss_moments.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma mx_norm_exprn_le m n (x : 'M[R]_(m, n)) k :
  `|x| ^+ k <= 1 + \sum_(ij : 'I_m * 'I_n) `|x ij.1 ij.2| ^+ k.
Proof.
set S := \sum_(ij : 'I_m * 'I_n) `|x ij.1 ij.2| ^+ k.
have S0 : 0 <= S by apply: sumr_ge0 => ij _; exact: exprn_ge0.
have -> : `|x| = \big[maxr/0]_ij `|x ij.1 ij.2| by rewrite -mx_normrE.
suff [] : 0 <= \big[maxr/0]_ij `|x ij.1 ij.2| /\
  (\big[maxr/0]_ij `|x ij.1 ij.2|) ^+ k <= 1 + S by [].
apply: (big_ind (fun y => 0 <= y /\ y ^+ k <= 1 + S)).
- by split => //; rewrite expr0n; case: (k == 0%N) => /=; lra.
- move=> a b [a0 ak] [b0 bk]; split; first by rewrite le_max a0.
  by case: (leP a b).
- move=> ij _; split => //.
  have : `|x ij.1 ij.2| ^+ k <= S.
    by rewrite /S (bigD1 ij)//= lerDl sumr_ge0// => ? _; exact: exprn_ge0.
  lra.
Qed.

Lemma integrable_gauss_poly n (f : 'rV[R]_n -> R) (C : R) k :
  measurable_fun [set: 'rV[R]_n] f -> (forall x, `|f x| <= C * (1 + `|x| ^+ k)) ->
  (gauss n).-integrable [set: 'rV[R]_n] (EFin \o f).
Proof.
move=> mf fC.
have C0 : 0 <= C.
  have := fC 0; rewrite normr0 expr0n.
  by have f0 := normr_ge0 (f 0); case: (k == 0%N) => /= h; nra.
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

End gauss_moments.
