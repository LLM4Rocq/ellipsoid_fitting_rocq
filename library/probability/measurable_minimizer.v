From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear rat interval boolp classical_sets.
From mathcomp Require Import functions reals ereal topology normedtype.
From mathcomp Require Import sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix euclidean.
From GaussianAnalysis Require Import self_concordant least_squares minimizers.
From GaussianAnalysis Require Import lindeberg barrier_lindeberg.

(**md**************************************************************************)
(* # Measurable minimizers                                                    *)
(*                                                                            *)
(* Let g t, for t in a measurable space T, be functions on a set D of row     *)
(* vectors, minimized at th t with quadratic growth:                          *)
(*   g t (th t) + c |theta - th t|^2 <= g t theta  for theta in D, c > 0.     *)
(* If the values g t (q m) at the points of a fixed sequence q of D are       *)
(* measurable in t and come arbitrarily close to the minimum, then t |-> th t *)
(* is measurable: th t is the limit of the first minimizers of g t among      *)
(* q 0, ..., q k. This gives a measurable choice of the minimizer of the      *)
(* least squares objective with a barrier of minimizers.v as a function of    *)
(* the features; it does not depend on the features that the objective does  *)
(* not use, as for the leave-one-out objectives of Koehler and Sohn (arXiv    *)
(* 2608.27372, proof of Proposition 2.1, lines 4525-4595).                    *)
(*                                                                            *)
(* ```                                                                        *)
(*        first_min g q k == the first minimizer of g among q 0, ..., q k,    *)
(*                           with its value                                   *)
(* ls_reduced Z P s lambda beta gamma B theta == the objective with a barrier *)
(*                           at (theta, ls_bopt theta), the best b for theta  *)
(* ls_min DV scB B0 D0 Z P s lambda beta gamma == the minimizer over D of     *)
(*                           ls_reduced                                       *)
(* ```                                                                        *)
(*                                                                            *)
(* Main results:                                                              *)
(* - measurable_minimizer: the selection lemma above.                         *)
(* - rel_open_dense_seq: a nonempty relatively open convex set D has a        *)
(*   sequence of points of D that is dense in D.                              *)
(* - ls_minP, ls_min_growth: (ls_min Z, ls_bopt (ls_min Z)) minimizes the     *)
(*   objective with a barrier on D x R, and the reduced objective at theta    *)
(*   in D exceeds its minimum by at least beta lambda |theta - ls_min Z|^2.   *)
(* - measurable_ls_min: Z |-> ls_min Z is measurable.                         *)
(* - ls_min_tuple_set: ls_min does not change when a feature outside P does.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section first_minimizer.
Context {R : realType} {N : nat}.

(* The first minimizer of g among q 0, ..., q k, with its value. *)
Fixpoint first_min (g : 'rV[R]_N -> R) (q : nat -> 'rV[R]_N) (k : nat) :
    'rV[R]_N * R :=
  if k is k'.+1 then
    if g (q k) < (first_min g q k').2 then (q k, g (q k))
    else first_min g q k'
  else (q 0%N, g (q 0%N)).

Lemma first_min_val g q k : (first_min g q k).2 = g (first_min g q k).1.
Proof. by elim: k => [|k IH] //=; case: ifP. Qed.

Lemma first_min_in (D : set 'rV[R]_N) g q k :
  (forall m, D (q m)) -> D (first_min g q k).1.
Proof.
move=> Dq; elim: k => [|k IH] /=; first exact: Dq.
by case: ifP => _; [exact: Dq | exact: IH].
Qed.

Lemma first_min_le g q k m : (m <= k)%N -> (first_min g q k).2 <= g (q m).
Proof.
elim: k m => [|k IH] m; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP ->|mk] /=.
  case: ifP => [_|/negbT]; first exact: lexx.
  by rewrite -leNgt.
case: ifP => [lt|_]; last exact: IH.
exact: le_trans (ltW lt) (IH m mk).
Qed.

Context d (T : measurableType d).

Lemma measurable_first_min (g : T -> 'rV[R]_N -> R) (q : nat -> 'rV[R]_N) k :
  (forall m, measurable_fun setT (fun t => g t (q m))) ->
  measurable_fun setT (fun t => first_min (g t) q k).
Proof.
move=> mg; elim: k => [|k IH] /=.
  exact: measurable_fun_pair (measurable_cst _) (mg 0%N).
apply: measurable_fun_ifT.
- apply: measurable_fun_ltr; first exact: mg.
  exact: measurableT_comp measurable_snd IH.
- exact: measurable_fun_pair (measurable_cst _) (mg _).
- exact: IH.
Qed.

(* The selection lemma. *)
Lemma measurable_minimizer (D : set 'rV[R]_N) (q : nat -> 'rV[R]_N)
    (g : T -> 'rV[R]_N -> R) (th : T -> 'rV[R]_N) (c : R) :
  0 < c -> (forall m, D (q m)) ->
  (forall m, measurable_fun setT (fun t => g t (q m))) ->
  (forall t theta, D theta ->
     g t (th t) + c * mxdot (theta - th t) (theta - th t) <= g t theta) ->
  (forall t (e : R), 0 < e -> exists m, g t (q m) < g t (th t) + e) ->
  measurable_fun setT th.
Proof.
move=> c0 Dq mg grow dens.
pose a k t := (first_min (g t) q k).1.
have ma k : measurable_fun setT (a k).
  exact: measurableT_comp measurable_fst (measurable_first_min k mg).
apply/measurable_fun_mxP => i j; rewrite (ord1 i).
apply: (measurable_fun_cvg (h := fun k t => a k t 0 j)) => [k|t _].
  exact: measurableT_comp (measurable_mxentry 0 j) (ma k).
apply/cvgrPdist_lt => e e0.
have ce0 : 0 < c * e ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
have [m hm] := dens t _ ce0.
exists m => // k /= mk.
have hk := grow t (a k t) (first_min_in (g t) k Dq).
have vk : g t (a k t) <= g t (q m).
  by rewrite /a -first_min_val; exact: first_min_le.
have hd : mxdot (a k t - th t) (a k t - th t) < e ^+ 2.
  by rewrite -(ltr_pM2l c0); lra.
have he := le_lt_trans (mxdot_entry _ 0 j) hd.
rewrite -(ltr_pXn2r (n := 2)) ?nnegrE ?normr_ge0 ?ltW //.
rewrite distrC real_normK ?num_real //.
by move: he; rewrite !mxE.
Qed.

Lemma measurable_mxdot_fun (f g : T -> 'rV[R]_N) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun t => mxdot (f t) (g t)).
Proof.
move=> mf mg; rewrite /mxdot.
apply: measurable_sum => i; apply: measurable_sum => j.
apply: measurable_funM.
- exact: measurableT_comp (measurable_mxentry i j) mf.
- exact: measurableT_comp (measurable_mxentry i j) mg.
Qed.

End first_minimizer.

Section dense_sequence.
Context {R : realType} {N : nat}.

(* A nonempty relatively open convex set has a dense sequence of points:
   the points theta_0 + q E of D, q rational, for an orthonormal basis E of
   its directions (the construction of measurable_inf_rel_open of
   barrier_lindeberg.v). *)
Lemma rel_open_dense_seq (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) :
  rel_open_convex V D -> D !=set0 ->
  exists q : nat -> 'rV[R]_N, (forall m, D (q m)) /\
    forall theta, D theta -> forall e : R, 0 < e ->
      exists m, `|q m - theta| < e.
Proof.
move=> DV [th0 Dth0].
have [_ dir op] := DV.
have [E [EE EV]] := vspace_orthonormal V.
move: E EE EV; set k := \dim V => E EE EV.
pose thq (q : 'rV[rat]_k) := th0 + map_mx (@ratr R) q *m E.
pose thq' q := if `[< D (thq q) >] then thq q else th0.
have Dq q : D (thq' q) by rewrite /thq'; case: asboolP.
pose cnt (m : nat) : 'rV[rat]_k := odflt 0 (@unpickle 'rV[rat]_k m).
exists (fun m => thq' (cnt m)); split => [m|th Dth e e0]; first exact: Dq.
have [e1 e10 he1] := op th Dth.
have k1 : 0 < (k%:R : R) + 1 by rewrite ltr_wpDl.
pose eta := Num.min e e1 / (k%:R + 1).
have mn0 : 0 < Num.min e e1 by rewrite lt_min e0 e10.
have eta0 : 0 < eta by rewrite divr_gt0.
have [y ye] := (EV (th - th0)).1 (dir _ _ Dth0 Dth).
have qex j : exists q : rat, ratr q \in `](y 0 j - eta), (y 0 j + eta)[.
  by apply: rat_in_itvoo; rewrite ltrBlDr -addrA ltrDl addr_gt0.
pose q := \row_j (projT1 (cid (qex j))).
have qj j : `|ratr (q 0 j) - y 0 j| < eta.
  rewrite mxE; case: (cid (qex j)) => /= qq.
  rewrite in_itv /= => /andP[a b].
  by rewrite ltr_norml; apply/andP; split; lra.
pose u := map_mx (@ratr R) q - y.
have thqE : thq q = th + u *m E.
  rewrite /thq /u mulmxBl -ye.
  by apply/rowP => j; rewrite !mxE; ring.
have uEV : u *m E \in V by apply/EV; exists u.
have uEn : `|u *m E| < Num.min e e1.
  apply: le_lt_trans (_ : k%:R * eta < _); last first.
    by rewrite /eta mulrA ltr_pdivrMr // mulrC ltr_pM2l // ltrDl.
  rewrite [leLHS]/Num.Def.normr /= mx_normrE.
  apply: bigmax_le; first by rewrite mulr_ge0 ?ler0n // ltW.
  move=> [i0 j] _ /=; rewrite (ord1 i0) mxE.
  apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite -[k in k%:R]card_ord -sumr_const.
  rewrite mulr_suml; apply: ler_sum => l _; rewrite normrM mul1r.
  apply: le_trans (_ : `|u 0 l| <= _).
    by rewrite ler_piMr // orthonormal_entry_le1.
  have -> : u 0 l = ratr (q 0 l) - y 0 l by rewrite /u !mxE.
  exact: ltW (qj l).
have Dthq : D (thq q).
  rewrite thqE; apply: he1 => //.
  by apply: lt_le_trans uEn _; rewrite ge_min lexx orbT.
exists (pickle q); rewrite /cnt pickleK /= /thq'.
case: asboolP => // _.
rewrite thqE addrAC subrr add0r; apply: lt_le_trans uEn _.
by rewrite ge_min lexx.
Qed.

End dense_sequence.

Section ls_min.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_function V D B).
Hypotheses (B0 : forall z, D z -> 0 <= B z) (D0 : D !=set0).
Variables (n : nat) (P : pred 'I_n) (s lambda beta gamma : R).
Hypotheses (s0 : 0 <= s) (l0 : 0 < lambda) (b0 : 0 < beta) (g0 : 0 < gamma).

(* The objective with a barrier at the best b for theta. *)
Definition ls_reduced (Z : n.-tuple 'rV[R]_N) (theta : 'rV[R]_N) : R :=
  ls_ridge Z P s lambda beta theta (ls_bopt Z P s beta theta) +
  gamma * B theta.

Lemma ls_reduced_le (Z : n.-tuple 'rV[R]_N) theta b :
  ls_reduced Z theta <=
  ls_barrier_objective Z P s lambda beta gamma B theta b.
Proof.
rewrite /ls_reduced /ls_barrier_objective lerD2r.
rewrite [X in _ <= X](ls_ridge_bopt Z lambda _ _ (ls_A0 P s0 b0)).
by rewrite lerDl mulr_ge0 ?sqr_ge0 // ltW // ls_A0.
Qed.

Lemma ls_min_exists (Z : n.-tuple 'rV[R]_N) :
  exists2 theta, D theta &
    forall theta', D theta' -> ls_reduced Z theta <= ls_reduced Z theta'.
Proof.
have k0 : 0 < beta * lambda by rewrite mulr_gt0.
have := @sc_minimizer R N V D B
  (fun theta => ls_ridge Z P s lambda beta theta (ls_bopt Z P s beta theta))
  gamma (beta * lambda) DV scB g0 k0 (@continuous_ls_reduced R N n Z P s lambda beta).
move=> /(_ _ B0 _ D0) [].
- by move=> z y t _ _ tt; exact: convex_ls_reduced.
- by move=> z; exact: ls_ridge_coercive.
by move=> zm Dzm hzm; exists zm.
Qed.

Definition ls_min (Z : n.-tuple 'rV[R]_N) : 'rV[R]_N :=
  s2val (cid2 (ls_min_exists Z)).

Lemma ls_min_in Z : D (ls_min Z).
Proof. exact: (s2valP (cid2 (ls_min_exists Z))). Qed.

Lemma ls_min_le Z theta : D theta -> ls_reduced Z (ls_min Z) <= ls_reduced Z theta.
Proof. exact: (s2valP' (cid2 (ls_min_exists Z))). Qed.

(* (ls_min Z, ls_bopt (ls_min Z)) minimizes the objective with a barrier. *)
Lemma ls_minP Z theta b : D theta ->
  ls_barrier_objective Z P s lambda beta gamma B (ls_min Z)
    (ls_bopt Z P s beta (ls_min Z)) <=
  ls_barrier_objective Z P s lambda beta gamma B theta b.
Proof.
move=> Dth; apply: le_trans (ls_min_le Z Dth) (ls_reduced_le Z theta b).
Qed.

(* Quadratic growth of the reduced objective away from ls_min Z. *)
Lemma ls_min_growth Z theta : D theta ->
  ls_reduced Z (ls_min Z) +
    beta * lambda * mxdot (theta - ls_min Z) (theta - ls_min Z) <=
  ls_reduced Z theta.
Proof.
move=> Dth; set th0 := ls_min Z; set b0' := ls_bopt Z P s beta th0.
have Dth0 : D th0 := ls_min_in Z.
have [_ dir _] := DV.
have hV : theta - th0 \in V := dir _ _ Dth0 Dth.
have thmin theta' b' : D theta' ->
    ls_barrier_objective Z P s lambda beta gamma B th0 b0' <=
    ls_barrier_objective Z P s lambda beta gamma B theta' b'.
  by move=> Dt; exact: ls_minP.
have e1 : th0 + (theta - th0) = theta by rewrite addrC subrK.
have e2 : b0' + (ls_bopt Z P s beta theta - b0') = ls_bopt Z P s beta theta.
  by rewrite addrC subrK.
have E := ls_taylor DV scB Dth0 thmin (ls_bopt Z P s beta theta - b0') hV.
rewrite e1 e2 in E.
have Bg : 0 <= bregman_div B theta th0.
  have := sc_bregman_ge DV scB Dth0 hV; rewrite e1 => /(_ Dth).
  by apply: le_trans; apply: sc_omega_ge0; exact: sqrtr_ge0.
have Rc := ls_ridge_coercive Z P lambda s0 b0 (theta - th0)
  (ls_bopt Z P s beta theta - b0').
have gB : 0 <= gamma * bregman_div B theta th0 by rewrite mulr_ge0 // ltW.
have F1 : ls_barrier_objective Z P s lambda beta gamma B theta
    (ls_bopt Z P s beta theta) = ls_reduced Z theta by [].
have F0 : ls_barrier_objective Z P s lambda beta gamma B th0 b0' =
    ls_reduced Z th0 by [].
rewrite F1 F0 in E.
lra.
Qed.

Lemma ls_min_unique Z theta : D theta ->
  (forall theta', D theta' -> ls_reduced Z theta <= ls_reduced Z theta') ->
  theta = ls_min Z.
Proof.
move=> Dth hth; have := ls_min_growth Z Dth.
have := hth _ (ls_min_in Z).
set u := theta - ls_min Z => h1 h2.
have : beta * lambda * mxdot u u <= 0 by lra.
rewrite pmulr_rle0 ?mulr_gt0 // => hu.
have /eqP : mxdot u u = 0 by apply/eqP; rewrite eq_le hu mxdot_ge0.
by rewrite mxdot_eq0 subr_eq0 => /eqP.
Qed.

(* The minimizer is a measurable function of the features. *)
Lemma measurable_ls_reduced_at theta :
  measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => ls_reduced Z theta).
Proof.
apply: measurable_funD; first exact: measurable_ls_reduced.
exact: measurable_cst.
Qed.

Lemma measurable_ls_min : measurable_fun setT ls_min.
Proof.
have [q [Dq qd]] := rel_open_dense_seq DV D0.
apply: (measurable_minimizer (D := D) (q := q) (g := ls_reduced)
  (c := beta * lambda)) => //.
- by rewrite mulr_gt0.
- by move=> m; exact: measurable_ls_reduced_at.
- by move=> Z theta Dth; exact: ls_min_growth.
move=> Z e e0; set th0 := ls_min Z.
have Dth0 : D th0 := ls_min_in Z.
have e2 : 0 < e / 2 by rewrite divr_gt0.
have g0' : 0 < e / 2 / gamma by rewrite divr_gt0.
have [d1 d10 hd1] := sc_function_continuous DV scB Dth0 g0'.
have := @continuous_ls_reduced R N n Z P s lambda beta th0.
move=> /cvgrPdist_lt /(_ _ e2) /(@nbhs_normP R 'rV[R]_N th0) [d2 d20 hd2].
have d12 : 0 < Num.min d1 d2 by rewrite lt_min d10 d20.
have [m hm] := qd th0 Dth0 _ d12.
exists m.
have hq1 : `|q m - th0| < d1 by apply: lt_le_trans hm _; rewrite ge_min lexx.
have hq2 : `|q m - th0| < d2.
  by apply: lt_le_trans hm _; rewrite ge_min lexx orbT.
have hB := hd1 _ (Dq m) hq1.
rewrite ltr_pdivlMr // in hB.
have := hd2 (q m); rewrite /ball_ /= distrC => /(_ hq2) hr.
have hn := ler_norm (B (q m) - B th0).
rewrite -(ler_pM2r g0) in hn.
have h3 := le_lt_trans hn hB.
rewrite ltr_norml in hr; case/andP: hr => hr _.
rewrite /ls_reduced; lra.
Qed.

(* The best b at the minimizer, and the values of the linear forms of the
   features there, are measurable functions of the features. *)
Lemma measurable_mxdot_ls_min (i : 'I_n) :
  measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => mxdot (tnth Z i) (ls_min Z)).
Proof.
apply: measurable_mxdot_fun; last exact: measurable_ls_min.
exact: measurable_tnth.
Qed.

Lemma measurable_ls_bopt_min :
  measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => ls_bopt Z P s beta (ls_min Z)).
Proof.
rewrite /ls_bopt; apply: measurable_funM; last exact: measurable_cst.
apply: measurable_funM; first exact: measurable_cst.
by apply: measurable_sum_pred => i _; exact: measurable_mxdot_ls_min.
Qed.

(* The minimizer does not depend on the features outside P. *)
Lemma ls_bopt_tuple_set (Z : n.-tuple 'rV[R]_N) i t theta :
  ~~ P i -> ls_bopt (tuple_set Z i t) P s beta theta = ls_bopt Z P s beta theta.
Proof.
move=> Pi; rewrite /ls_bopt; congr (_ * _ / _); apply: eq_bigr => j Pj.
by rewrite tnth_tuple_set_neq //; apply: contraNneq Pi => <-.
Qed.

Lemma ls_reduced_tuple_set (Z : n.-tuple 'rV[R]_N) i t theta :
  ~~ P i -> ls_reduced (tuple_set Z i t) theta = ls_reduced Z theta.
Proof.
move=> Pi.
have El b : ls_loss (tuple_set Z i t) P theta b = ls_loss Z P theta b.
  rewrite /ls_loss; apply: eq_bigr => j Pj.
  by rewrite tnth_tuple_set_neq //; apply: contraNneq Pi => <-.
by rewrite /ls_reduced /ls_ridge (ls_bopt_tuple_set Z t theta Pi) El.
Qed.

Lemma ls_min_tuple_set (Z : n.-tuple 'rV[R]_N) i t :
  ~~ P i -> ls_min (tuple_set Z i t) = ls_min Z.
Proof.
move=> Pi; symmetry; apply: ls_min_unique; first exact: ls_min_in.
move=> theta Dth; rewrite !(ls_reduced_tuple_set Z t _ Pi).
exact: ls_min_le.
Qed.

End ls_min.
