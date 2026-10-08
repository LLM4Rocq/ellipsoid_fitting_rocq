From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import sesquilinear rat interval boolp classical_sets.
From mathcomp Require Import functions reals ereal topology normedtype.
From mathcomp Require Import sequences derive realfun exp measure.
From mathcomp Require Import lebesgue_measure measurable_realfun.
From mathcomp Require Import lebesgue_integral probability.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis Require Import measurable_matrix euclidean opnorm.
From GaussianAnalysis Require Import real_spectral self_concordant.
From GaussianAnalysis Require Import least_squares minimizers ls_insertion.
From GaussianAnalysis Require Import feature_moments.
From GaussianAnalysis Require Import lindeberg tuple_rows efron_stein.

(**md**************************************************************************)
(* # Universality of barrier-regularized least squares                        *)
(*                                                                            *)
(* Theorem 2.9 of Koehler and Sohn (arXiv 2608.27372, lines 1282-1344, proof  *)
(* lines 1637-2116 and 3809-4225), in the paper's abstract feature form, for  *)
(* two laws mu and nu of features on 'rV[R]_N that are (K, tau)-regular with  *)
(* the same covariance Sigma (regular_feature of least_squares.v), with       *)
(* lambda = opnorm Sigma and tau >= 0. D is nonempty, convex and relatively   *)
(* open with directions V (rel_open_convex), B >= 0 is a self-concordant      *)
(* function on D (sc_function), beta, gamma > 0 and n > 0. Phi Z is the value *)
(* ls_barrier_value Z lambda beta D gamma B of the features Z, and            *)
(*   Lref = (1 + 1 / beta) (1 + inf_(theta in D) (lambda |theta|^2            *)
(*          + gamma B theta))                                                 *)
(* is ls_ref_scale lambda beta gamma D B. The paper asks D to be bounded and  *)
(* B to be a barrier; the proof uses neither.                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*  hybrid mu nu k == the laws of the coordinates of the Lindeberg argument:  *)
(*                    mu before the coordinate k, nu from k on                *)
(* ```                                                                        *)
(*                                                                            *)
(* - barrier_lindeberg_mean, (2.12): if 36 <= n gamma, then                   *)
(*     |E_(mu^n) Phi - E_(nu^n) Phi| <= 100 (1 + K^4)^2 Lref^2                *)
(*       ((n gamma)^(-1/2) + sqrt (dim V) (tau / lambda + 1) / n).            *)
(* - barrier_lindeberg_variance, (2.13): Var_(mu^n) Phi <=                    *)
(*   4 (1 + K^4)^2 Lref^2 / n.                                                *)
(* - barrier_lindeberg_concentration, (2.14): for t > 0 and 36 <= n gamma,    *)
(*   Phi is within the bound of (2.12) plus t of E_(nu^n) Phi, except on an   *)
(*   event of mu^n-probability at most 4 (1 + K^4)^2 Lref^2 / (n t^2).        *)
(* The hypotheses are symmetric in mu and nu, so the last two hold for nu.    *)
(*                                                                            *)
(* The proof is the paper's. measurable_ls_barrier_value: Phi is a measurable *)
(* function of the features (an infimum over a countable dense subset of D).  *)
(* lindeberg_telescope: the replacement argument for an integrable functional *)
(* with bounds that depend on the other coordinates. insertion_compare        *)
(* (Propositions 2.14 and 2.16): the comparison of the means of an insertion  *)
(* cost under mu and nu, from its pointwise bounds (ls_insertion.v) and the   *)
(* moment calculus of feature_moments.v; le_amgm turns the Cauchy-Schwarz     *)
(* step into an infimum over a weight. loo_compare and loo_variance: the same *)
(* for the value, at the leave-one-out minimizer of minimizers.v.             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section measurable_inf.
Context {R : realType} {N : nat} d (T : measurableType d).

(* The entries of a matrix with orthonormal rows are at most 1. *)
Lemma orthonormal_entry_le1 k (E : 'M[R]_(k, N)) l j :
  E *m E^T = 1%:M -> `|E l j| <= 1.
Proof.
move=> EE.
have h := mxdot_entry (row l E) 0 j.
have e1 : mxdot (row l E) (row l E) = 1.
  have := congr1 (fun A : 'M[R]_k => A l l) EE.
  rewrite [in X in _ = X -> _]mxE eqxx mulr1n => <-.
  by rewrite mxE /mxdot big_ord1; apply: eq_bigr => p _; rewrite !mxE.
rewrite e1 mxE in h.
rewrite -(ler_sqr (normr_ge0 _) ler01) ?nnegrE ?normr_ge0 ?ler01 //.
by rewrite expr1n real_normK ?num_real.
Qed.

(* An infimum over a relatively open convex set of an upper semicontinuous
   family of measurable functions is measurable: it is the infimum over the
   countable dense set of the points theta_0 + q E, q rational. *)
Lemma measurable_inf_rel_open (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N)
    (g : T -> 'rV[R]_N -> R) :
  rel_open_convex V D -> D !=set0 ->
  (forall th, measurable_fun setT (g ^~ th)) ->
  (forall t th, D th -> forall e : R, 0 < e -> exists2 dl : R, 0 < dl &
     forall th', D th' -> `|th' - th| < dl -> g t th' < g t th + e) ->
  (forall t th, D th -> 0 <= g t th) ->
  measurable_fun setT (fun t => inf [set g t th | th in D]).
Proof.
move=> DV [th0 Dth0] mg usc g0.
have [_ dir op] := DV.
have [E [EE EV]] := vspace_orthonormal V.
move: E EE EV; set k := \dim V => E EE EV.
(* the countable family theta_0 + q E, q rational, moved into D *)
pose thq (q : 'rV[rat]_k) := th0 + map_mx (@ratr R) q *m E.
pose thq' q := if `[< D (thq q) >] then thq q else th0.
have Dq q : D (thq' q) by rewrite /thq'; case: asboolP.
pose cnt (m : nat) : 'rV[rat]_k := odflt 0 (@unpickle 'rV[rat]_k m).
pose h (m : nat) (t : T) := g t (thq' (cnt m)).
have dens t th : D th -> forall e : R, 0 < e -> exists m, h m t < g t th + e.
  move=> Dth e e0.
  have [dl dl0 hdl] := usc t th Dth e e0.
  have [e1 e10 he1] := op th Dth.
  have k1 : 0 < (k%:R : R) + 1 by rewrite ltr_wpDl.
  pose eta := Num.min dl e1 / (k%:R + 1).
  have mn0 : 0 < Num.min dl e1 by rewrite lt_min dl0 e10.
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
  have uEn : `|u *m E| < Num.min dl e1.
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
  exists (pickle q); rewrite /h /cnt pickleK /= /thq'.
  case: asboolP => // _; apply: hdl => //.
  rewrite thqE addrAC subrr add0r; apply: lt_le_trans uEn _.
  by rewrite ge_min lexx.
(* so the infimum is the infimum over the countable family *)
have key t : inf [set g t th | th in D] = infs (h ^~ t) 0.
  rewrite /infs /=.
  set S1 := [set g t th | th in D]; set S2 := sdrop _ _.
  have S21 : S2 `<=` S1 by move=> _ [m _ <-]; exists (thq' (cnt m)).
  have S1lb : has_lbound S1 by exists 0 => _ [th Dth <-]; exact: g0.
  have S2n : S2 !=set0 by exists (h 0%N t), 0%N.
  apply/eqP; rewrite eq_le; apply/andP; split.
    by apply: lb_le_inf S2n _ => y /S21 S1y; apply: (ge_inf S1lb).
  apply/ler_addgt0Pr => e e0.
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have S1n : S1 !=set0 by exists (g t th0), th0.
  have [_ [th Dth <-] hy] := inf_adherent e2 (conj S1n S1lb).
  have [m hm] := dens t th Dth _ e2.
  have S2lb : has_lbound S2.
    by exists 0 => y /S21 [th' Dth' <-]; exact: g0.
  have S2m : S2 (h m t) by exists m.
  apply: le_trans (ge_inf S2lb S2m) _.
  by apply: ltW; lra.
have -> : (fun t => inf [set g t th | th in D]) =
    (fun t => infs (h ^~ t) 0) by apply/funext => t; exact: key.
apply: measurable_fun_infs => [t _|m]; last exact: mg.
by exists 0 => _ [m _ <-]; exact: g0.
Qed.

End measurable_inf.

Section measurable_values.
Context {R : realType} {N : nat}.

Lemma measurable_mxdot_tnth n (i : 'I_n) (th : 'rV[R]_N) :
  measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => mxdot (tnth Z i) th).
Proof.
apply: (measurableT_comp (f := fun z : 'rV[R]_N => mxdot z th)).
  by apply: continuous_measurable_mx; exact: continuous_mxdotl.
exact: measurable_tnth.
Qed.

Lemma measurable_sum_pred d (T : measurableType d) n (P : pred 'I_n)
    (h : 'I_n -> T -> R) :
  (forall i, P i -> measurable_fun setT (h i)) ->
  measurable_fun setT (fun x => \sum_(i < n | P i) h i x).
Proof.
move=> mh.
have -> : (fun x => \sum_(i < n | P i) h i x) =
    (fun x => \sum_(i < n) (if P i then h i x else 0)).
  by apply/funext => x; rewrite big_mkcond.
apply: measurable_sum => i.
case Pi : (P i); first exact: mh.
exact: measurable_cst.
Qed.

Lemma measurable_ls_reduced n (P : pred 'I_n) (s lambda beta : R)
    (th : 'rV[R]_N) :
  measurable_fun setT (fun Z : n.-tuple 'rV[R]_N =>
    ls_ridge Z P s lambda beta th (ls_bopt Z P s beta th)).
Proof.
have md i := @measurable_mxdot_tnth n i th.
have mb : measurable_fun setT (fun Z : n.-tuple 'rV[R]_N =>
    ls_bopt Z P s beta th).
  rewrite /ls_bopt; apply: measurable_funM; last exact: measurable_cst.
  apply: measurable_funM; first exact: measurable_cst.
  by apply: measurable_sum_pred => i _; exact: md.
rewrite /ls_ridge /ls_loss.
apply: measurable_funD.
  apply: measurable_funM; first exact: measurable_cst.
  apply: measurable_sum_pred => i _; apply: measurable_funX.
  exact: measurable_funB.
apply: measurable_funM; first exact: measurable_cst.
apply: measurable_funD; first exact: measurable_cst.
exact: measurable_funX.
Qed.

End measurable_values.

Section ls_value_measurable.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Hypothesis DV : rel_open_convex V D.
Hypothesis D0 : D !=set0.
Hypothesis B0 : forall z, D z -> 0 <= B z.
Hypothesis Bc : forall z, D z -> forall e : R, 0 < e ->
  exists2 dl : R, 0 < dl & forall y, D y -> `|y - z| < dl -> `|B y - B z| < e.

Lemma ls_ridge_ge0' n (Z : n.-tuple 'rV[R]_N) (P : pred 'I_n)
    (s lambda beta : R) th b :
  0 <= s -> 0 <= lambda -> 0 <= beta -> 0 <= ls_ridge Z P s lambda beta th b.
Proof.
move=> s0 l0 b0; rewrite /ls_ridge; apply: addr_ge0.
  by apply: mulr_ge0 => //; apply: sumr_ge0 => i _; exact: sqr_ge0.
apply: mulr_ge0 => //; apply: addr_ge0 (sqr_ge0 _).
by rewrite mulr_ge0 ?mxdot_ge0.
Qed.

(* The value is the infimum over D of the objective with the optimal b. *)
Lemma ls_barrier_valueE n (Z : n.-tuple 'rV[R]_N) (lambda beta gamma : R) :
  (0 < n)%N -> 0 <= lambda -> 0 <= beta -> 0 <= gamma ->
  ls_barrier_value Z lambda beta D gamma B =
  inf [set ls_ridge Z predT (n%:R *+ 2)^-1 lambda beta th
         (ls_bopt Z predT (n%:R *+ 2)^-1 beta th) + gamma * B th | th in D].
Proof.
move=> n0 l0 b0 g0.
set s := (n%:R *+ 2)^-1.
have s0 : 0 <= s by rewrite invr_ge0 mulrn_wge0 // ler0n.
rewrite /ls_barrier_value.
have A0 : 0 < s * #|predT : pred 'I_n|%:R + beta.
  rewrite ltr_wpDr // mulr_gt0 // ?invr_gt0 ?mulrn_wgt0 ?ltr0n //.
  by rewrite cardT size_enum_ord.
set S := [set _ | _ in _ & _ in _]; set S' := [set _ | _ in _].
have S'S : S' `<=` S.
  move=> _ [th Dth <-]; exists th => //.
  by exists (ls_bopt Z predT s beta th).
have Slb : has_lbound S.
  exists 0 => _ [th Dth [b _ <-]].
  by apply: addr_ge0; [exact: ls_ridge_ge0' | rewrite mulr_ge0 ?B0].
have S'lb : has_lbound S'.
  exists 0 => _ [th Dth <-].
  by apply: addr_ge0; [exact: ls_ridge_ge0' | rewrite mulr_ge0 ?B0].
have [th0 Dth0] := D0.
have S'n : S' !=set0.
  by exists (ls_ridge Z predT s lambda beta th0
    (ls_bopt Z predT s beta th0) + gamma * B th0), th0.
have Sn : S !=set0 by have [y /S'S Sy] := S'n; exists y.
apply/eqP; rewrite eq_le; apply/andP; split.
  by apply: lb_le_inf S'n _ => y /S'S Sy; apply: (ge_inf Slb).
apply: lb_le_inf Sn _ => _ [th Dth [b _ <-]].
apply: le_trans (_ : ls_ridge Z predT s lambda beta th
  (ls_bopt Z predT s beta th) + gamma * B th <= _).
  by apply: (ge_inf S'lb); exists th.
rewrite lerD2r /ls_objective [X in _ <= X](ls_ridge_bopt Z lambda _ b A0).
by rewrite lerDl mulr_ge0 ?sqr_ge0 // ltW.
Qed.

(* The values Phi_Z(D, B; beta, gamma) are measurable functions of the
   features. *)
Lemma measurable_ls_barrier_value n (lambda beta gamma : R) :
  0 <= lambda -> 0 <= beta -> 0 <= gamma ->
  measurable_fun setT
    (fun Z : n.-tuple 'rV[R]_N => ls_barrier_value Z lambda beta D gamma B).
Proof.
move=> l0 b0 g0.
case: n => [|n].
  have -> : (fun Z : 0.-tuple 'rV[R]_N =>
      ls_barrier_value Z lambda beta D gamma B) =
      cst (ls_barrier_value [tuple] lambda beta D gamma B).
    by apply/funext => Z; rewrite (tuple0 Z).
  exact: measurable_cst.
have -> : (fun Z : n.+1.-tuple 'rV[R]_N =>
    ls_barrier_value Z lambda beta D gamma B) =
    (fun Z => inf [set ls_ridge Z predT (n.+1%:R *+ 2)^-1 lambda beta th
       (ls_bopt Z predT (n.+1%:R *+ 2)^-1 beta th) + gamma * B th | th in D]).
  by apply/funext => Z; rewrite ls_barrier_valueE.
apply: (measurable_inf_rel_open DV D0).
- move=> th; apply: measurable_funD; first exact: measurable_ls_reduced.
  exact: measurable_cst.
- move=> Z th Dth e e0.
  have e2 : 0 < e / 2 by rewrite divr_gt0.
  have g1 : 0 < gamma + 1 by rewrite ltr_wpDl.
  have [d1 d10 hd1] := Bc Dth (divr_gt0 e2 g1).
  have := @continuous_ls_reduced R N n.+1 Z predT (n.+1%:R *+ 2)^-1
    lambda beta th.
  move=> /cvgrPdist_lt /(_ _ e2) /(@nbhs_normP R 'rV[R]_N th) [d2 d20 hd2].
  exists (Num.min d1 d2); first by rewrite lt_min d10 d20.
  move=> th' Dth'; rewrite lt_min => /andP[t1 t2].
  have := hd1 th' Dth' t1 => hB.
  have := hd2 th'; rewrite /ball_ /= distrC => /(_ t2) hg.
  have hB' : gamma * B th' <= gamma * B th + e / 2.
    have h1 : gamma * (B th' - B th) <= gamma * `|B th' - B th|.
      by rewrite ler_wpM2l // ler_norm.
    have h2 : gamma * `|B th' - B th| <=
        (gamma + 1) * (e / 2 / (gamma + 1)).
      by apply: ler_pM; rewrite ?normr_ge0 // ?lerDl // ltW.
    move: h2; rewrite [X in _ <= X]mulrC divfK ?gt_eqF // => h2.
    by move: h1; rewrite mulrBr; lra.
  by move: hg; rewrite ltr_norml => /andP[hg _]; lra.
move=> Z th Dth; apply: addr_ge0; last by rewrite mulr_ge0 ?B0.
exact: ls_ridge_ge0'.
Qed.

End ls_value_measurable.

Section telescoping.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* The hybrid law: mu for the coordinates < k, nu for the others. *)
Definition hybrid (mu nu : probability T R) (k : nat) (j : nat) :
    probability T R :=
  if (j < k)%N then mu else nu.

Lemma probability_inhabited (mu : probability T R) : exists t : T, True.
Proof.
apply: contrapT => noT; have T0 : [set: T] = set0.
  by apply/seteqP; split => // t _; apply: noT; exists t.
have := @probability_setT _ _ _ mu.
by rewrite T0 measure0 => /esym/eqP; rewrite onee_eq0.
Qed.

(* The integral of a function that does not depend on the coordinate i does
   not depend on the law of that coordinate. *)
Lemma integral_tuple_prod_free (rho rho' : nat -> probability T R) n
    (i : 'I_n) (G : n.-tuple T -> \bar R) :
  measurable_fun setT G -> (forall x t, G (tuple_set x i t) = G x) ->
  (forall j, j != nat_of_ord i -> rho j = rho' j) ->
  \int[tuple_prod rho n]_x G x = \int[tuple_prod rho' n]_x G x.
Proof.
move=> mG Gfree rr.
have [t0 _] := probability_inhabited (rho 0%N).
(* both laws give the same law to tuple_set x i t0 *)
pose g (j : nat) : T -> T := if j == nat_of_ord i then fun=> t0 else id.
pose mu2 (j : nat) : probability T R :=
  if j == nat_of_ord i then (dirac t0 : probability T R) else rho j.
have gm j : measurable_fun setT (g j).
  by rewrite /g; case: ifP => _; [exact: measurable_cst | exact: measurable_id].
have gx x : tuple_map g x = tuple_set x i t0.
  apply: eq_from_tnth => j; rewrite !tnth_mktuple /g.
  have -> : (nat_of_ord j == nat_of_ord i) = (j == i) by [].
  by case: (j == i).
have E (r : nat -> probability T R) :
    (forall j, j != nat_of_ord i -> r j = rho j) ->
    \int[tuple_prod r n]_x G x = \int[tuple_prod mu2 n]_x G x.
  move=> hr; rewrite (integral_tuple_map (nu := r) (mu := mu2) (g := g)) //.
    move=> j A mA; rewrite /mu2 /g; case: eqP => [ji|/eqP ji].
      rewrite /= diracE preimage_cst; case: (asboolP (A t0)) => At0.
        by rewrite mem_set // probability_setT.
      by rewrite memNset // measure0.
    by rewrite hr.
  by apply: eq_integral => x _; rewrite gx Gfree.
by rewrite (E rho) // (E rho') // => j ji; rewrite -rr.
Qed.

Lemma tnth_tuple_set n (x : n.-tuple T) (i : 'I_n) (t : T) :
  tnth (tuple_set x i t) i = t.
Proof. by rewrite tnth_mktuple eqxx. Qed.

Lemma tnth_tuple_set_neq n (x : n.-tuple T) (i j : 'I_n) (t : T) :
  j != i -> tnth (tuple_set x i t) j = tnth x j.
Proof. by move=> ji; rewrite tnth_mktuple (negbTE ji). Qed.

(* The law of the coordinate j of tuple_prod rho n is rho j. *)
Lemma ge0_integral_tuple_prod_tnth (rho : nat -> probability T R) n
    (j : 'I_n) (g : T -> \bar R) :
  measurable_fun setT g -> (forall t, 0 <= g t) ->
  \int[tuple_prod rho n]_x g (tnth x j) = \int[rho j]_t g t.
Proof.
move=> mg g0.
have mG : measurable_fun setT (fun x : n.-tuple T => g (tnth x j)).
  exact: measurableT_comp mg (measurable_tnth j).
rewrite (ge0_integral_tuple_prod_set rho j mG (fun x => g0 _)).
under eq_integral do under eq_integral do rewrite tnth_tuple_set.
by rewrite integral_cst //= [X in _ * X]probability_setT mule1.
Qed.

Lemma integrable_tuple_prod_tnth (rho : nat -> probability T R) n
    (j : 'I_n) (g : T -> R) :
  (rho j).-integrable setT (EFin \o g) ->
  (tuple_prod rho n).-integrable setT (EFin \o (fun x => g (tnth x j))).
Proof.
move=> /integrableP[mg ig]; apply/integrableP; split.
  exact: measurableT_comp mg (measurable_tnth j).
rewrite (ge0_integral_tuple_prod_tnth rho j (g := fun t => (`|g t|)%:E)) //.
apply/measurable_EFinP; apply: measurableT_comp => //.
exact/measurable_EFinP.
Qed.

Lemma Rintegral_tuple_prod_tnth (rho : nat -> probability T R) n
    (j : 'I_n) (g : T -> R) :
  measurable_fun setT g -> (forall t, 0 <= g t)%R ->
  (\int[tuple_prod rho n]_x g (tnth x j) = \int[rho j]_t g t)%R.
Proof.
move=> mg g0; rewrite /Rintegral.
rewrite (ge0_integral_tuple_prod_tnth rho j (g := fun t => (g t)%:E)) //.
exact/measurable_EFinP.
Qed.

(* Lindeberg's replacement with integrable functionals and bounds that
   depend on the other coordinates: for F >= 0, replacing the laws mu of
   the coordinates by nu changes the expectation of F by at most
   sum_i E_(hybrid i) b_i, if b_i bounds the change of the integral in the
   coordinate i. *)
Lemma lindeberg_telescope (mu nu : probability T R) n (F : n.-tuple T -> R)
    (b : 'I_n -> n.-tuple T -> R) :
  measurable_fun setT F -> (forall x, (0 <= F x)%R) ->
  (forall k, (k <= n)%N ->
     (tuple_prod (hybrid mu nu k) n).-integrable setT (EFin \o F)) ->
  (forall (i : 'I_n) x,
     mu.-integrable setT (fun t => (F (tuple_set x i t))%:E) /\
     nu.-integrable setT (fun t => (F (tuple_set x i t))%:E)) ->
  (forall i : 'I_n, measurable_fun setT (b i)) ->
  (forall i : 'I_n,
     (tuple_prod (hybrid mu nu i) n).-integrable setT (EFin \o b i)) ->
  (forall (i : 'I_n) x, (`|\int[mu]_t F (tuple_set x i t) -
                 \int[nu]_t F (tuple_set x i t)| <= b i x)%R) ->
  (`|\int[tuple_prod (fun=> mu) n]_x F x - \int[tuple_prod (fun=> nu) n]_x F x|
    <= \sum_(i < n) \int[tuple_prod (hybrid mu nu i) n]_x b i x)%R.
Proof.
move=> mF F0 Fi Fx mb bi hb.
pose P k := tuple_prod (hybrid mu nu k) n.
have Pn : tuple_prod (fun=> mu) n = P n.
  by apply: eq_tuple_prod => j jn; rewrite /hybrid jn.
have P0 : tuple_prod (fun=> nu) n = P 0%N by apply: eq_tuple_prod.
pose G (rho : probability T R) (i : 'I_n) x :=
  (\int[rho]_t F (tuple_set x i t))%R.
have GE (rho : probability T R) (i : 'I_n) x :
    rho.-integrable setT (fun t => (F (tuple_set x i t))%:E) ->
    (G rho i x)%:E = \int[rho]_t (F (tuple_set x i t))%:E.
  by move=> h; rewrite /G Rintegral_EFin.
have Gfree rho (i : 'I_n) x t : G rho i (tuple_set x i t) = G rho i x.
  by rewrite /G; apply: eq_Rintegral => s _; rewrite tuple_set_set.
have mG (rho : probability T R) (i : 'I_n) :
    (forall x, rho.-integrable setT (fun t => (F (tuple_set x i t))%:E)) ->
    measurable_fun setT (G rho i).
  move=> hr; apply/measurable_EFinP.
  have mFE : measurable_fun setT (EFin \o F) by exact/measurable_EFinP.
  have F0E x : (0 <= (EFin \o F) x)%E by rewrite /= lee_fin.
  have := @measurable_tuple_set_integral _ T R (fun=> rho) n i (EFin \o F)
    mFE F0E.
  by apply: eq_measurable_fun => x _; rewrite /= GE.
have mFE : measurable_fun setT (EFin \o F) by exact/measurable_EFinP.
have F0E x : (0 <= (EFin \o F) x)%E by rewrite /= lee_fin.
have fub (k : nat) (i : 'I_n) :
    hybrid mu nu k i = mu \/ hybrid mu nu k i = nu.
  by rewrite /hybrid; case: ifP; [left|right].
have intx (k : nat) (i : 'I_n) x :
    (hybrid mu nu k i).-integrable setT (fun t => (F (tuple_set x i t))%:E).
  by case: (fub k i) => ->; [exact: (Fx i x).1 | exact: (Fx i x).2].
have fub' (k : nat) (i : 'I_n) :
    \int[P k]_x (F x)%:E = \int[P k]_x (G (hybrid mu nu k i) i x)%:E.
  rewrite (ge0_integral_tuple_prod_set _ i mFE F0E).
  by apply: eq_integral => x _; rewrite /= GE.
have E1 (i : 'I_n) : \int[P i.+1]_x (F x)%:E = \int[P i]_x (G mu i x)%:E.
  rewrite (fub' i.+1 i) /hybrid ltnSn.
  have mGi : measurable_fun setT (EFin \o G mu i).
    by apply/measurable_EFinP; apply: mG => x; exact: (Fx i x).1.
  have Gfi x t : (EFin \o G mu i) (tuple_set x i t) = (EFin \o G mu i) x.
    by rewrite /= Gfree.
  have hl j : j != nat_of_ord i -> hybrid mu nu i.+1 j = hybrid mu nu i j.
    by move=> ji; rewrite /hybrid ltnS leq_eqVlt (negbTE ji).
  exact: (integral_tuple_prod_free mGi Gfi hl).
have E2 (i : 'I_n) : \int[P i]_x (F x)%:E = \int[P i]_x (G nu i x)%:E.
  by rewrite (fub' i i) /hybrid ltnn.
have Gint (rho : probability T R) (i : 'I_n) (k : nat) : (k <= n)%N ->
    (forall x, rho.-integrable setT (fun t => (F (tuple_set x i t))%:E)) ->
    \int[P k]_x (F x)%:E = \int[P i]_x (G rho i x)%:E ->
    (P i).-integrable setT (EFin \o G rho i).
  move=> kn hr hE; apply/integrableP; split.
    by apply/measurable_EFinP; exact: mG.
  have G0 x : (0 <= G rho i x)%R by apply: Rintegral_ge0 => t _; exact: F0.
  under eq_integral do rewrite /= ger0_norm ?G0 //.
  rewrite -hE; have /integrableP[_] := Fi k kn.
  by under eq_integral do rewrite /= ger0_norm ?F0 //.
have Gmi (i : 'I_n) : (P i).-integrable setT (EFin \o G mu i).
  exact: (Gint mu i i.+1 (ltn_ord i) (fun x => (Fx i x).1) (E1 i)).
have Gni (i : 'I_n) : (P i).-integrable setT (EFin \o G nu i).
  exact: (Gint nu i i (ltnW (ltn_ord i)) (fun x => (Fx i x).2) (E2 i)).
have Di (i : 'I_n) : (\int[P i.+1]_x F x - \int[P i]_x F x =
    \int[P i]_x (G mu i x - G nu i x))%R.
  rewrite (RintegralB measurableT (Gmi i) (Gni i)).
  by rewrite /Rintegral E1 E2.
rewrite Pn P0.
rewrite -(telescope_sumr (fun k => \int[P k]_x F x)%R (leq0n n)) big_mkord.
under eq_bigr do rewrite Di.
apply: (le_trans (ler_norm_sum _ _ _)); apply: ler_sum => i _.
have Gi : (P i).-integrable setT (EFin \o (fun x => G mu i x - G nu i x)%R).
  exact: (integrableB measurableT (Gmi i) (Gni i)).
apply: (le_trans (le_normr_Rintegral measurableT Gi)).
apply: le_Rintegral => //; first exact: integrable_norm.
  exact: bi.
by move=> x _; exact: hb.
Qed.

End telescoping.

Section real_bounds.
Context {R : realType}.

(* If X <= e A + B / e for every e > 0, then X <= 2 sqrt (A B). *)
Lemma le_amgm (X A B : R) : 0 <= A -> 0 <= B ->
  (forall e, 0 < e -> X <= e * A + B / e) -> X <= 2 * Num.sqrt (A * B).
Proof.
move=> A0 B0 h.
have [X0|Xp] := leP X 0.
  by apply: le_trans X0 _; rewrite mulr_ge0 ?sqrtr_ge0.
have [Ap|] := ltP 0 A; last first.
  move=> A0'; have A00 : A = 0 by apply/eqP; rewrite eq_le A0' A0.
  exfalso; have e0 : 0 < 2 * (B + 1) / X.
    by rewrite divr_gt0 // mulr_gt0 // ltr_wpDl.
  have := h _ e0; rewrite A00 mulr0 add0r.
  have XB : X != 0 by rewrite gt_eqF.
  have B1 : B + 1 != 0 by rewrite gt_eqF // ltr_wpDl.
  have -> : B / (2 * (B + 1) / X) = X * (B / (2 * (B + 1))) by field.
  have : B / (2 * (B + 1)) <= 2^-1.
    by rewrite ler_pdivrMr ?mulr_gt0 ?ltr_wpDl //; lra.
  move=> hB hX; have := ler_wpM2l (ltW Xp) hB; lra.
have [Bp|] := ltP 0 B; last first.
  move=> B0'; have B00 : B = 0 by apply/eqP; rewrite eq_le B0' B0.
  exfalso; have e0 : 0 < X / (2 * A) by rewrite divr_gt0 // mulr_gt0.
  have := h _ e0; rewrite B00 mul0r addr0.
  have AB : A != 0 by rewrite gt_eqF.
  have -> : X / (2 * A) * A = X / 2 by field.
  lra.
have sA : 0 < Num.sqrt A by rewrite sqrtr_gt0.
have sB : 0 < Num.sqrt B by rewrite sqrtr_gt0.
have := h (Num.sqrt B / Num.sqrt A) (divr_gt0 sB sA).
rewrite sqrtrM ?(ltW Ap) //.
have hA : A = Num.sqrt A ^+ 2 by rewrite sqr_sqrtr // ltW.
have hB : B = Num.sqrt B ^+ 2 by rewrite sqr_sqrtr // ltW.
move: (Num.sqrt A) (Num.sqrt B) sA sB hA hB => a b a0 b0 hA hB.
rewrite [in X in X -> _]hA [in X in X -> _]hB.
have a0' : a != 0 by rewrite gt_eqF.
have b0' : b != 0 by rewrite gt_eqF.
by have -> : b / a * a ^+ 2 + b ^+ 2 / (b / a) = 2 * (a * b) by field.
Qed.

(* The difference of two inverses. *)
Lemma inv_diff_le (a b c : R) : 0 < c -> c <= a -> c <= b ->
  `|a^-1 - b^-1| <= `|a - b| / c ^+ 2.
Proof.
move=> c0 ca cb.
have a0 : 0 < a := lt_le_trans c0 ca.
have b0 : 0 < b := lt_le_trans c0 cb.
have -> : a^-1 - b^-1 = (b - a) / (a * b).
  have a0' : a != 0 by rewrite gt_eqF.
  have b0' : b != 0 by rewrite gt_eqF.
  by field.
have ab0 : 0 <= (a * b)^-1 by rewrite invr_ge0 mulr_ge0 // ltW.
rewrite normrM (ger0_norm ab0) distrC.
apply: ler_wpM2l; first exact: normr_ge0.
rewrite lef_pV2 ?posrE ?mulr_gt0 ?exprn_gt0 //.
by rewrite expr2 ler_pM // ltW.
Qed.

(* A product bounded by squares, with a free weight. *)
Lemma le_weighted_sqr (x y e : R) : 0 < e ->
  x * y <= (e * x ^+ 2 + y ^+ 2 / e) / 2.
Proof.
move=> e0; rewrite -subr_ge0.
have e0' : e != 0 by rewrite gt_eqF.
have -> : (e * x ^+ 2 + y ^+ 2 / e) / 2 - x * y = (e * x - y) ^+ 2 / (2 * e).
  by field.
by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // ltW.
Qed.

End real_bounds.

Section insertion_compare.
Context {R : realType} {N : nat}.
Variables (K tau : R) (Sigma : 'M[R]_N) (mu nu : probability 'rV[R]_N R).
Hypotheses (rmu : regular_feature K tau Sigma mu)
  (rnu : regular_feature K tau Sigma nu) (tau0 : 0 <= tau).
Variables (n k : nat) (beta gamma : R).
Hypotheses (n0 : (0 < n)%N) (b0 : 0 < beta) (g0 : 0 < gamma).
Variables (f : 'rV[R]_N -> R) (thm v : 'rV[R]_N) (bm c0 : R) (T : 'M[R]_N).
Hypothesis mf : measurable_fun setT f.
Hypothesis fb : forall z, 0 <= f z <= (bm - mxdot z thm) ^+ 2 / (2 * n%:R).
Hypothesis l0 : forall z, 0 <= c0 - 2 * mxdot z v + mxdot z (z *m T).
Hypothesis fq : forall z,
  `|f z - (bm - mxdot z thm) ^+ 2 /
     (2 * (n%:R + (c0 - 2 * mxdot z v + mxdot z (z *m T))))| <=
  (2 + 3 * (bm - mxdot z thm) ^+ 4) / (n%:R * Num.sqrt (n%:R * gamma)).
Hypotheses (Tsym : T \is symmetricmx)
  (Tf : frobenius T ^+ 2 <= k%:R / (4 * beta ^+ 2 * opnorm Sigma ^+ 2))
  (vv : mxdot v v <= k%:R / (4 * beta ^+ 2 * opnorm Sigma)).

Local Notation lambda := (opnorm Sigma).
Local Notation S := (opnorm Sigma * mxdot thm thm + bm ^+ 2).
Local Notation rho := (Num.sqrt k%:R * (tau / opnorm Sigma + 1) / beta).

(* Proposition 2.16: the variance of l(z) is at most 2 rho^2. *)
Lemma ins_l_var (rr : probability 'rV[R]_N R) :
  regular_feature K tau Sigma rr ->
  \int[rr]_z ((c0 - 2 * mxdot z v + mxdot z (z *m T) -
     \int[rr]_y (c0 - 2 * mxdot y v + mxdot y (y *m T))) ^+ 2) <=
  2 * rho ^+ 2.
Proof.
move=> reg; apply: le_trans (reg_ell_var reg c0 v Tsym) _.
have lam0 := reg_lambda_gt0 rmu.
have h1 : 2 * tau ^+ 2 * frobenius T ^+ 2 <=
    2 * tau ^+ 2 * (k%:R / (4 * beta ^+ 2 * lambda ^+ 2)).
  by rewrite ler_wpM2l // mulr_ge0 // sqr_ge0.
have h2 : 8 * lambda * mxdot v v <=
    8 * lambda * (k%:R / (4 * beta ^+ 2 * lambda)).
  by rewrite ler_wpM2l // mulr_ge0 // ltW.
apply: le_trans (lerD h1 h2) _.
have -> : rho ^+ 2 = k%:R * (tau / lambda + 1) ^+ 2 / beta ^+ 2.
  by rewrite !exprMn sqr_sqrtr ?ler0n // exprVn.
rewrite -subr_ge0.
have l0' : lambda != 0 by rewrite gt_eqF.
have b0' : beta != 0 by rewrite gt_eqF.
have -> : 2 * (k%:R * (tau / lambda + 1) ^+ 2 / beta ^+ 2) -
    (2 * tau ^+ 2 * (k%:R / (4 * beta ^+ 2 * lambda ^+ 2)) +
     8 * lambda * (k%:R / (4 * beta ^+ 2 * lambda))) =
    k%:R / beta ^+ 2 * (3 / 2 * (tau / lambda) ^+ 2 + 4 * (tau / lambda)).
  by field.
have t0 : 0 <= tau / lambda by rewrite divr_ge0 // ltW.
apply: mulr_ge0; first by rewrite divr_ge0 ?ler0n ?sqr_ge0.
by apply: addr_ge0; apply: mulr_ge0 => //; rewrite ?sqr_ge0 // divr_ge0.
Qed.

(* Propositions 2.14 and 2.16: the comparison of the insertion costs. *)
Lemma insertion_compare :
  `|\int[mu]_z f z - \int[nu]_z f z| <=
  (4 + 48 * (1 + K ^+ 4) * S ^+ 2) / (n%:R * Num.sqrt (n%:R * gamma)) +
  4 * Num.sqrt (1 + K ^+ 4) * rho * S / n%:R ^+ 2.
Proof.
set kap := 1 + K ^+ 4.
set nn := (n%:R : R).
set sq := Num.sqrt (nn * gamma).
have nn0 : 0 < nn by rewrite ltr0n.
have sq0 : 0 < sq by rewrite sqrtr_gt0 mulr_gt0.
have lam0 := reg_lambda_gt0 rmu.
have kap0 : 0 <= kap by rewrite addr_ge0 // exprn_even_ge0.
have S0 : 0 <= S by rewrite addr_ge0 ?sqr_ge0 // mulr_ge0 ?mxdot_ge0 // ltW.
have rho0 : 0 <= rho.
  by rewrite divr_ge0 ?mulr_ge0 ?sqrtr_ge0 ?addr_ge0 ?divr_ge0 // ltW.
set lb := \int[mu]_z (c0 - 2 * mxdot z v + mxdot z (z *m T)).
have lbnu : \int[nu]_z (c0 - 2 * mxdot z v + mxdot z (z *m T)) = lb.
  by rewrite /lb (reg_ell_mean rnu) (reg_ell_mean rmu).
have lb0 : 0 <= lb by apply: Rintegral_ge0 => z _; exact: l0.
pose qb z := (bm - mxdot z thm) ^+ 2 / (2 * (nn + lb)).
(* the bound for one law, with the common mean lb of l *)
have one (rr : probability 'rV[R]_N R) : regular_feature K tau Sigma rr ->
    \int[rr]_z (c0 - 2 * mxdot z v + mxdot z (z *m T)) = lb ->
    `|\int[rr]_z f z - \int[rr]_z qb z| <=
      (2 + 24 * kap * S ^+ 2) / (nn * sq) +
      2 * Num.sqrt kap * rho * S / nn ^+ 2.
  move=> reg lbr.
  have ir2 := reg_int_resid2 reg thm bm.
  have ir4 := reg_int_resid4 reg thm bm.
  have il2 := reg_int_ell2 reg c0 v T lb.
  have iqb : rr.-integrable setT (EFin \o qb) := integrableRZr _ ir2.
  have ifr : rr.-integrable setT (EFin \o f).
    apply: (le_integrable measurableT _ _ (integrableRZr (2 * nn)^-1 ir2)).
      exact/measurable_EFinP.
    move=> z _; rewrite /= lee_fin.
    have /andP[f0 f1] := fb z.
    by rewrite (ger0_norm f0); apply: le_trans f1 (ler_norm _).
  have ifq := integrableRB ifr iqb.
  rewrite -(RintegralB measurableT ifr iqb).
  apply: le_trans (le_normr_Rintegral measurableT ifq) _.
  set X := \int[rr]_z `|f z - qb z|.
  set R4 := \int[rr]_z ((bm - mxdot z thm) ^+ 4).
  set Vl := \int[rr]_z ((c0 - 2 * mxdot z v + mxdot z (z *m T) - lb) ^+ 2).
  have R4b : R4 <= 8 * kap * S ^+ 2 := reg_resid4 reg thm bm.
  have Vlb : Vl <= 2 * rho ^+ 2 by have := ins_l_var reg; rewrite lbr.
  have R40 : 0 <= R4 by apply: Rintegral_ge0 => z _; rewrite exprn_even_ge0.
  have Vl0 : 0 <= Vl by apply: Rintegral_ge0 => z _; rewrite sqr_ge0.
  (* the pointwise bound, for a weight e > 0 *)
  have pw (e : R) (z : 'rV[R]_N) : 0 < e ->
      `|f z - qb z| <= (2 + 3 * (bm - mxdot z thm) ^+ 4) / (nn * sq) +
        (e * (bm - mxdot z thm) ^+ 4 +
         (c0 - 2 * mxdot z v + mxdot z (z *m T) - lb) ^+ 2 / e) /
        (4 * nn ^+ 2).
    move=> e0.
    set r2 := (bm - mxdot z thm) ^+ 2.
    set lz := c0 - 2 * mxdot z v + mxdot z (z *m T).
    have lz0 : 0 <= lz := l0 z.
    have r4 : (bm - mxdot z thm) ^+ 4 = r2 ^+ 2 by rewrite /r2 -exprM.
    rewrite r4.
    apply: le_trans (ler_distD (r2 / (2 * (nn + lz))) _ _) _.
    apply: lerD; first by have := fq z; rewrite -/r2 -/lz r4.
    rewrite /qb -/r2.
    have -> : r2 / (2 * (nn + lz)) - r2 / (2 * (nn + lb)) =
        r2 / 2 * ((nn + lz)^-1 - (nn + lb)^-1).
      by rewrite !invfM; ring.
    have r20 : 0 <= r2 / 2 by rewrite divr_ge0 ?sqr_ge0.
    rewrite normrM (ger0_norm r20).
    apply: le_trans (ler_wpM2l r20 (inv_diff_le nn0 _ _)) _.
    - by rewrite lerDl.
    - by rewrite lerDl.
    have -> : nn + lz - (nn + lb) = lz - lb by ring.
    have w := le_weighted_sqr r2 `|lz - lb| e0.
    rewrite real_normK ?num_real // in w.
    have nn2 : 0 < 4 * nn ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
    have nn0' : nn != 0 by rewrite gt_eqF.
    have -> : r2 / 2 * (`|lz - lb| / nn ^+ 2) =
        r2 * `|lz - lb| / (2 * nn ^+ 2) by field.
    have nn20 : 0 < 2 * nn ^+ 2 by rewrite mulr_gt0 // exprn_gt0.
    rewrite ler_pdivrMr //.
    have -> : (e * r2 ^+ 2 + (lz - lb) ^+ 2 / e) / (4 * nn ^+ 2) *
        (2 * nn ^+ 2) = (e * r2 ^+ 2 + (lz - lb) ^+ 2 / e) / 2.
      have e0' : e != 0 by rewrite gt_eqF.
      by field.
    exact: w.
  have c10 : 0 < (nn * sq)^-1 by rewrite invr_gt0 mulr_gt0.
  have c20 : 0 < (4 * nn ^+ 2)^-1 by rewrite invr_gt0 mulr_gt0 // exprn_gt0.
  (* integrating the pointwise bound *)
  have key (e : R) : 0 < e ->
      X - (2 + 3 * R4) / (nn * sq) <=
      e * (R4 / (4 * nn ^+ 2)) + Vl / (4 * nn ^+ 2) / e.
    move=> e0.
    have iA : rr.-integrable setT
        (EFin \o (fun z => 2 + 3 * (bm - mxdot z thm) ^+ 4)).
      exact: integrableRD (integrable_cst_prob rr 2) (integrableRZl 3 ir4).
    have iB : rr.-integrable setT (EFin \o (fun z =>
        e * (bm - mxdot z thm) ^+ 4 +
        (c0 - 2 * mxdot z v + mxdot z (z *m T) - lb) ^+ 2 / e)).
      exact: integrableRD (integrableRZl e ir4) (integrableRZr e^-1 il2).
    have iAc := integrableRZr (nn * sq)^-1 iA.
    have iBc := integrableRZr (4 * nn ^+ 2)^-1 iB.
    have ig := integrableRD iAc iBc.
    have := le_Rintegral measurableT (integrable_norm ifq) ig
      (fun z _ => pw e z e0).
    rewrite -/X (RintegralD measurableT iAc iBc).
    rewrite (RintegralZr _ measurableT iA) (RintegralZr _ measurableT iB).
    rewrite (RintegralD measurableT (integrable_cst_prob rr 2)
      (integrableRZl 3 ir4)).
    rewrite (RintegralD measurableT (integrableRZl e ir4)
      (integrableRZr e^-1 il2)).
    rewrite Rintegral_cst_prob (RintegralZl _ measurableT ir4).
    rewrite (RintegralZl _ measurableT ir4) (RintegralZr _ measurableT il2).
    rewrite -/R4 -/Vl.
    have e0' : e != 0 by rewrite gt_eqF.
    have nn0' : nn != 0 by rewrite gt_eqF.
    have sq0' : sq != 0 by rewrite gt_eqF.
    move=> h; rewrite lerBlDl; apply: le_trans h _.
    by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
  (* the infimum over e *)
  have A0 : 0 <= R4 / (4 * nn ^+ 2).
    by rewrite divr_ge0 // ltW // mulr_gt0 // exprn_gt0.
  have B0 : 0 <= Vl / (4 * nn ^+ 2).
    by rewrite divr_ge0 // ltW // mulr_gt0 // exprn_gt0.
  have := le_amgm A0 B0 key.
  have sqb : Num.sqrt (R4 / (4 * nn ^+ 2) * (Vl / (4 * nn ^+ 2))) <=
      Num.sqrt kap * rho * S / nn ^+ 2.
    have nn0' : nn != 0 by rewrite gt_eqF.
    apply: le_trans (_ : Num.sqrt ((S * rho / nn ^+ 2) ^+ 2 * kap) <= _).
      apply: ler_wsqrtr.
      have -> : (S * rho / nn ^+ 2) ^+ 2 * kap =
          8 * kap * S ^+ 2 / (4 * nn ^+ 2) * (2 * rho ^+ 2 / (4 * nn ^+ 2)).
        have l0' : lambda != 0 by rewrite gt_eqF.
        have b0' : beta != 0 by rewrite gt_eqF.
        by field.
      have c4 : 0 <= (4 * nn ^+ 2)^-1 by rewrite ltW.
      apply: ler_pM; [exact: A0 | exact: B0 | |].
        by apply: ler_wpM2r.
      by apply: ler_wpM2r.
    rewrite sqrtrM ?sqr_ge0 // sqrtr_sqr ger0_norm; last first.
      by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
    by apply: divr_ge0; [exact: mulr_ge0 | exact: sqr_ge0].
  move=> h; rewrite lerBlDl in h; apply: le_trans h _.
  have R4b' : 3 * R4 <= 24 * kap * S ^+ 2 by lra.
  apply: lerD.
    by apply: ler_wpM2r; [exact: ltW | lra].
  have := ler_wpM2l (ler0n R 2) sqb.
  by rewrite !mulrA.
(* the quadratic approximation has the same mean for both laws *)
have qbE : \int[mu]_z qb z = \int[nu]_z qb z.
  rewrite /qb (RintegralZr _ measurableT (reg_int_resid2 rmu thm bm)).
  rewrite (RintegralZr _ measurableT (reg_int_resid2 rnu thm bm)).
  by rewrite (reg_resid2 rmu) (reg_resid2 rnu).
have h1 := one mu rmu erefl.
have h2 := one nu rnu lbnu.
rewrite distrC in h2.
apply: le_trans (ler_distD (\int[mu]_z qb z) _ _) _.
rewrite qbE in h1.
rewrite qbE.
apply: le_trans (lerD h1 h2) _.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; ring.
Qed.

End insertion_compare.

Section reference_scale.
Context {R : realType} {N : nat}.

(* The reference scale of the paper, (2.11). *)
Definition ls_ref_scale (lambda beta gamma : R) (D : set 'rV[R]_N)
    (B : 'rV[R]_N -> R) : R :=
  (1 + beta^-1) * (1 + inf [set lambda * mxdot th th + gamma * B th | th in D]).

End reference_scale.

Section barrier_lindeberg.
Context {R : realType} {N : nat}.
Variables (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N) (B : 'rV[R]_N -> R).
Hypotheses (DV : rel_open_convex V D) (scB : sc_function V D B).
Hypotheses (B0 : forall z, D z -> 0 <= B z) (D0 : D !=set0).
Variables (K tau : R) (Sigma : 'M[R]_N) (mu nu : probability 'rV[R]_N R).
Hypotheses (rmu : regular_feature K tau Sigma mu)
  (rnu : regular_feature K tau Sigma nu) (tau0 : 0 <= tau).
Variables (n : nat) (beta gamma : R).
Hypotheses (n0 : (0 < n)%N) (b0 : 0 < beta) (g0 : 0 < gamma).

Local Notation lambda := (opnorm Sigma).
Local Notation Phi Z := (ls_barrier_value Z (opnorm Sigma) beta D gamma B).
Local Notation s := ((n%:R *+ 2)^-1 : R).
Local Notation Sbar thr i x :=
  ((s * \sum_(j < n | j != i) mxdot (tnth x j) thr ^+ 2 +
    beta * opnorm Sigma * mxdot thr thr + gamma * B thr) / beta).
Local Notation bnd Sb :=
  ((4 + 48 * (1 + K ^+ 4) * Sb ^+ 2) / (n%:R * Num.sqrt (n%:R * gamma)) +
   4 * Num.sqrt (1 + K ^+ 4) *
     (Num.sqrt (\dim V)%:R * (tau / opnorm Sigma + 1) / beta) * Sb /
   n%:R ^+ 2).

(* The comparison in the coordinate i, the other coordinates being fixed. *)
Lemma loo_compare (thr : 'rV[R]_N) (i : 'I_n) (x : n.-tuple 'rV[R]_N) :
  D thr -> 36 <= n%:R * gamma ->
  `|\int[mu]_t Phi (tuple_set x i t) - \int[nu]_t Phi (tuple_set x i t)| <=
  bnd (Sbar thr i x).
Proof.
move=> Dthr n36.
have lam0 := reg_lambda_gt0 rmu.
have s0 : 0 <= s by rewrite invr_ge0 mulrn_wge0 // ler0n.
(* the leave-one-out minimizer, an orthonormal basis of V and the Hessian *)
have [thm [bm [Dthm thmin]]] :=
  ls_barrier_minimizer x (fun j => j != i) DV scB B0 s0 lam0 b0 g0 D0.
have [E [EE EV]] := vspace_orthonormal V.
have [_ rep _ _ _] := scB.
have [g [M0 hM0]] := rep thm Dthm.
pose M := 2^-1 *: (M0 + M0^T).
have Msym : M \is symmetricmx.
  by apply/symmetricmxP; rewrite /M linearZ /= linearD /= trmxK addrC.
have HM h : h \in V -> 'D_h ('D_h B) thm = mxdot h (h *m M).
  move=> hV; have [_ ->] := hM0 h hV.
  rewrite /M -scalemxAr mulmxDr mxdotZr mxdotDr.
  have -> : mxdot h (h *m M0^T) = mxdot h (h *m M0).
    by rewrite -mxdot_mulmxr mxdotC.
  by field.
have Bc z (Dz : D z) (e : R) (e0 : 0 < e) :=
  sc_function_continuous DV scB Dz e0.
have mPhi := measurable_ls_barrier_value DV D0 B0 Bc (n := n)
  (ltW lam0) (ltW b0) (ltW g0).
(* the insertion cost and the coefficients of l *)
set Fv := ls_barrier_objective x (fun j => j != i) s lambda beta gamma B thm bm.
pose f z := ins_cost D B x i lambda beta gamma thm bm z.
have PhiE t : Phi (tuple_set x i t) = f t + Fv by rewrite /f /ins_cost subrK.
have mf : measurable_fun setT f.
  rewrite /f /ins_cost; apply: measurable_funB; last exact: measurable_cst.
  exact: measurableT_comp mPhi (measurable_tuple_set x i).
set c0 := ins_c0 x i lambda beta gamma E M.
set v := ins_v x i lambda beta gamma E M.
set T := ins_T x i lambda beta gamma E M.
have ellE z : ins_ell x i lambda beta gamma M E z =
    c0 - 2 * mxdot z v + mxdot z (z *m T).
  by rewrite (ins_ell_quadratic scB x i lam0 b0 g0 EE EV Dthm Msym HM z) mxdotC.
have fb z : 0 <= f z <= (bm - mxdot z thm) ^+ 2 / (2 * n%:R).
  exact: (ins_cost_bounds Dthm thmin z).
have l0 z : 0 <= c0 - 2 * mxdot z v + mxdot z (z *m T).
  rewrite -ellE.
  exact: (ins_ell_ge0 scB x i lam0 b0 g0 EE EV Dthm Msym HM z).
have fq z : `|f z - (bm - mxdot z thm) ^+ 2 /
    (2 * (n%:R + (c0 - 2 * mxdot z v + mxdot z (z *m T))))| <=
    (2 + 3 * (bm - mxdot z thm) ^+ 4) / (n%:R * Num.sqrt (n%:R * gamma)).
  rewrite -ellE.
  exact: (ins_cost_quadratic DV scB lam0 b0 g0 EE EV Dthm thmin Msym HM z n36).
have Tsym := ins_T_sym scB x i lam0 b0 g0 EE EV Dthm Msym HM.
have Tf : frobenius T ^+ 2 <= (\dim V)%:R / (4 * beta ^+ 2 * lambda ^+ 2).
  rewrite frobenius_sqr.
  exact: (ins_T_frobenius scB x i lam0 b0 g0 EE EV Dthm Msym HM).
have vv := ins_v_bound scB x i lam0 b0 g0 EE EV Dthm Msym HM.
have := insertion_compare rmu rnu tau0 n0 b0 g0 mf fb l0 fq Tsym Tf vv.
(* the integrals of the value and of the insertion cost *)
have ifr (rr : probability 'rV[R]_N R) : regular_feature K tau Sigma rr ->
    rr.-integrable setT (EFin \o f).
  move=> reg.
  apply: (le_integrable measurableT _ _
    (integrableRZr (2 * n%:R)^-1 (reg_int_resid2 reg thm bm))).
    exact/measurable_EFinP.
  move=> z _; rewrite /= lee_fin.
  have /andP[f0 f1] := fb z.
  by rewrite (ger0_norm f0); apply: le_trans f1 (ler_norm _).
have intE (rr : probability 'rV[R]_N R) : regular_feature K tau Sigma rr ->
    \int[rr]_t Phi (tuple_set x i t) = \int[rr]_t f t + Fv.
  move=> reg; under eq_Rintegral do rewrite PhiE.
  rewrite (RintegralD measurableT (ifr rr reg) (integrable_cst_prob rr Fv)).
  by rewrite Rintegral_cst_prob.
rewrite (intE mu rmu) (intE nu rnu) opprD addrACA subrr addr0.
move=> h; apply: le_trans h _.
(* the size of the minimizer is at most Sbar *)
have S0 : 0 <= lambda * mxdot thm thm + bm ^+ 2.
  by rewrite addr_ge0 ?sqr_ge0 // mulr_ge0 ?mxdot_ge0 // ltW.
have Sle : lambda * mxdot thm thm + bm ^+ 2 <=
    ((n%:R *+ 2)^-1 * \sum_(j < n | j != i) mxdot (tnth x j) thr ^+ 2 +
      beta * lambda * mxdot thr thr + gamma * B thr) / beta.
  rewrite ler_pdivlMr // [X in X <= _]mulrC.
  exact: (ins_size_le B0 g0 Dthm thmin Dthr).
have kap0 : 0 <= 1 + K ^+ 4 by rewrite addr_ge0 // exprn_even_ge0.
apply: lerD.
  apply: ler_wpM2r; first by rewrite invr_ge0 mulr_ge0 ?ler0n ?sqrtr_ge0.
  rewrite lerD2l; apply: ler_wpM2l; first by rewrite mulr_ge0.
  by rewrite ler_sqr ?nnegrE // (le_trans S0 Sle).
apply: ler_wpM2r; first by rewrite invr_ge0 exprn_ge0 ?ler0n.
apply: ler_wpM2l => //.
apply: mulr_ge0; first by rewrite mulr_ge0 ?sqrtr_ge0.
apply: divr_ge0; last exact: ltW.
by rewrite mulr_ge0 ?sqrtr_ge0 // addr_ge0 // divr_ge0 // ltW.
Qed.

Let objective_ge0 (Z : n.-tuple 'rV[R]_N) th b :
  0 <= ls_objective Z lambda beta th b.
Proof.
rewrite /ls_objective; apply: addr_ge0.
  rewrite mulr_ge0 ?invr_ge0 ?mulrn_wge0 ?ler0n //.
  by rewrite sumr_ge0 // => j _; rewrite sqr_ge0.
by rewrite mulr_ge0 ?addr_ge0 ?sqr_ge0 ?mulr_ge0 ?mxdot_ge0 ?opnorm_ge0 // ltW.
Qed.

Lemma Phi_ge0 (Z : n.-tuple 'rV[R]_N) : 0 <= Phi Z.
Proof.
rewrite /ls_barrier_value; apply: lb_le_inf.
  have [th Dth] := D0.
  exists (ls_objective Z lambda beta th 0 + gamma * B th), th => //.
  by exists 0.
move=> _ [th Dth [b _ <-]].
by rewrite addr_ge0 ?objective_ge0 // mulr_ge0 ?B0 // ltW.
Qed.

Lemma Phi_le (thr : 'rV[R]_N) (Z : n.-tuple 'rV[R]_N) : D thr ->
  Phi Z <= s * \sum_(j < n) mxdot (tnth Z j) thr ^+ 2 +
    (beta * lambda * mxdot thr thr + gamma * B thr).
Proof.
move=> Dthr; rewrite /ls_barrier_value.
have lb : has_lbound [set ls_objective Z lambda beta th b + gamma * B th |
    th in D & b in [set: R]].
  exists 0 => _ [th Dth [b _ <-]].
  by rewrite addr_ge0 ?objective_ge0 // mulr_ge0 ?B0 // ltW.
apply: le_trans (ge_inf lb _) _; first by exists thr => //; exists 0.
rewrite /ls_objective.
under eq_bigr do rewrite sub0r sqrrN.
by rewrite expr0n /= addr0 mulrA addrA.
Qed.

Lemma Phi_meas : measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => Phi Z).
Proof.
have Bc z (Dz : D z) (e : R) (e0 : 0 < e) :=
  sc_function_continuous DV scB Dz e0.
exact: (measurable_ls_barrier_value DV D0 B0 Bc (n := n) (opnorm_ge0 _)
  (ltW b0) (ltW g0)).
Qed.

Lemma hybrid_regular k j : regular_feature K tau Sigma (hybrid mu nu k j).
Proof. by rewrite /hybrid; case: ifP. Qed.

Lemma int_Phi (rho : nat -> probability 'rV[R]_N R) :
  (forall j, regular_feature K tau Sigma (rho j)) ->
  (tuple_prod rho n).-integrable setT (EFin \o (fun Z => Phi Z)).
Proof.
move=> hr; have [thr Dthr] := D0.
have iS : (tuple_prod rho n).-integrable setT
    (EFin \o (fun x => \sum_(j < n) mxdot (tnth x j) thr ^+ 2)).
  apply: integrableR_sum => j.
  exact: (@integrable_tuple_prod_tnth _ _ _ rho n j
    (fun z => mxdot z thr ^+ 2) (reg_int_sqr (hr j) thr)).
have iB := integrableRD (integrableRZl s iS)
  (integrable_cst_prob _ (beta * lambda * mxdot thr thr + gamma * B thr)).
apply: (le_integrable measurableT _ _ iB).
  by apply/measurable_EFinP; exact: Phi_meas.
move=> Z _; rewrite /= lee_fin ger0_norm ?Phi_ge0 //.
exact: le_trans (Phi_le Z Dthr) (ler_norm _).
Qed.

Lemma int_Phi_set (rr : probability 'rV[R]_N R) (i : 'I_n)
    (x : n.-tuple 'rV[R]_N) :
  regular_feature K tau Sigma rr ->
  rr.-integrable setT (fun t => (Phi (tuple_set x i t))%:E).
Proof.
move=> reg; have [thr Dthr] := D0.
set A := \sum_(j < n) mxdot (tnth x j) thr ^+ 2.
set C := beta * lambda * mxdot thr thr + gamma * B thr.
have iB : rr.-integrable setT
    (EFin \o (fun t => s * (A + mxdot t thr ^+ 2) + C)).
  apply: integrableRD; last exact: integrable_cst_prob.
  apply: integrableRZl; apply: integrableRD; first exact: integrable_cst_prob.
  exact: (reg_int_sqr reg thr).
apply: (le_integrable measurableT _ _ iB).
  apply/measurable_EFinP.
  exact: measurableT_comp Phi_meas (measurable_tuple_set x i).
move=> t _; rewrite /= lee_fin ger0_norm ?Phi_ge0 //.
apply: le_trans (Phi_le _ Dthr) (le_trans _ (ler_norm _)).
rewrite lerD2r; apply: ler_wpM2l; first by rewrite invr_ge0 mulrn_wge0 ?ler0n.
rewrite [leLHS](bigD1 i) //= tnth_tuple_set /A [X in _ <= X + _](bigD1 i) //=.
have -> : \sum_(i0 < n | i0 != i) mxdot (tnth (tuple_set x i t) i0) thr ^+ 2 =
    \sum_(i0 < n | i0 != i) mxdot (tnth x i0) thr ^+ 2.
  by apply: eq_bigr => j ji; rewrite tnth_tuple_set_neq.
by have := sqr_ge0 (mxdot (tnth x i) thr); lra.
Qed.

Local Notation Lref := (ls_ref_scale (opnorm Sigma) beta gamma D B).

(* A reference point at which lambda |theta|^2 + gamma B theta is at most
   one more than its infimum. *)
Lemma ref_point : exists2 thr, D thr &
  [/\ 0 <= inf [set lambda * mxdot th th + gamma * B th | th in D],
      lambda * mxdot thr thr + gamma * B thr <=
        1 + inf [set lambda * mxdot th th + gamma * B th | th in D] &
      1 + beta^-1 <= Lref].
Proof.
set S := [set _ | _ in _].
have v0 th : D th -> 0 <= lambda * mxdot th th + gamma * B th.
  by move=> Dth; rewrite addr_ge0 ?mulr_ge0 ?mxdot_ge0 ?opnorm_ge0 ?B0 // ltW.
have Sn : S !=set0.
  by have [th Dth] := D0; exists (lambda * mxdot th th + gamma * B th), th.
have Slb : has_lbound S by exists 0 => _ [th Dth <-]; exact: v0.
have I0 : 0 <= inf S by apply: lb_le_inf Sn _ => _ [th Dth <-]; exact: v0.
have [_ [th Dth <-] h] := inf_adherent ltr01 (conj Sn Slb).
exists th => //; split => //; first by rewrite [1 + _]addrC ltW.
rewrite /ls_ref_scale -/S -[leLHS]mulr1 ler_wpM2l ?lerDl //.
by rewrite addr_ge0 // invr_ge0 ltW.
Qed.

(* (Sum_(j in P) a_j)^2 <= n sum_j a_j^2. *)
Lemma sum_pred_sqr_le (P : pred 'I_n) (a : 'I_n -> R) :
  (forall j, 0 <= a j) ->
  (\sum_(j < n | P j) a j) ^+ 2 <= n%:R * \sum_(j < n) a j ^+ 2.
Proof.
move=> a0; rewrite big_mkcond /=.
have := sum_cauchy_schwarz (fun j => if P j then a j else 0) (fun=> 1).
have e1 : \sum_(i < n) (if P i then a i else 0) * 1 =
    \sum_(i < n) (if P i then a i else 0).
  by apply: eq_bigr => j _; rewrite mulr1.
have e2 : \sum_(i < n) (1 * 1 : R) = n%:R.
  by under eq_bigr do rewrite mulr1; rewrite sumr_const card_ord.
rewrite e1 e2 => h; apply: le_trans h _.
rewrite mulrC ler_wpM2l ?ler0n //; apply: ler_sum => j _.
by case: (P j); rewrite ?mul0r ?sqr_ge0 // expr2.
Qed.

(* Theorem 2.9, (2.12). *)
Theorem barrier_lindeberg_mean : 36 <= n%:R * gamma ->
  `|\int[tuple_prod (fun=> mu) n]_Z Phi Z -
    \int[tuple_prod (fun=> nu) n]_Z Phi Z| <=
  100 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 *
  ((Num.sqrt (n%:R * gamma))^-1 +
   Num.sqrt (\dim V)%:R * (tau / opnorm Sigma + 1) / n%:R).
Proof.
move=> n36.
have [thr Dthr [I0 Jle Lb]] := ref_point.
move: I0 Jle Lb; set I := inf _ => I0 Jle Lb.
set kap := 1 + K ^+ 4.
set nn := (n%:R : R).
set sq := Num.sqrt (nn * gamma).
set rk := Num.sqrt (\dim V)%:R * (tau / lambda + 1).
set C0 := beta * lambda * mxdot thr thr + gamma * B thr.
have nn0 : 0 < nn by rewrite ltr0n.
have sq0 : 0 < sq by rewrite sqrtr_gt0 mulr_gt0.
have lam0 := reg_lambda_gt0 rmu.
have kap1 : 1 <= kap by rewrite lerDl exprn_even_ge0.
have rk0 : 0 <= rk.
  by rewrite mulr_ge0 ?sqrtr_ge0 // addr_ge0 // divr_ge0 // ltW.
set c1 := 4 / (nn * sq).
set c2 := 48 * kap / (nn * sq).
set c3 := 4 * Num.sqrt kap * rk / nn ^+ 2.
have c20 : 0 <= c2 by rewrite divr_ge0 ?mulr_ge0 ?(le_trans ler01 kap1) // ltW.
have c30 : 0 <= c3.
  apply: divr_ge0; last by rewrite exprn_ge0 // ltW.
  by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: sqrtr_ge0.
set A0 := c1 + c3 / (2 * beta ^+ 2) +
  (c2 + c3 / 2) * (2 * C0 ^+ 2 / beta ^+ 2).
set B1 := (c2 + c3 / 2) * (2 * s ^+ 2 * nn / beta ^+ 2).
pose P4 (x : n.-tuple 'rV[R]_N) := \sum_(j < n) mxdot (tnth x j) thr ^+ 4.
pose b (i : 'I_n) (x : n.-tuple 'rV[R]_N) := A0 + B1 * P4 x.
(* the bound in the coordinate i is a polynomial in the fourth moments *)
have hb (i : 'I_n) (x : n.-tuple 'rV[R]_N) :
    `|\int[mu]_t Phi (tuple_set x i t) - \int[nu]_t Phi (tuple_set x i t)| <=
    b i x.
  apply: le_trans (loo_compare i x Dthr n36) _.
  set Y := \sum_(j < n | j != i) mxdot (tnth x j) thr ^+ 2.
  have Y0 : 0 <= Y by rewrite sumr_ge0 // => j _; rewrite sqr_ge0.
  have YP : Y ^+ 2 <= nn * P4 x.
    apply: le_trans (sum_pred_sqr_le _
      (fun j => sqr_ge0 (mxdot (tnth x j) thr))) _.
    by rewrite /P4; under eq_bigr do rewrite -exprM.
  set Sb := (_ * Y + _ + _) / beta.
  have SbE : Sb = (s * Y + C0) / beta by rewrite /Sb /C0 addrA.
  apply: le_trans (_ : _ <= c1 + c2 * Sb ^+ 2 + c3 * (Sb / beta)) _.
    rewrite le_eqVlt; apply/orP; left; apply/eqP.
    by rewrite /c1 /c2 /c3 /rk /kap /sq /nn; ring.
  have am : Sb / beta <= Sb ^+ 2 / 2 + 1 / (2 * beta ^+ 2).
    rewrite -subr_ge0.
    have b0' : beta != 0 by rewrite gt_eqF.
    have -> : Sb ^+ 2 / 2 + 1 / (2 * beta ^+ 2) - Sb / beta =
        (Sb - beta^-1) ^+ 2 / 2 by field.
    by rewrite divr_ge0 ?sqr_ge0.
  have Sb2 : Sb ^+ 2 <= (2 * s ^+ 2 * nn * P4 x + 2 * C0 ^+ 2) / beta ^+ 2.
    rewrite SbE expr_div_n ler_pM2r ?invr_gt0 ?exprn_gt0 //.
    have h1 := sqr_ge0 (s * Y - C0).
    have h2 : s ^+ 2 * Y ^+ 2 <= s ^+ 2 * (nn * P4 x).
      by rewrite ler_wpM2l ?sqr_ge0.
    by nra.
  have c23 : 0 <= c2 + c3 / 2 by rewrite addr_ge0 // divr_ge0.
  apply: le_trans
    (_ : _ <= c1 + c3 / (2 * beta ^+ 2) + (c2 + c3 / 2) * Sb ^+ 2) _.
    have h := ler_wpM2l c30 am.
    apply: le_trans (lerD (lexx (c1 + c2 * Sb ^+ 2)) h) _.
    rewrite le_eqVlt; apply/orP; left; apply/eqP.
    by rewrite /c1 /c2 /c3 /rk /kap /sq /nn; ring.
  apply: le_trans (lerD (lexx _) (ler_wpM2l c23 Sb2)) _.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by rewrite /b /A0 /B1 /c1 /c2 /c3 /rk /kap /sq /nn; ring.
(* the Lindeberg telescoping *)
have mP4 : measurable_fun setT P4.
  rewrite /P4; apply: measurable_sum => j; apply: measurable_funX.
  exact: measurable_mxdot_tnth.
have mb (i : 'I_n) : measurable_fun setT (b i).
  apply: measurable_funD; first exact: measurable_cst.
  by apply: measurable_funM; [exact: measurable_cst | exact: mP4].
have iP4 (rho : nat -> probability 'rV[R]_N R) :
    (forall j, regular_feature K tau Sigma (rho j)) ->
    (tuple_prod rho n).-integrable setT (EFin \o P4).
  move=> hr; apply: integrableR_sum => j.
  exact: (@integrable_tuple_prod_tnth _ _ _ rho n j
    (fun z => mxdot z thr ^+ 4) (reg_int4 (hr j) thr)).
have bi (i : 'I_n) :
    (tuple_prod (hybrid mu nu i) n).-integrable setT (EFin \o b i).
  apply: integrableRD; first exact: integrable_cst_prob.
  exact: integrableRZl (iP4 _ (hybrid_regular i)).
have Fi (k : nat) : (k <= n)%N ->
    (tuple_prod (hybrid mu nu k) n).-integrable setT
      (EFin \o (fun Z => Phi Z)).
  by move=> _; exact: int_Phi (hybrid_regular k).
have Fx (i : 'I_n) x :
    mu.-integrable setT (fun t => (Phi (tuple_set x i t))%:E) /\
    nu.-integrable setT (fun t => (Phi (tuple_set x i t))%:E).
  by split; apply: int_Phi_set.
have := lindeberg_telescope Phi_meas Phi_ge0 Fi Fx mb bi hb.
move=> h; apply: le_trans h _.
(* the hybrid means of the bound *)
set M4 := K ^+ 4 * lambda ^+ 2 * mxdot thr thr ^+ 2.
have c23 : 0 <= c2 + c3 / 2 by rewrite addr_ge0 // divr_ge0.
have B10 : 0 <= B1.
  apply: mulr_ge0 => //; apply: divr_ge0; last exact: sqr_ge0.
  by rewrite mulr_ge0 ?mulr_ge0 ?sqr_ge0 // ltW.
have Eb (i : 'I_n) :
    \int[tuple_prod (hybrid mu nu i) n]_x b i x <= A0 + B1 * (nn * M4).
  have iP := iP4 _ (hybrid_regular i).
  rewrite /b (RintegralD measurableT (integrable_cst_prob _ A0)
    (integrableRZl B1 iP)).
  rewrite Rintegral_cst_prob (RintegralZl _ measurableT iP) lerD2l.
  apply: ler_wpM2l => //.
  rewrite /P4 (Rintegral_sumr _ (fun j => @integrable_tuple_prod_tnth _ _ _
    (hybrid mu nu i) n j (fun z => mxdot z thr ^+ 4)
    (reg_int4 (hybrid_regular i j) thr))).
  apply: le_trans (_ : \sum_(j < n) M4 <= _); last first.
    by rewrite sumr_const card_ord -mulr_natl.
  apply: ler_sum => j _.
  rewrite (Rintegral_tuple_prod_tnth (hybrid mu nu i) j
    (g := fun z => mxdot z thr ^+ 4)).
  - by apply: measurable_funX; exact: measurable_mxdotl.
  - by move=> t; rewrite exprn_even_ge0.
  - exact: reg_moment4 (hybrid_regular i j) thr.
apply: le_trans (ler_sum _ (fun i _ => Eb i)) _.
rewrite sumr_const card_ord -[X in X <= _]mulr_natl -/nn.
(* the reference scale bounds the remaining quantities *)
have b0' : beta != 0 by rewrite gt_eqF.
have nn0' : nn != 0 by rewrite gt_eqF.
set lt := lambda * mxdot thr thr.
have lt0 : 0 <= lt by rewrite mulr_ge0 ?mxdot_ge0 // ltW.
have BB0 : 0 <= gamma * B thr by rewrite mulr_ge0 ?B0 // ltW.
have LE : Lref = (1 + beta^-1) * (1 + I) by [].
have bi0 : 0 < beta^-1 by rewrite invr_gt0.
have L1 : 1 <= Lref by apply: le_trans Lb; rewrite lerDl ltW.
have Lv : beta^-1 <= Lref by apply: le_trans Lb; rewrite lerDr.
have lt1 : lt <= 1 + I by move: Jle; rewrite -/lt; lra.
have gB1 : gamma * B thr <= 1 + I by move: Jle; rewrite -/lt; lra.
have Lc : C0 * beta^-1 <= Lref.
  have -> : C0 * beta^-1 = lt + gamma * B thr * beta^-1.
    by rewrite /C0 /lt; field.
  rewrite LE mulrDl mul1r; apply: lerD => //.
  by rewrite mulrC; apply: ler_wpM2l => //; exact: ltW.
have Lw : lt * beta^-1 <= Lref.
  apply: le_trans (_ : (1 + I) * beta^-1 <= _).
    by apply: ler_wpM2r => //; exact: ltW.
  rewrite LE [_ * beta^-1]mulrC.
  by apply: ler_wpM2r; [rewrite addr_ge0 | rewrite lerDr].
have E1 : A0 + B1 * (nn * M4) = c1 + c3 / 2 * (beta^-1) ^+ 2 +
    (c2 + c3 / 2) * (2 * (C0 / beta) ^+ 2 + K ^+ 4 / 2 * (lt / beta) ^+ 2).
  have n2 : (n%:R *+ 2 : R) = 2 * nn by rewrite -mulr_natl.
  rewrite /A0 /B1 /M4 /lt n2.
  rewrite /c1 /c2 /c3 /rk /kap /sq /nn.
  have n0r : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
  have sq0' : Num.sqrt (n%:R * gamma) != 0.
    by rewrite gt_eqF // sqrtr_gt0 mulr_gt0 // ltr0n.
  have l0' : lambda != 0 by rewrite gt_eqF.
  by field.
rewrite E1.
have sq_le u : 0 <= u -> u <= Lref -> u ^+ 2 <= Lref ^+ 2.
  by move=> u0 uL; rewrite ler_sqr ?nnegrE // (le_trans u0 uL).
have C00 : 0 <= C0 / beta.
  apply: divr_ge0; last exact: ltW.
  apply: addr_ge0 => //; apply: mulr_ge0; last exact: mxdot_ge0.
  by apply: mulr_ge0; exact: ltW.
have lt00 : 0 <= lt / beta by rewrite divr_ge0 // ltW.
have h1 := sq_le _ (ltW bi0) Lv.
have h2 := sq_le _ C00 Lc.
have h3 := sq_le _ lt00 Lw.
have K40 : 0 <= K ^+ 4 by rewrite exprn_even_ge0.
have inner : 2 * (C0 / beta) ^+ 2 + K ^+ 4 / 2 * (lt / beta) ^+ 2 <=
    2 * kap * Lref ^+ 2.
  have h4 : K ^+ 4 / 2 * (lt / beta) ^+ 2 <= K ^+ 4 / 2 * Lref ^+ 2.
    by rewrite ler_wpM2l // divr_ge0.
  have h5 := mulr_ge0 K40 (sqr_ge0 Lref).
  by rewrite /kap; lra.
have step : c1 + c3 / 2 * beta^-1 ^+ 2 +
    (c2 + c3 / 2) * (2 * (C0 / beta) ^+ 2 + K ^+ 4 / 2 * (lt / beta) ^+ 2) <=
    c1 + c3 / 2 * Lref ^+ 2 + (c2 + c3 / 2) * (2 * kap * Lref ^+ 2).
  apply: lerD; first by rewrite lerD2l ler_wpM2l // divr_ge0.
  by rewrite ler_wpM2l.
apply: le_trans (ler_wpM2l (ltW nn0) step) _.
(* the final constant *)
have t0 : 0 <= Num.sqrt kap := sqrtr_ge0 _.
have tk : Num.sqrt kap <= kap.
  have k0 : 0 <= kap := le_trans ler01 kap1.
  have t1 : 1 <= Num.sqrt kap by rewrite -sqrtr1 ler_wsqrtr.
  rewrite -{2}(sqr_sqrtr k0) expr2.
  by rewrite ler_peMr.
have E2 : nn * (c1 + c3 / 2 * Lref ^+ 2 +
      (c2 + c3 / 2) * (2 * kap * Lref ^+ 2)) =
    4 * sq^-1 + 96 * (kap ^+ 2 * Lref ^+ 2) * sq^-1 +
    (2 + 4 * kap) * Num.sqrt kap * (rk / nn * Lref ^+ 2).
  rewrite /c1 /c2 /c3.
  have sq0' : sq != 0 by rewrite gt_eqF.
  by field.
rewrite E2.
have a0 : 0 <= sq^-1 by rewrite invr_ge0 ltW.
have rL0 : 0 <= rk / nn * Lref ^+ 2.
  by rewrite mulr_ge0 ?divr_ge0 ?sqr_ge0 // ltW.
have kL1 : 1 <= kap ^+ 2 * Lref ^+ 2.
  rewrite -exprMn -(expr1n R 2) ler_sqr ?nnegrE //.
    by rewrite mulr_ge0 // (le_trans ler01).
  by rewrite -[leLHS](mulr1 1) ler_pM.
have q1 : 4 / sq <= 4 * (kap ^+ 2 * Lref ^+ 2) / sq.
  by rewrite ler_wpM2r // ler_peMr.
have q2 : (2 + 4 * kap) * Num.sqrt kap <= 6 * kap ^+ 2.
  apply: le_trans (_ : (2 + 4 * kap) * kap <= _).
    by rewrite ler_wpM2l // addr_ge0 // mulr_ge0 // (le_trans ler01).
  by rewrite expr2; nra.
have q3 := ler_wpM2r rL0 q2.
have kL0 : 0 <= kap ^+ 2 * Lref ^+ 2 * (rk / nn).
  apply: mulr_ge0; first by rewrite mulr_ge0 ?sqr_ge0.
  by apply: divr_ge0 => //; exact: ltW.
have e3 : 6 * kap ^+ 2 * (rk / nn * Lref ^+ 2) =
    6 * (kap ^+ 2 * Lref ^+ 2 * (rk / nn)).
  by rewrite /rk /kap /nn; ring.
rewrite e3 in q3.
have e4 : 100 * kap ^+ 2 * Lref ^+ 2 * (sq^-1 + rk / nn) =
    100 * (kap ^+ 2 * Lref ^+ 2 * sq^-1) +
    100 * (kap ^+ 2 * Lref ^+ 2 * (rk / nn)).
  by rewrite /kap /sq /rk /nn; ring.
have e5 : 96 * (kap ^+ 2 * Lref ^+ 2) / sq =
    96 * (kap ^+ 2 * Lref ^+ 2 * sq^-1).
  by rewrite /kap /sq /nn; ring.
have e6 : 4 * (kap ^+ 2 * Lref ^+ 2) / sq =
    4 * (kap ^+ 2 * Lref ^+ 2 * sq^-1).
  by rewrite /kap /sq /nn; ring.
rewrite e5 e4; rewrite e6 in q1.
have kLa : 0 <= kap ^+ 2 * Lref ^+ 2 * sq^-1.
  by apply: mulr_ge0 => //; rewrite mulr_ge0 ?sqr_ge0.
move: q1 q3 kLa kL0.
set X := kap ^+ 2 * Lref ^+ 2 / sq.
set Y := kap ^+ 2 * Lref ^+ 2 * (rk / nn).
set Z := (2 + 4 * kap) * Num.sqrt kap * (rk / nn * Lref ^+ 2).
move=> q1 q3 kLa kL0.
lra.
Qed.

(* The variance in the coordinate i, the other coordinates being fixed. *)
Lemma loo_variance (thr : 'rV[R]_N) (i : 'I_n) (x : n.-tuple 'rV[R]_N) :
  D thr ->
  ('V_mu[fun t => Phi (tuple_set x i t)] <=
    (2 * (1 + K ^+ 4) / n%:R ^+ 2 * (Sbar thr i x) ^+ 2)%:E)%E.
Proof.
move=> Dthr.
have lam0 := reg_lambda_gt0 rmu.
have s0 : 0 <= s by rewrite invr_ge0 mulrn_wge0 // ler0n.
have [thm [bm [Dthm thmin]]] :=
  ls_barrier_minimizer x (fun j => j != i) DV scB B0 s0 lam0 b0 g0 D0.
set Fv := ls_barrier_objective x (fun j => j != i) s lambda beta gamma B thm bm.
pose f z := ins_cost D B x i lambda beta gamma thm bm z.
have PhiE t : Phi (tuple_set x i t) = f t + Fv by rewrite /f /ins_cost subrK.
have mf' : measurable_fun setT (fun t => Phi (tuple_set x i t)).
  exact: measurableT_comp Phi_meas (measurable_tuple_set x i).
have mf : measurable_fun setT f.
  rewrite /f /ins_cost; apply: measurable_funB => //; exact: measurable_cst.
(* the variance is at most the second moment of the insertion cost *)
apply: le_trans (variance_le_sqr_dev mu Fv mf') _.
under eq_integral do rewrite PhiE addrK.
have fb z : 0 <= f z <= (bm - mxdot z thm) ^+ 2 / (2 * n%:R).
  exact: (ins_cost_bounds Dthm thmin z).
have ir4 := reg_int_resid4 rmu thm bm.
have i4 := integrableRZr ((2 * n%:R) ^+ 2)^-1 ir4.
apply: le_trans (_ : \int[mu]_t ((bm - mxdot t thm) ^+ 4 /
    (2 * n%:R) ^+ 2)%:E <= _)%E.
  apply: ge0_le_integral => //.
  - by move=> t _; rewrite lee_fin sqr_ge0.
  - by apply/measurable_EFinP; apply: measurable_funX.
  - by move/integrableP : i4 => [].
  - move=> t _; rewrite lee_fin.
    have /andP[f0 f1] := fb t.
    have -> : (bm - mxdot t thm) ^+ 4 / (2 * n%:R) ^+ 2 =
        ((bm - mxdot t thm) ^+ 2 / (2 * n%:R)) ^+ 2.
      by rewrite expr_div_n -exprM.
    by rewrite ler_sqr ?nnegrE // (le_trans f0 f1).
rewrite -(Rintegral_EFin i4) lee_fin (RintegralZr _ measurableT ir4).
have R4 := reg_resid4 rmu thm bm.
(* the size of the minimizer is at most Sbar *)
have S0 : 0 <= lambda * mxdot thm thm + bm ^+ 2.
  by rewrite addr_ge0 ?sqr_ge0 // mulr_ge0 ?mxdot_ge0 // ltW.
have Sle : lambda * mxdot thm thm + bm ^+ 2 <=
    ((n%:R *+ 2)^-1 * \sum_(j < n | j != i) mxdot (tnth x j) thr ^+ 2 +
      beta * lambda * mxdot thr thr + gamma * B thr) / beta.
  rewrite ler_pdivlMr // [X in X <= _]mulrC.
  exact: (ins_size_le B0 g0 Dthm thmin Dthr).
set Sb := (_ / beta) in Sle *.
have S2 : (lambda * mxdot thm thm + bm ^+ 2) ^+ 2 <= Sb ^+ 2.
  by rewrite ler_sqr ?nnegrE // (le_trans S0 Sle).
have nn0 : 0 < (n%:R : R) by rewrite ltr0n.
have c0 : 0 < ((2 * n%:R) ^+ 2)^-1 :> R.
  by rewrite invr_gt0 exprn_gt0 // mulr_gt0.
apply: le_trans (ler_wpM2r (ltW c0) R4) _.
have kap0 : 0 <= 1 + K ^+ 4 by rewrite addr_ge0 // exprn_even_ge0.
apply: le_trans (_ : 8 * (1 + K ^+ 4) * Sb ^+ 2 * ((2 * n%:R) ^+ 2)^-1 <= _).
  by apply: ler_wpM2r; [exact: ltW | rewrite ler_wpM2l // mulr_ge0].
have nn0' : (n%:R : R) != 0 by rewrite gt_eqF.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by field.
Qed.

Lemma Sbar_sqr_le (thr : 'rV[R]_N) (i : 'I_n) (x : n.-tuple 'rV[R]_N) :
  (Sbar thr i x) ^+ 2 <=
  (2 * s ^+ 2 * n%:R * \sum_(j < n) mxdot (tnth x j) thr ^+ 4 +
   2 * (beta * lambda * mxdot thr thr + gamma * B thr) ^+ 2) / beta ^+ 2.
Proof.
set Y := \sum_(j < n | j != i) mxdot (tnth x j) thr ^+ 2.
set C0 := beta * lambda * mxdot thr thr + gamma * B thr.
have YP : Y ^+ 2 <= n%:R * \sum_(j < n) mxdot (tnth x j) thr ^+ 4.
  apply: le_trans (sum_pred_sqr_le _
    (fun j => sqr_ge0 (mxdot (tnth x j) thr))) _.
  by under eq_bigr do rewrite -exprM.
have -> : Sbar thr i x = (s * Y + C0) / beta by rewrite /C0 addrA.
rewrite expr_div_n ler_pM2r ?invr_gt0 ?exprn_gt0 //.
have h1 := sqr_ge0 (s * Y - C0).
have h2 : s ^+ 2 * Y ^+ 2 <=
    s ^+ 2 * (n%:R * \sum_(j < n) mxdot (tnth x j) thr ^+ 4).
  by rewrite ler_wpM2l ?sqr_ge0.
by nra.
Qed.

Lemma int_P4 (rho : nat -> probability 'rV[R]_N R) (thr : 'rV[R]_N) :
  (forall j, regular_feature K tau Sigma (rho j)) ->
  (tuple_prod rho n).-integrable setT
    (EFin \o (fun x => \sum_(j < n) mxdot (tnth x j) thr ^+ 4)) /\
  \int[tuple_prod rho n]_x (\sum_(j < n) mxdot (tnth x j) thr ^+ 4) <=
    n%:R * (K ^+ 4 * lambda ^+ 2 * mxdot thr thr ^+ 2).
Proof.
move=> hr.
have ij (j : 'I_n) := @integrable_tuple_prod_tnth _ _ _ rho n j
  (fun z => mxdot z thr ^+ 4) (reg_int4 (hr j) thr).
split; first exact: integrableR_sum.
rewrite (Rintegral_sumr _ ij).
have -> : n%:R * (K ^+ 4 * lambda ^+ 2 * mxdot thr thr ^+ 2) =
    \sum_(j < n) (K ^+ 4 * lambda ^+ 2 * mxdot thr thr ^+ 2).
  by rewrite sumr_const card_ord mulr_natl.
apply: ler_sum => j _.
rewrite (Rintegral_tuple_prod_tnth rho j (g := fun z => mxdot z thr ^+ 4)).
- by apply: measurable_funX; exact: measurable_mxdotl.
- by move=> t; rewrite exprn_even_ge0.
- exact: reg_moment4 (hr j) thr.
Qed.

(* E Sbar^2 <= 2 (1 + K^4) Lref^2 at a reference point. *)
Lemma ref_moment_bound (thr : 'rV[R]_N) : D thr ->
  opnorm Sigma * mxdot thr thr + gamma * B thr <=
    1 + inf [set opnorm Sigma * mxdot th th + gamma * B th | th in D] ->
  (2 * s ^+ 2 * n%:R * (n%:R * (K ^+ 4 * lambda ^+ 2 * mxdot thr thr ^+ 2)) +
   2 * (beta * lambda * mxdot thr thr + gamma * B thr) ^+ 2) / beta ^+ 2 <=
  2 * (1 + K ^+ 4) * Lref ^+ 2.
Proof.
move=> Dthr; set I := inf _ => Jle.
have lam0 := reg_lambda_gt0 rmu.
set lt := lambda * mxdot thr thr.
have lt0 : 0 <= lt by rewrite mulr_ge0 ?mxdot_ge0 // ltW.
have BB0 : 0 <= gamma * B thr by rewrite mulr_ge0 ?B0 // ltW.
have LE : Lref = (1 + beta^-1) * (1 + I) by [].
have bi0 : 0 < beta^-1 by rewrite invr_gt0.
have lt1 : lt <= 1 + I by move: Jle; rewrite -/lt; lra.
have gB1 : gamma * B thr <= 1 + I by move: Jle; rewrite -/lt; lra.
have b0' : beta != 0 by rewrite gt_eqF.
have nn0' : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
set C0 := beta * lambda * mxdot thr thr + gamma * B thr.
have Lc : C0 / beta <= Lref.
  have -> : C0 / beta = lt + gamma * B thr * beta^-1.
    by rewrite /C0 /lt; field.
  rewrite LE mulrDl mul1r; apply: lerD => //.
  by rewrite mulrC; apply: ler_wpM2l => //; exact: ltW.
have Lw : lt / beta <= Lref.
  apply: le_trans (_ : (1 + I) * beta^-1 <= _).
    by apply: ler_wpM2r => //; exact: ltW.
  rewrite LE [_ * beta^-1]mulrC.
  have I1 : 0 <= 1 + I by apply: le_trans Jle; rewrite -/lt addr_ge0.
  by apply: ler_wpM2r => //; rewrite lerDr.
have -> : (2 * s ^+ 2 * n%:R * (n%:R * (K ^+ 4 * lambda ^+ 2 *
    mxdot thr thr ^+ 2)) + 2 * C0 ^+ 2) / beta ^+ 2 =
    2 * (C0 / beta) ^+ 2 + K ^+ 4 / 2 * (lt / beta) ^+ 2.
  have n2 : (n%:R *+ 2 : R) = 2 * n%:R by rewrite -mulr_natl.
  by rewrite n2 /lt; field.
have sq_le u : 0 <= u -> u <= Lref -> u ^+ 2 <= Lref ^+ 2.
  by move=> u0 uL; rewrite ler_sqr ?nnegrE // (le_trans u0 uL).
have C00 : 0 <= C0 / beta.
  apply: divr_ge0; last exact: ltW.
  apply: addr_ge0 => //; apply: mulr_ge0; last exact: mxdot_ge0.
  by apply: mulr_ge0; exact: ltW.
have lt00 : 0 <= lt / beta by rewrite divr_ge0 // ltW.
have h2 := sq_le _ C00 Lc.
have h3 := sq_le _ lt00 Lw.
have K40 : 0 <= K ^+ 4 by rewrite exprn_even_ge0.
have h4 : K ^+ 4 / 2 * (lt / beta) ^+ 2 <= K ^+ 4 / 2 * Lref ^+ 2.
  by rewrite ler_wpM2l // divr_ge0.
have h5 := mulr_ge0 K40 (sqr_ge0 Lref).
lra.
Qed.

(* Theorem 2.9, (2.13): the variance of the value, for the law mu (and, the
   hypotheses being symmetric, for nu). *)
Theorem barrier_lindeberg_variance :
  ('V_(tuple_prod (fun=> mu) n)[fun Z => Phi Z] <=
    (4 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 / n%:R)%:E)%E.
Proof.
have [thr Dthr [I0 Jle Lb]] := ref_point.
have hmu : forall j : nat, regular_feature K tau Sigma ((fun=> mu) j) by [].
(* the Efron-Stein inequality *)
apply: le_trans (efron_stein_integrable (int_Phi hmu)) _.
set kap := 1 + K ^+ 4.
set nn := (n%:R : R).
have nn0 : 0 < nn by rewrite ltr0n.
set C0 := beta * lambda * mxdot thr thr + gamma * B thr.
pose P4 (x : n.-tuple 'rV[R]_N) := \sum_(j < n) mxdot (tnth x j) thr ^+ 4.
have [iP4 EP4] := int_P4 thr hmu.
set c := 2 * kap / nn ^+ 2.
have c0 : 0 <= c.
  by rewrite divr_ge0 ?sqr_ge0 // mulr_ge0 // addr_ge0 // exprn_even_ge0.
pose g x := c * ((2 * s ^+ 2 * nn * P4 x + 2 * C0 ^+ 2) / beta ^+ 2).
(* the variance in each coordinate *)
have Vb (i : 'I_n) x :
    ('V_mu[fun t => Phi (tuple_set x i t)] <= (g x)%:E)%E.
  apply: le_trans (loo_variance i x Dthr) _.
  by rewrite lee_fin ler_wpM2l // Sbar_sqr_le.
have iQ : (tuple_prod (fun=> mu) n).-integrable setT
    (EFin \o (fun x => 2 * s ^+ 2 * nn * P4 x + 2 * C0 ^+ 2)).
  apply: integrableRD; first exact: integrableRZl iP4.
  exact: integrable_cst_prob.
have iQb := integrableRZr (beta ^+ 2)^-1 iQ.
have ig : (tuple_prod (fun=> mu) n).-integrable setT (EFin \o g).
  by rewrite /g; exact: (integrableRZl c iQb).
have Ei (i : 'I_n) :
    (\int[tuple_prod (fun=> mu) n]_x
       'V_mu[fun t => Phi (tuple_set x i t)] <=
     (c * (2 * kap * Lref ^+ 2))%:E)%E.
  have h : (\int[tuple_prod (fun=> mu) n]_x
       'V_mu[fun t => Phi (tuple_set x i t)] <=
      \int[tuple_prod (fun=> mu) n]_x (g x)%:E)%E.
    apply: ge0_le_integral => //.
    - by move=> x _; exact: variance_ge0.
    - exact: (measurable_variance_tuple_set (fun=> mu) i Phi_meas).
    - by case/integrableP : ig.
  apply: le_trans h _.
  rewrite -(Rintegral_EFin ig) lee_fin.
  rewrite /g (RintegralZl _ measurableT iQb) ler_wpM2l //.
  rewrite (RintegralZr _ measurableT iQ).
  rewrite (RintegralD measurableT (integrableRZl _ iP4)
    (integrable_cst_prob _ _)).
  rewrite (RintegralZl _ measurableT iP4) Rintegral_cst_prob.
  apply: le_trans (ref_moment_bound Dthr Jle).
  rewrite ler_wpM2r ?invr_ge0 ?sqr_ge0 // lerD2r ler_wpM2l //.
  by rewrite mulr_ge0 ?mulr_ge0 ?sqr_ge0 // ltW.
(* the sum over the coordinates *)
apply: (@le_trans _ _ (\sum_(i < n) (c * (2 * kap * Lref ^+ 2))%:E)%E).
  by apply: lee_sum => i _; exact: Ei.
rewrite sumEFin sumr_const card_ord lee_fin -mulr_natr -/nn.
have nn0' : nn != 0 by rewrite gt_eqF.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
by rewrite /c /kap /nn; field.
Qed.

(* Theorem 2.9, (2.14), for the law mu (and, the hypotheses being symmetric,
   for nu): the value is close to the mean of the value under nu^n. *)
Theorem barrier_lindeberg_concentration (t : R) :
  0 < t -> 36 <= n%:R * gamma ->
  (tuple_prod (fun=> mu) n
     [set Z | (100 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 *
        ((Num.sqrt (n%:R * gamma))^-1 +
         Num.sqrt (\dim V)%:R * (tau / opnorm Sigma + 1) / n%:R) + t <
        `|Phi Z - \int[tuple_prod (fun=> nu) n]_Z Phi Z|)%R] <=
   (4 * (1 + K ^+ 4) ^+ 2 * Lref ^+ 2 / (n%:R * t ^+ 2))%:E)%E.
Proof.
move=> t0 n36.
set err := 100 * _ * _ * _.
set Ev := \int[tuple_prod (fun=> nu) n]_Z Phi Z.
set Eu := \int[tuple_prod (fun=> mu) n]_Z Phi Z.
have hm : `|Eu - Ev| <= err := barrier_lindeberg_mean n36.
(* Chebyshev's inequality for the value under mu^n *)
pose X : {RV (tuple_prod (fun=> mu) n) >-> R} := HB.pack (fun Z => Phi Z)
  (isMeasurableFun.Build _ _ _ _ (fun Z => Phi Z) Phi_meas).
have cheb := chebyshev X t0.
have EX : fine 'E_(tuple_prod (fun=> mu) n)[X] = Eu by rewrite unlock.
rewrite EX in cheb.
have mlt (f : n.-tuple 'rV[R]_N -> R) (a : R) (lt : bool) :
    measurable_fun setT f ->
    measurable [set Z | (if lt then a < f Z else a <= f Z)%R].
  move=> mf.
  have := mf measurableT _
    (measurable_itv (Interval (BSide (~~ lt) a) +oo%O)).
  rewrite setTI; congr measurable; apply/seteqP; split => z /=.
    by rewrite in_itv /= andbT; case: lt.
  by rewrite in_itv /= andbT; case: lt.
have mF (c : R) :
    measurable_fun setT (fun Z : n.-tuple 'rV[R]_N => `|Phi Z - c|).
  apply: measurableT_comp => //; apply: measurable_funB => //.
  exact: Phi_meas.
apply: (@le_trans _ _
  (tuple_prod (fun=> mu) n [set x | (t <= `|X x - Eu|)%R])).
  apply: le_measure; rewrite ?inE.
  - exact: (mlt _ (err + t) true (mF Ev)).
  - exact: (mlt _ t false (mF Eu)).
  move=> Z /= h.
  have := ler_distD Eu (Phi Z) Ev.
  by move=> h2; lra.
apply: le_trans cheb _.
have hv := barrier_lindeberg_variance.
apply: le_trans (lee_wpmul2l _ hv) _.
  by rewrite lee_fin invr_ge0 exprn_ge0 // ltW.
rewrite -EFinM lee_fin.
have t0' : t != 0 by rewrite gt_eqF.
have nn0' : (n%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
by rewrite le_eqVlt; apply/orP; left; apply/eqP; field.
Qed.

End barrier_lindeberg.
