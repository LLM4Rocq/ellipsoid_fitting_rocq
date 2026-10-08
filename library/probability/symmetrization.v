From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import efron_stein.

(**md**************************************************************************)
(* # Rademacher averages, contraction and symmetrization                      *)
(*                                                                            *)
(* Rademacher signs are written as a finite average over the 2^n sign         *)
(* vectors, not as a measure. For independent random elements X_1, ..., X_n   *)
(* (tuple_prod) and a finite class of functions f_j, the tools of empirical   *)
(* process theory that the small-ball method needs, for expectations only:    *)
(* no concentration inequality is used.                                       *)
(*                                                                            *)
(* Main results:                                                              *)
(* - rademacher_mean_cst, rademacher_meanD, rademacher_meanZ,                 *)
(*   ler_rademacher_mean, rademacher_mean_flip, rademacher_mean_neg: the      *)
(*   average over signs is linear, monotone, and invariant under changing one *)
(*   sign or all of them; rademacher_mean_prod: E eps_k eps_l = [k == l];     *)
(*   rademacher_mean_sqr_sum, rademacher_mean_abs_sum:                        *)
(*   E (sum_k a_k eps_k)^2 = sum_k a_k^2, hence                               *)
(*   E |sum_k a_k eps_k| <= (sum_k a_k^2)^(1/2).                              *)
(* - Contraction (Ledoux-Talagrand), contraction: for a finite class of       *)
(*   vectors t_j of R^n and L-Lipschitz phi_k with phi_k(0) = 0,              *)
(*     rademacher_mean (max_j |sum_k eps_k phi_k(t_jk)|)                      *)
(*       <= 2 L rademacher_mean (max_j |sum_k eps_k t_jk|);                   *)
(*   contraction_bigmax0: the same without absolute values and without the    *)
(*   factor 2, over the class and the zero vector, proved one coordinate at a *)
(*   time (bigmax0_contraction1).                                             *)
(* - Symmetrization (Gine-Zinn), symmetrization: for x of law tuple_prod mu n *)
(*   and measurable f_j integrable for every mu_k,                            *)
(*     E max_j |sum_k (f_j(x_k) - E f_j(x_k))|                                *)
(*       <= 2 E rademacher_mean (max_j |sum_k eps_k f_j(x_k)|),               *)
(*   as integrals in [0, +oo]. Proof: an independent copy as the second block *)
(*   of n + n coordinates of law doubled_law mu n (ge0_integral_tuple_left,   *)
(*   ge0_integral_tuple_right); Jensen's inequality for max_norm              *)
(*   (jensen_max_norm), one coordinate of the copy at a time, and the         *)
(*   exchange of x_k and its copy (ge0_integral_swap), both by Fubini at one  *)
(*   coordinate (ge0_integral_tuple_prod_set of efron_stein.v).               *)
(* - Tools: max_normD, max_normN (max_norm is a norm), measurable_bigmax0,    *)
(*   measurable_max_norm, ge0_integral_rademacher_mean,                       *)
(*   measurable_rademacher_mean.                                              *)
(*                                                                            *)
(* ```                                                                        *)
(*                rademacher b == the sign 1 if b, -1 otherwise               *)
(*           rademacher_mean F == 2^-n sum_{s : n.-tuple bool} F s, the       *)
(*                                expectation of F over n independent signs   *)
(*               sign_flip i s == s with its sign i changed                   *)
(*                  sign_neg s == s with every sign changed                   *)
(*                  max_norm v == max_j |v j| for v : 'I_m -> R (0 if m = 0)  *)
(*            doubled_law mu n == the laws of n + n coordinates whose two     *)
(*                                blocks are independent copies of            *)
(*                                tuple_prod mu n                             *)
(* tuple_left z, tuple_right z == the two blocks of z : (n + n).-tuple T      *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section rademacher.
Context {R : realType}.

Definition rademacher (b : bool) : R := if b then 1 else -1.

Definition rademacher_mean n (F : n.-tuple bool -> R) : R :=
  (2 ^+ n)^-1 * \sum_(s : n.-tuple bool) F s.

End rademacher.

Section rademacher_theory.
Context {R : realType}.
Local Notation rm := (@rademacher_mean R).

Lemma rademacherN b : rademacher (~~ b) = - rademacher b :> R.
Proof. by case: b; rewrite /rademacher /= ?opprK. Qed.

Lemma rademacher_sqr b : rademacher b ^+ 2 = 1 :> R.
Proof. by case: b; rewrite /rademacher ?sqrrN expr1n. Qed.

Lemma normr_rademacher b : `|rademacher b| = 1 :> R.
Proof. by case: b; rewrite /rademacher ?normrN normr1. Qed.

Lemma rademacher_mean_cst n (c : R) : rm (fun _ : n.-tuple bool => c) = c.
Proof.
rewrite /rademacher_mean sumr_const card_tuple card_bool.
by rewrite -[c *+ _]mulr_natl natrX mulKf// expf_neq0// pnatr_eq0.
Qed.

Lemma rademacher_meanD n (F G : n.-tuple bool -> R) :
  rm (fun s => F s + G s) = rm F + rm G.
Proof. by rewrite /rademacher_mean big_split mulrDr. Qed.

Lemma rademacher_meanZ n (c : R) (F : n.-tuple bool -> R) :
  rm (fun s => c * F s) = c * rm F.
Proof. by rewrite /rademacher_mean -mulr_sumr mulrCA. Qed.

Lemma ler_rademacher_mean n (F G : n.-tuple bool -> R) :
  (forall s, F s <= G s) -> rm F <= rm G.
Proof.
move=> FG; rewrite /rademacher_mean ler_wpM2l ?invr_ge0 ?exprn_ge0 ?ler0n//.
exact: ler_sum.
Qed.

Lemma rademacher_mean_ge0 n (F : n.-tuple bool -> R) :
  (forall s, 0 <= F s) -> 0 <= rm F.
Proof.
move=> F0; rewrite -(rademacher_mean_cst n 0); exact: ler_rademacher_mean.
Qed.

(* Changing the sign of coordinate i, and of every coordinate. *)
Definition sign_flip n (i : 'I_n) (s : n.-tuple bool) : n.-tuple bool :=
  [tuple if j == i then ~~ tnth s j else tnth s j | j < n].

Definition sign_neg n (s : n.-tuple bool) : n.-tuple bool :=
  [tuple ~~ tnth s j | j < n].

Lemma tnth_sign_flip n (i j : 'I_n) s :
  tnth (sign_flip i s) j = if j == i then ~~ tnth s j else tnth s j.
Proof. by rewrite tnth_mktuple. Qed.

Lemma sign_flipK n (i : 'I_n) : involutive (sign_flip i).
Proof.
move=> s; apply: eq_from_tnth => j; rewrite !tnth_sign_flip.
by case: (j == i); rewrite ?negbK.
Qed.

Lemma sign_negK n : involutive (@sign_neg n).
Proof. by move=> s; apply: eq_from_tnth => j; rewrite !tnth_mktuple negbK. Qed.

Lemma rademacher_mean_flip n (i : 'I_n) (F : n.-tuple bool -> R) :
  rm (fun s => F (sign_flip i s)) = rm F.
Proof.
rewrite /rademacher_mean; congr (_ * _).
by rewrite [RHS](reindex_inj (can_inj (sign_flipK i))).
Qed.

Lemma rademacher_mean_neg n (F : n.-tuple bool -> R) :
  rm (fun s => F (sign_neg s)) = rm F.
Proof.
rewrite /rademacher_mean; congr (_ * _).
by rewrite [RHS](reindex_inj (can_inj (@sign_negK n))).
Qed.

(* The average over the sign of coordinate i. *)
Lemma rademacher_mean_pair n (i : 'I_n) (F : n.-tuple bool -> R) :
  rm F = rm (fun s => 2^-1 * (F s + F (sign_flip i s))).
Proof.
rewrite rademacher_meanZ rademacher_meanD rademacher_mean_flip.
by move: (rm F) => x; field.
Qed.

(* A maximum \big[Num.max/0] over a class is the maximum over the class and
   the zero vector. *)
Lemma bigmax0_ge0 m (F : 'I_m -> R) : 0 <= \big[Num.max/0]_(j < m) F j.
Proof. by elim/big_rec: _ => // i x _ x0; rewrite le_max x0 orbT. Qed.

(* Contraction at one coordinate. *)
Lemma bigmax0_contraction1 m (a t : 'I_m -> R) (phi : R -> R) (L : R) :
  (forall x y, `|phi x - phi y| <= L * `|x - y|) -> phi 0 = 0 ->
  \big[Num.max/0]_(j < m) (a j + phi (t j)) +
  \big[Num.max/0]_(j < m) (a j - phi (t j)) <=
  \big[Num.max/0]_(j < m) (a j + L * t j) +
  \big[Num.max/0]_(j < m) (a j - L * t j).
Proof.
move=> phiL phi0.
set M1 := \big[Num.max/0]_(j < m) (a j + L * t j).
set M2 := \big[Num.max/0]_(j < m) (a j - L * t j).
have M10 : 0 <= M1 := bigmax0_ge0 _.
have M20 : 0 <= M2 := bigmax0_ge0 _.
have pair a1 t1 a2 t2 : a1 + L * t1 <= M1 -> a1 - L * t1 <= M2 ->
    a2 + L * t2 <= M1 -> a2 - L * t2 <= M2 ->
    a1 + phi t1 + (a2 - phi t2) <= M1 + M2.
  move=> h1 h1' h2 h2'; have := phiL t1 t2.
  case: (leP t2 t1) => tt.
    by rewrite [`|t1 - t2|]ger0_norm ?subr_ge0// => /ler_normlP[_]; lra.
  by rewrite [`|t1 - t2|]ltr0_norm ?subr_lt0// => /ler_normlP[_]; lra.
have h1 j : a j + L * t j <= M1 by exact: le_bigmax.
have h2 j : a j - L * t j <= M2 by exact: le_bigmax.
have z1 : 0 + L * 0 <= M1 by rewrite mulr0 addr0.
have z2 : 0 - L * 0 <= M2 by rewrite mulr0 subr0.
rewrite -lerBrDr; apply: bigmax_le.
  rewrite subr_ge0; apply: bigmax_le => [|j _]; first by rewrite addr_ge0.
  have := pair 0 0 (a j) (t j) z1 z2 (h1 j) (h2 j).
  by rewrite phi0 !addr0 add0r.
move=> j1 _; rewrite lerBrDr addrC -lerBrDr; apply: bigmax_le => [|j2 _].
  rewrite subr_ge0.
  have := pair (a j1) (t j1) 0 0 (h1 j1) (h2 j1) z1 z2.
  by rewrite phi0 subr0 addr0.
by rewrite lerBrDr addrC; exact: pair.
Qed.

Lemma bigmax0_pM m (c : R) (F : 'I_m -> R) : 0 <= c ->
  \big[Num.max/0]_(j < m) (c * F j) = c * \big[Num.max/0]_(j < m) F j.
Proof.
move=> c0; elim/big_rec2: _ => [|j x y _ ->]; first by rewrite mulr0.
by rewrite maxr_pMr.
Qed.

Lemma sum_rademacher_flip n (i : 'I_n) (s : n.-tuple bool) (g : 'I_n -> R) :
  \sum_(k < n) rademacher (tnth (sign_flip i s) k) * g k =
  \sum_(k < n | k != i) rademacher (tnth s k) * g k
  - rademacher (tnth s i) * g i.
Proof.
rewrite (bigD1 i)//= tnth_sign_flip eqxx rademacherN mulNr addrC.
congr (_ - _); apply: eq_bigr => k ki.
by rewrite tnth_sign_flip (negbTE ki).
Qed.

(* Contraction (Ledoux-Talagrand) without absolute values, over a class
   that contains the zero vector. *)
Lemma contraction_bigmax0 n m (t : 'I_m -> 'I_n -> R) (phi : 'I_n -> R -> R)
    (L : R) : 0 <= L ->
  (forall k x y, `|phi k x - phi k y| <= L * `|x - y|) ->
  (forall k, phi k 0 = 0) ->
  rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    \sum_(k < n) rademacher (tnth s k) * phi k (t j k)) <=
  L * rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    \sum_(k < n) rademacher (tnth s k) * t j k).
Proof.
move=> L0 phiL phi0.
(* g p replaces phi_k by L times the identity on the coordinates k < p. *)
pose g p j (k : 'I_n) := if (k < p)%N then L * t j k else phi k (t j k).
pose H p (s : n.-tuple bool) := \big[Num.max/0]_(j < m)
  \sum_(k < n) rademacher (tnth s k) * g p j k.
have H0 : H 0%N = (fun s => \big[Num.max/0]_(j < m)
    \sum_(k < n) rademacher (tnth s k) * phi k (t j k)) by [].
have Hn : H n = (fun s => L * \big[Num.max/0]_(j < m)
    \sum_(k < n) rademacher (tnth s k) * t j k).
  apply/funext => s; rewrite /H -bigmax0_pM//; apply: eq_bigr => j _.
  by rewrite mulr_sumr; apply: eq_bigr => k _; rewrite /g ltn_ord mulrCA.
have step (i : 'I_n) s : H i s + H i (sign_flip i s) <=
    H i.+1 s + H i.+1 (sign_flip i s).
  pose a p j := \sum_(k < n | k != i) rademacher (tnth s k) * g p j k.
  have aS j : a i.+1 j = a i j.
    apply: eq_bigr => k ki; rewrite /g ltnS leq_eqVlt.
    by have -> : (k == i :> nat) = false by apply/negbTE.
  have E p j : \sum_(k < n) rademacher (tnth s k) * g p j k =
      a p j + rademacher (tnth s i) * g p j i.
    by rewrite (bigD1 i)//= addrC.
  rewrite /H; under eq_bigr do rewrite E; under [X in _ + X]eq_bigr do
    rewrite sum_rademacher_flip -/(a _ _).
  under [X in _ <= X + _]eq_bigr do rewrite E aS.
  under [X in _ <= _ + X]eq_bigr do rewrite sum_rademacher_flip -/(a _ _) aS.
  rewrite /g ltnn leqnn.
  have C := bigmax0_contraction1 (a i) (fun j => t j i) (phiL i) (phi0 i).
  case: (tnth s i); rewrite /rademacher.
    under [X in X + _ <= _]eq_bigr do rewrite mul1r.
    under [X in _ + X <= _]eq_bigr do rewrite mul1r.
    under [X in _ <= X + _]eq_bigr do rewrite mul1r.
    under [X in _ <= _ + X]eq_bigr do rewrite mul1r.
    exact: C.
  under [X in X + _ <= _]eq_bigr do rewrite mulN1r.
  under [X in _ + X <= _]eq_bigr do rewrite mulN1r opprK.
  under [X in _ <= X + _]eq_bigr do rewrite mulN1r.
  under [X in _ <= _ + X]eq_bigr do rewrite mulN1r opprK.
  by rewrite addrC [X in _ <= X]addrC.
have mono (i : 'I_n) : rm (H i) <= rm (H i.+1).
  rewrite (rademacher_mean_pair i (H i)) (rademacher_mean_pair i (H i.+1)).
  apply: ler_rademacher_mean => s.
  by rewrite ler_pM2l ?invr_gt0 ?ltr0n//; exact: step.
have chain p : (p <= n)%N -> rm (H 0%N) <= rm (H p).
  elim: p => [|p IH] pn; first by [].
  exact: le_trans (IH (ltnW pn)) (mono (Ordinal pn)).
by have := chain n (leqnn n); rewrite H0 Hn rademacher_meanZ.
Qed.

Lemma sum_rademacher_neg n (s : n.-tuple bool) (g : 'I_n -> R) :
  \sum_(k < n) rademacher (tnth (sign_neg s) k) * g k =
  - \sum_(k < n) rademacher (tnth s k) * g k.
Proof.
rewrite -sumrN; apply: eq_bigr => k _.
by rewrite tnth_mktuple rademacherN mulNr.
Qed.

(* Contraction (Ledoux-Talagrand). *)
Lemma contraction n m (t : 'I_m -> 'I_n -> R) (phi : 'I_n -> R -> R)
    (L : R) : 0 <= L ->
  (forall k x y, `|phi k x - phi k y| <= L * `|x - y|) ->
  (forall k, phi k 0 = 0) ->
  rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    `|\sum_(k < n) rademacher (tnth s k) * phi k (t j k)|) <=
  2 * L * rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    `|\sum_(k < n) rademacher (tnth s k) * t j k|).
Proof.
move=> L0 phiL phi0.
pose Y (s : n.-tuple bool) j :=
  \sum_(k < n) rademacher (tnth s k) * phi k (t j k).
(* |Y_j| is at most the maximum of the Y_j and 0 plus that of the -Y_j and
   0; changing every sign maps the second to the first. *)
have split s : \big[Num.max/0]_(j < m) `|Y s j| <=
    \big[Num.max/0]_(j < m) Y s j + \big[Num.max/0]_(j < m) Y (sign_neg s) j.
  apply: bigmax_le => [|j _]; first by rewrite addr_ge0 ?bigmax0_ge0.
  have YN : Y (sign_neg s) j = - Y s j by rewrite /Y sum_rademacher_neg.
  have h1 : Y s j <= \big[Num.max/0]_(j < m) Y s j by exact: le_bigmax.
  have h2 : Y (sign_neg s) j <= \big[Num.max/0]_(j < m) Y (sign_neg s) j.
    exact: le_bigmax.
  have := bigmax0_ge0 (Y s); have := bigmax0_ge0 (Y (sign_neg s)).
  rewrite YN in h2.
  move=> M20 M10; case: (lerP 0 (Y s j)) => y0.
    by rewrite ger0_norm//; apply: le_trans h1 _; rewrite lerDl.
  by rewrite ltr0_norm//; apply: le_trans h2 _; rewrite lerDr.
apply: le_trans (ler_rademacher_mean split) _.
rewrite rademacher_meanD.
rewrite (rademacher_mean_neg (fun s => \big[Num.max/0]_(j < m) Y s j)).
have C := contraction_bigmax0 t L0 phiL phi0.
have D : rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    \sum_(k < n) rademacher (tnth s k) * t j k) <=
  rm (fun s : n.-tuple bool => \big[Num.max/0]_(j < m)
    `|\sum_(k < n) rademacher (tnth s k) * t j k|).
  apply: ler_rademacher_mean => s; apply: bigmax_le => [|j _].
    exact: bigmax0_ge0.
  exact: le_trans (ler_norm _) (le_bigmax _ _ _).
rewrite -mulrA mulr2n mulrDl mul1r.
have CD := le_trans C (ler_wpM2l L0 D).
by apply: lerD; exact: CD.
Qed.

Lemma rademacher_mean_sum n (I : finType) (F : I -> n.-tuple bool -> R) :
  rm (fun s => \sum_(i : I) F i s) = \sum_(i : I) rm (F i).
Proof. by rewrite /rademacher_mean exchange_big mulr_sumr. Qed.

Lemma rademacher_mean_prod n (k l : 'I_n) :
  rm (fun s : n.-tuple bool => rademacher (tnth s k) * rademacher (tnth s l)) =
  (k == l)%:R.
Proof.
have [<-|kl] := eqVneq k l.
  under eq_fun do rewrite -expr2 rademacher_sqr.
  exact: rademacher_mean_cst.
set F := fun s : n.-tuple bool => _.
have FN s : F (sign_flip k s) = - F s.
  by rewrite /F !tnth_sign_flip eqxx eq_sym (negbTE kl) rademacherN mulNr.
have E : rm F = - rm F.
  rewrite -[X in X = _](rademacher_mean_flip k F).
  under eq_fun do rewrite FN.
  by rewrite /rademacher_mean sumrN mulrN.
by move: E; move: (rm F) => x; rewrite /= => e; lra.
Qed.

Lemma rademacher_mean_sqr_sum n (a : 'I_n -> R) :
  rm (fun s : n.-tuple bool => (\sum_(k < n) a k * rademacher (tnth s k)) ^+ 2)
  = \sum_(k < n) a k ^+ 2.
Proof.
have E s : (\sum_(k < n) a k * rademacher (tnth s k)) ^+ 2 =
    \sum_(k < n) \sum_(l < n)
      (a k * a l) * (rademacher (tnth s k) * rademacher (tnth s l)).
  rewrite expr2 mulr_suml; apply: eq_bigr => k _.
  by rewrite mulr_sumr; apply: eq_bigr => l _; rewrite mulrACA.
under eq_fun do rewrite E.
rewrite rademacher_mean_sum; apply: eq_bigr => k _.
rewrite rademacher_mean_sum (bigD1 k)//= big1 ?addr0.
  move=> l lk.
  rewrite (rademacher_meanZ (a k * a l)
    (fun s => rademacher (tnth s k) * rademacher (tnth s l))).
  by rewrite rademacher_mean_prod eq_sym (negbTE lk) mulr0.
rewrite (rademacher_meanZ (a k * a k)
  (fun s => rademacher (tnth s k) * rademacher (tnth s k))).
by rewrite rademacher_mean_prod eqxx mulr1 expr2.
Qed.

Lemma rademacher_mean_abs_sum n (a : 'I_n -> R) :
  rm (fun s : n.-tuple bool => `|\sum_(k < n) a k * rademacher (tnth s k)|) <=
  Num.sqrt (\sum_(k < n) a k ^+ 2).
Proof.
set S := fun s : n.-tuple bool => \sum_(k < n) a k * rademacher (tnth s k).
set c := rm (fun s => `|S s|).
have c0 : 0 <= c by apply: rademacher_mean_ge0 => s; exact: normr_ge0.
(* 0 <= rm ((|S| - c)^2) = rm (S^2) - c^2 *)
have h : 0 <= rm (fun s => S s ^+ 2 + ((- 2 * c) * `|S s| + c ^+ 2)).
  apply: rademacher_mean_ge0 => s; rewrite -[S s ^+ 2]real_normK ?num_real//.
  by have := sqr_ge0 (`|S s| - c); move: `|S s| => x; lra.
rewrite rademacher_meanD rademacher_meanD in h.
rewrite (rademacher_meanZ (-2 * c) (fun s => `|S s|)) rademacher_mean_cst in h.
rewrite -/c rademacher_mean_sqr_sum in h.
rewrite -[c]ger0_norm// -sqrtr_sqr; apply: ler_wsqrtr.
by move: h; move: (\sum_(k < n) a k ^+ 2) => A; nra.
Qed.

End rademacher_theory.

Section max_norm.
Context {R : realType}.

(* The norm max_j |v_j| of 'I_m -> R. *)
Definition max_norm m (v : 'I_m -> R) : R := \big[Num.max/0]_(j < m) `|v j|.

Lemma max_norm_ge0 m (v : 'I_m -> R) : 0 <= max_norm v.
Proof. exact: bigmax0_ge0. Qed.

Lemma ler_max_norm m (v : 'I_m -> R) j : `|v j| <= max_norm v.
Proof. exact: le_bigmax. Qed.

Lemma max_normD m (u v : 'I_m -> R) :
  max_norm (fun j => u j + v j) <= max_norm u + max_norm v.
Proof.
apply: bigmax_le => [|j _]; first by rewrite addr_ge0 ?max_norm_ge0.
exact: le_trans (ler_normD _ _) (lerD (ler_max_norm u j) (ler_max_norm v j)).
Qed.

Lemma max_normN m (v : 'I_m -> R) : max_norm (fun j => - v j) = max_norm v.
Proof. by apply: eq_bigr => j _; rewrite normrN. Qed.

End max_norm.

Section measurable_max_norm.
Context d (U : measurableType d) (R : realType).

Lemma measurable_bigmax0 m (F : 'I_m -> U -> R) :
  (forall j, measurable_fun [set: U] (F j)) ->
  measurable_fun [set: U] (fun x => \big[Num.max/0]_(j < m) F j x).
Proof.
elim: m F => [|m IH] F mF.
  by under eq_fun do rewrite big_ord0; exact: measurable_cst.
under eq_fun do rewrite big_ord_recl.
apply: measurable_maxr; first exact: mF.
exact: IH (fun j => F (lift ord0 j)) (fun j => mF _).
Qed.

Lemma measurable_max_norm m (F : 'I_m -> U -> R) :
  (forall j, measurable_fun [set: U] (F j)) ->
  measurable_fun [set: U] (fun x => max_norm (fun j => F j x)).
Proof.
move=> mF; apply: measurable_bigmax0 => j.
exact: measurableT_comp (mF j).
Qed.

(* Jensen's inequality for the norm max_j |.|. *)
Lemma jensen_max_norm (P : probability U R) m (a : 'I_m -> R)
    (g : 'I_m -> U -> R) :
  (forall j, P.-integrable [set: U] (EFin \o g j)) ->
  (forall j, \int[P]_t g j t = 0) ->
  ((max_norm a)%:E <= \int[P]_t (max_norm (fun j => a j + g j t))%:E)%E.
Proof.
move=> gi g0.
set X := (\int[P]_t _)%E.
have mg j : measurable_fun [set: U] (g j).
  by apply/measurable_EFinP; exact: measurable_int (gi j).
have mag j : measurable_fun [set: U] (fun t => a j + g j t).
  by apply: measurable_funD => //; exact: measurable_cst.
have X0 : (0 <= X)%E.
  by apply: integral_ge0 => t _; rewrite lee_fin max_norm_ge0.
(* |a_j| = |E (a_j + g_j)| <= E |a_j + g_j| <= E max_norm (a + g) *)
have Xj j : ((`|a j|)%:E <= X)%E.
  have ij : P.-integrable [set: U] (EFin \o (fun t => a j + g j t)).
    have ci : P.-integrable [set: U] (EFin \o cst (a j)).
      exact: finite_measure_integrable_cst.
    have := integrableD measurableT ci (gi j).
    by apply: eq_integrable => // t _; rewrite /= EFinD.
  have -> : `|a j| = `|\int[P]_t (a j + g j t)|.
    rewrite RintegralD//; first exact: finite_measure_integrable_cst.
    rewrite g0 addr0 Rintegral_cst// -[X in fine X]/(P setT).
    by rewrite probability_setT /= mulr1.
  rewrite EFin_normr_Rintegral//.
  apply: le_trans (le_abse_integral _ _ _) _ => //.
    exact/measurable_EFinP.
  apply: ge0_le_integral => //.
  - by apply: measurableT_comp => //; exact/measurable_EFinP.
  - by apply/measurable_EFinP; exact: measurable_max_norm.
  - move=> t _; rewrite abse_EFin lee_fin.
    exact: (ler_max_norm (fun i => a i + g i t) j).
rewrite /max_norm; elim/big_rec: _ => [//|j y _ hy].
by case: (leP `|a j| y) => _.
Qed.

End measurable_max_norm.

Section swap_integral.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.

(* Exchanging two independent variables of the same law. *)
Lemma ge0_integral_swap (P : probability T R) (H : T * T -> \bar R) :
  measurable_fun [set: T * T] H -> (forall p, 0 <= H p) ->
  \int[P]_u \int[P]_t H (t, u) = \int[P]_u \int[P]_t H (u, t).
Proof.
move=> mH H0.
have F1 := fubini_tonelli1 (m1 := P) (m2 := P) _ mH H0.
have F2 := fubini_tonelli2 (m1 := P) (m2 := P) _ mH H0.
by rewrite /fubini_F /fubini_G in F1 F2; rewrite -F2 F1.
Qed.

Lemma ge0_integral_rademacher_mean (P : {measure set T -> \bar R}) n
    (F : n.-tuple bool -> T -> R) :
  (forall s, measurable_fun [set: T] (F s)) -> (forall s x, (0 <= F s x)%R) ->
  \int[P]_x (rademacher_mean (fun s => F s x))%:E =
  ((2 ^+ n)^-1)%:E * \sum_(s : n.-tuple bool) \int[P]_x (F s x)%:E.
Proof.
move=> mF F0; rewrite /rademacher_mean.
under eq_integral do rewrite EFinM.
rewrite ge0_integralZl_EFin ?invr_ge0 ?exprn_ge0//.
- by move=> x _; rewrite lee_fin sumr_ge0.
- by apply/measurable_EFinP; exact: measurable_sum.
congr (_ * _); rewrite -ge0_integral_sum//.
- by move=> s; exact/measurable_EFinP.
- by move=> s x _; rewrite lee_fin.
by apply: eq_integral => x _; rewrite sumEFin.
Qed.

Lemma measurable_rademacher_mean n (F : n.-tuple bool -> T -> R) :
  (forall s, measurable_fun [set: T] (F s)) ->
  measurable_fun [set: T] (fun x => rademacher_mean (fun s => F s x)).
Proof.
move=> mF; apply: measurable_funM; first exact: measurable_cst.
exact: measurable_sum.
Qed.

End swap_integral.

Section doubled_tuple.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.
Variables (mu : nat -> probability T R) (n : nat).

(* Two independent copies X, X' of x of law tuple_prod mu n, as the two
   blocks of a tuple of n + n coordinates. *)
Definition doubled_law (i : nat) : probability T R :=
  if (i < n)%N then mu i else mu (i - n).

Definition tuple_left (z : (n + n).-tuple T) : n.-tuple T :=
  [tuple tnth z (lshift n k) | k < n].

Definition tuple_right (z : (n + n).-tuple T) : n.-tuple T :=
  [tuple tnth z (rshift n k) | k < n].

Lemma measurable_tuple_left : measurable_fun [set: (n + n).-tuple T] tuple_left.
Proof.
apply/measurable_fun_tnthP => k /=.
apply: (eq_measurable_fun (fun z : (n + n).-tuple T => tnth z (lshift n k))).
  by move=> z _; rewrite /= /tuple_left tnth_mktuple.
exact: measurable_tnth.
Qed.

Lemma measurable_tuple_right :
  measurable_fun [set: (n + n).-tuple T] tuple_right.
Proof.
apply/measurable_fun_tnthP => k /=.
apply: (eq_measurable_fun (fun z : (n + n).-tuple T => tnth z (rshift n k))).
  by move=> z _; rewrite /= /tuple_right tnth_mktuple.
exact: measurable_tnth.
Qed.

Lemma doubled_law_left : tuple_prod doubled_law n = tuple_prod mu n.
Proof. by apply: eq_tuple_prod => i ilt; rewrite /doubled_law ilt. Qed.

Lemma doubled_law_right :
  tuple_prod (fun i => doubled_law (n + i)) n = tuple_prod mu n.
Proof.
apply: eq_tuple_prod => i ilt.
by rewrite /doubled_law ltnNge leq_addr /= addKn.
Qed.

Lemma ge0_integral_tuple_left (G : n.-tuple T -> \bar R) :
  measurable_fun [set: n.-tuple T] G -> (forall x, 0 <= G x) ->
  \int[tuple_prod doubled_law (n + n)]_z G (tuple_left z) =
  \int[tuple_prod mu n]_x G x.
Proof.
move=> mG G0; rewrite ge0_integral_tuple_prod_cat//.
  exact: measurableT_comp mG measurable_tuple_left.
rewrite doubled_law_left; apply: eq_integral => x _.
have e (y : n.-tuple T) : tuple_left [tuple of x ++ y] = x.
  by apply: eq_from_tnth => k; rewrite tnth_mktuple tnth_lshift.
under eq_integral do rewrite e.
by rewrite integral_cst// [X in _ * X]probability_setT mule1.
Qed.

Lemma ge0_integral_tuple_right (G : n.-tuple T -> \bar R) :
  measurable_fun [set: n.-tuple T] G -> (forall x, 0 <= G x) ->
  \int[tuple_prod doubled_law (n + n)]_z G (tuple_right z) =
  \int[tuple_prod mu n]_x G x.
Proof.
move=> mG G0; rewrite ge0_integral_tuple_prod_cat//.
  exact: measurableT_comp mG measurable_tuple_right.
have e (x y : n.-tuple T) : tuple_right [tuple of x ++ y] = y.
  by apply: eq_from_tnth => k; rewrite tnth_mktuple tnth_rshift.
under eq_integral do under eq_integral do rewrite e.
rewrite doubled_law_right.
by rewrite integral_cst// [X in _ * X]probability_setT mule1.
Qed.

End doubled_tuple.

Section symmetrization.
Context d (T : measurableType d) (R : realType).
Local Open Scope ereal_scope.
Variables (mu : nat -> probability T R) (n m : nat) (f : 'I_m -> T -> R).
Hypothesis mf : forall j, measurable_fun [set: T] (f j).
Hypothesis fi : forall j k, (mu k).-integrable [set: T] (EFin \o f j).


Local Lemma nu_left (k : 'I_n) : doubled_law mu n (lshift n k) = mu k.
Proof. by rewrite /doubled_law /= ltn_ord. Qed.

Local Lemma nu_right (k : 'I_n) : doubled_law mu n (rshift n k) = mu k.
Proof. by rewrite /doubled_law /= ltnNge leq_addr /= addKn. Qed.

Local Lemma mft j (i : 'I_(n + n)) :
  measurable_fun [set: (n + n).-tuple T] (fun z => f j (tnth z i)).
Proof. exact: measurableT_comp (mf j) (measurable_tnth i). Qed.

(* The sums with the coordinates k < p of the first block centered by the
   second block, the others by their means. *)
Local Definition A (p : nat) (z : (n + n).-tuple T) (j : 'I_m) : R :=
  (\sum_(k < n) (f j (tnth z (lshift n k)) -
     (if (k < p)%N then f j (tnth z (rshift n k))
      else \int[mu k]_t f j t)))%R.

Local Lemma mA p : measurable_fun [set: (n + n).-tuple T]
  (fun z => (max_norm (A p z))%:E).
Proof.
apply/measurable_EFinP; apply: measurable_max_norm => j.
apply: measurable_sum => k; apply: measurable_funB; first exact: mft.
by case: (k < p)%N; [exact: mft|exact: measurable_cst].
Qed.

Local Lemma A_set (p : 'I_n) z t j :
  A p.+1 (tuple_set z (rshift n p) t) j =
  (A p z j + (\int[mu p]_t f j t - f j t))%R.
Proof.
rewrite /A (bigD1 p)//= [in RHS](bigD1 p)//= ltnSn ltnn.
rewrite !tnth_mktuple eq_lrshift eqxx.
have -> : (\sum_(i < n | i != p)
      (f j (tnth (tuple_set z (rshift n p) t) (lshift n i)) -
       (if (i < p.+1)%N
        then f j (tnth (tuple_set z (rshift n p) t) (rshift n i))
        else \int[mu i]_t0 f j t0)) =
  \sum_(i < n | i != p)
      (f j (tnth z (lshift n i)) -
       (if (i < p)%N then f j (tnth z (rshift n i))
        else \int[mu i]_t0 f j t0)))%R.
  apply: eq_bigr => k kp; rewrite !tnth_mktuple eq_lrshift eq_rshift.
  rewrite (negbTE kp) ltnS leq_eqVlt.
  by have -> : (k == p :> nat) = false by apply/negbTE.
move: (\sum_(i < n | i != p) _)%R => S.
by move: (f j _) (f j t) (\int[mu p]_t0 f j t0)%R => a b c; ring.
Qed.

Local Lemma jensen_step (p : 'I_n) :
  \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (A p z))%:E <=
  \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (A p.+1 z))%:E.
Proof.
have A0 q z : 0 <= (max_norm (A q z))%:E by rewrite lee_fin max_norm_ge0.
rewrite [X in _ <= X](ge0_integral_tuple_prod_set _ (rshift n p) (mA p.+1)
  (A0 p.+1)).
apply: ge0_le_integral => //.
- exact: mA.
- exact: measurable_tuple_set_integral (mA p.+1) (A0 p.+1).
move=> z _; rewrite nu_right.
have E t : A p.+1 (tuple_set z (rshift n p) t) =
    (fun j => A p z j + (\int[mu p]_t0 f j t0 - f j t))%R.
  by apply/funext => j; exact: A_set.
under eq_integral do rewrite E.
apply: jensen_max_norm => j.
  have ci : (mu p).-integrable [set: T] (EFin \o cst (\int[mu p]_t f j t)%R).
    exact: finite_measure_integrable_cst.
  have := integrableB measurableT ci (fi j p).
  by apply: eq_integrable => // t _; rewrite /= EFinB.
rewrite RintegralB//; first exact: finite_measure_integrable_cst.
  exact: fi.
rewrite Rintegral_cst// -[X in fine X]/(mu p setT) probability_setT /= mulr1.
by rewrite subrr.
Qed.

(* The sums of the differences with signs. *)
Local Definition B (s : n.-tuple bool) (z : (n + n).-tuple T) (j : 'I_m) : R :=
  (\sum_(k < n) rademacher (tnth s k) *
     (f j (tnth z (lshift n k)) - f j (tnth z (rshift n k))))%R.

Local Lemma mB s : measurable_fun [set: (n + n).-tuple T]
  (fun z => (max_norm (B s z))%:E).
Proof.
apply/measurable_EFinP; apply: measurable_max_norm => j.
apply: measurable_sum => k; apply: measurable_funM; first exact: measurable_cst.
by apply: measurable_funB; exact: mft.
Qed.

Local Lemma B_set s (q : 'I_n) z t u j :
  B (sign_flip q s) (tuple_set (tuple_set z (rshift n q) u) (lshift n q) t) j =
  B s (tuple_set (tuple_set z (rshift n q) t) (lshift n q) u) j.
Proof.
rewrite /B (bigD1 q)//= [in RHS](bigD1 q)//=; congr (_ + _)%R.
  rewrite tnth_sign_flip eqxx rademacherN !tnth_mktuple eqxx eq_rlshift.
  by rewrite eqxx mulNr -mulrN opprB.
apply: eq_bigr => k kq; rewrite tnth_sign_flip (negbTE kq) !tnth_mktuple.
by rewrite !eq_lshift !eq_rlshift !eq_lrshift !eq_rshift (negbTE kq).
Qed.

Local Lemma fubini_pair (q : 'I_n) (F : (n + n).-tuple T -> \bar R) :
  measurable_fun [set: (n + n).-tuple T] F -> (forall z, 0 <= F z) ->
  \int[tuple_prod (doubled_law mu n) (n + n)]_z F z =
  \int[tuple_prod (doubled_law mu n) (n + n)]_z \int[mu q]_u \int[mu q]_t
    F (tuple_set (tuple_set z (rshift n q) u) (lshift n q) t).
Proof.
move=> mF F0.
rewrite (ge0_integral_tuple_prod_set _ (lshift n q) mF F0).
rewrite (ge0_integral_tuple_prod_set _ (rshift n q)).
- exact: measurable_tuple_set_integral mF F0.
- by move=> z; apply: integral_ge0 => t _; exact: F0.
by rewrite nu_left nu_right.
Qed.

Local Lemma swap_step s (q : 'I_n) :
  \int[tuple_prod (doubled_law mu n) (n + n)]_z
    (max_norm (B (sign_flip q s) z))%:E =
  \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (B s z))%:E.
Proof.
have B0 s' z : 0 <= (max_norm (B s' z))%:E by rewrite lee_fin max_norm_ge0.
rewrite (fubini_pair q (mB _) (B0 _)) [RHS](fubini_pair q (mB _) (B0 _)).
apply: eq_integral => z _.
have E t u : B (sign_flip q s)
    (tuple_set (tuple_set z (rshift n q) u) (lshift n q) t) =
  B s (tuple_set (tuple_set z (rshift n q) t) (lshift n q) u).
  by apply/funext => j; exact: B_set.
under eq_integral do under eq_integral do rewrite E.
pose H (p : T * T) := (max_norm
  (B s (tuple_set (tuple_set z (rshift n q) p.1) (lshift n q) p.2)))%:E.
have mH : measurable_fun [set: T * T] H.
  have mset : measurable_fun [set: T * T] (fun p : T * T =>
      tuple_set (tuple_set z (rshift n q) p.1) (lshift n q) p.2).
    apply/measurable_fun_tnthP => i /=.
    apply: (eq_measurable_fun (fun p : T * T => if i == lshift n q then p.2
        else if i == rshift n q then p.1 else tnth z i)).
      by move=> p _; rewrite /= !tnth_mktuple.
    case: (i == lshift n q); first exact: measurable_snd.
    by case: (i == rshift n q); [exact: measurable_fst|exact: measurable_cst].
  exact: measurableT_comp (mB s) mset.
exact: (ge0_integral_swap (mu q) mH (fun p => B0 _ _)).
Qed.

Theorem symmetrization :
  \int[tuple_prod mu n]_x
    (max_norm (fun j => \sum_(k < n) (f j (tnth x k) - \int[mu k]_t f j t)))%:E
  <= 2%:E * \int[tuple_prod mu n]_x
    (rademacher_mean (fun s : n.-tuple bool =>
      max_norm (fun j =>
        \sum_(k < n) rademacher (tnth s k) * f j (tnth x k))))%:E.
Proof.
have mfk j (k : 'I_n) :
    measurable_fun [set: n.-tuple T] (fun x => f j (tnth x k)).
  exact: measurableT_comp (mf j) (measurable_tnth k).
(* 1. The left side, on the first block of the doubled tuple. *)
have -> : \int[tuple_prod mu n]_x (max_norm (fun j =>
    \sum_(k < n) (f j (tnth x k) - \int[mu k]_t f j t)))%:E =
  \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (A 0 z))%:E.
  rewrite -(@ge0_integral_tuple_left _ _ _ mu n (fun x => (max_norm (fun j =>
    \sum_(k < n) (f j (tnth x k) - \int[mu k]_t f j t)))%:E)).
  - apply/measurable_EFinP; apply: measurable_max_norm => j.
    apply: measurable_sum => k.
    by apply: measurable_funB; [exact: mfk|exact: measurable_cst].
  - by move=> x; rewrite lee_fin max_norm_ge0.
  apply: eq_integral => z _; congr EFin; apply: eq_bigr => j _; congr normr.
  by apply: eq_bigr => k _; rewrite /tuple_left tnth_mktuple.
(* 2. Jensen's inequality, one coordinate of the second block at a time. *)
have chain p : (p <= n)%N ->
    \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (A 0 z))%:E <=
    \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (A p z))%:E.
  elim: p => [|p IH] pn; first by [].
  exact: le_trans (IH (ltnW pn)) (jensen_step (Ordinal pn)).
apply: le_trans (chain n (leqnn n)) _.
pose one := [tuple true | _ < n] : n.-tuple bool.
have An z : A n z = B one z.
  apply/funext => j; apply: eq_bigr => k _.
  by rewrite ltn_ord tnth_mktuple /rademacher mul1r.
under eq_integral do rewrite An.
(* 3. Every sign vector gives the same integral, one sign at a time. *)
have flips s :
    \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (B s z))%:E =
    \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (B one z))%:E.
  pose sp p := [tuple if (k < p)%N then tnth s k else true | k < n].
  have sp0 : sp 0%N = one by apply: eq_from_tnth => k; rewrite !tnth_mktuple.
  have spn : sp n = s.
    by apply: eq_from_tnth => k; rewrite tnth_mktuple ltn_ord.
  have step p (pn : (p < n)%N) :
      \int[tuple_prod (doubled_law mu n) (n + n)]_z
        (max_norm (B (sp p.+1) z))%:E =
      \int[tuple_prod (doubled_law mu n) (n + n)]_z
        (max_norm (B (sp p) z))%:E.
    case sP: (tnth s (Ordinal pn)).
      have -> : sp p.+1 = sp p.
        apply: eq_from_tnth => k; rewrite !tnth_mktuple ltnS leq_eqVlt.
        case: eqP => [kp|_] //=; rewrite kp ltnn.
        by have -> : k = Ordinal pn by exact: val_inj.
      by [].
    have -> : sp p.+1 = sign_flip (Ordinal pn) (sp p).
      apply: eq_from_tnth => k; rewrite tnth_sign_flip !tnth_mktuple ltnS.
      rewrite leq_eqVlt; case: (eqVneq k (Ordinal pn)) => [->|kp] /=.
        by rewrite eqxx ltnn sP.
      by have -> : (k == p :> nat) = false by apply/negbTE.
    exact: swap_step.
  have : forall p, (p <= n)%N ->
      \int[tuple_prod (doubled_law mu n) (n + n)]_z
        (max_norm (B (sp p) z))%:E =
      \int[tuple_prod (doubled_law mu n) (n + n)]_z
        (max_norm (B one z))%:E.
    elim => [|p IH] pn; first by rewrite sp0.
    by rewrite step// IH// ltnW.
  by move=> /(_ n (leqnn n)); rewrite spn.
(* 4. Hence the integral is that of the average over the signs. *)
have mBs s : measurable_fun [set: (n + n).-tuple T]
    (fun z => max_norm (B s z)).
  apply: measurable_max_norm => j; apply: measurable_sum => k.
  apply: measurable_funM; first exact: measurable_cst.
  by apply: measurable_funB; exact: mft.
have avg :
    \int[tuple_prod (doubled_law mu n) (n + n)]_z (max_norm (B one z))%:E =
    \int[tuple_prod (doubled_law mu n) (n + n)]_z
      (rademacher_mean (fun s => max_norm (B s z)))%:E.
  rewrite (ge0_integral_rademacher_mean _ mBs (fun s z => max_norm_ge0 _)).
  under eq_bigr do rewrite flips.
  rewrite sumr_const card_tuple card_bool.
  move: (\int[_]_z (max_norm (B one z))%:E) => I.
  have -> : (I *+ 2 ^ n)%R = ((2 ^ n)%:R)%:E * I by rewrite mule_natl.
  by rewrite muleA -EFinM natrX mulVf ?mul1e.
rewrite avg.
(* 5. The triangle inequality and the laws of the two blocks. *)
pose g (x : n.-tuple T) (s : n.-tuple bool) :=
  max_norm (fun j => \sum_(k < n) rademacher (tnth s k) * f j (tnth x k))%R.
have Ble s z :
    (max_norm (B s z) <= g (tuple_left z) s + g (tuple_right z) s)%R.
  have -> : B s z = (fun j =>
      (\sum_(k < n) rademacher (tnth s k) * f j (tnth (tuple_left z) k)) +
      - (\sum_(k < n) rademacher (tnth s k) * f j (tnth (tuple_right z) k)))%R.
    apply/funext => j; rewrite /B -sumrN -big_split; apply: eq_bigr => k _.
    by rewrite !tnth_mktuple mulrBr.
  by apply: le_trans (max_normD _ _) _; rewrite max_normN.
have mg s : measurable_fun [set: n.-tuple T] (g ^~ s).
  apply: measurable_max_norm => j; apply: measurable_sum => k.
  by apply: measurable_funM; [exact: measurable_cst|exact: mfk].
have mrg : measurable_fun [set: n.-tuple T]
    (fun x => (rademacher_mean (g x))%:E).
  by apply/measurable_EFinP; exact: measurable_rademacher_mean.
have rg0 x : 0 <= (rademacher_mean (g x))%:E.
  by rewrite lee_fin; apply: rademacher_mean_ge0 => s; exact: max_norm_ge0.
apply: (@le_trans _ _ (\int[tuple_prod (doubled_law mu n) (n + n)]_z
    ((rademacher_mean (g (tuple_left z)))%:E +
     (rademacher_mean (g (tuple_right z)))%:E))).
  apply: ge0_le_integral => //.
  - move=> z _; rewrite lee_fin.
    by apply: rademacher_mean_ge0 => s; exact: max_norm_ge0.
  - by apply/measurable_EFinP; exact: measurable_rademacher_mean.
  - apply: emeasurable_funD.
      exact: (measurableT_comp mrg (@measurable_tuple_left _ _ n)).
    exact: (measurableT_comp mrg (@measurable_tuple_right _ _ n)).
  move=> z _; rewrite -EFinD lee_fin -rademacher_meanD.
  exact: ler_rademacher_mean.
rewrite ge0_integralD//.
- exact: (measurableT_comp mrg (@measurable_tuple_left _ _ n)).
- exact: (measurableT_comp mrg (@measurable_tuple_right _ _ n)).
rewrite (ge0_integral_tuple_left mu mrg rg0).
rewrite (ge0_integral_tuple_right mu mrg rg0).
move: (\int[tuple_prod mu n]_x (rademacher_mean (g x))%:E) => I.
by rewrite -[2%:E]/(2%:R%:E) mule_natl -[X in X <= _]mulr2n.
Qed.

End symmetrization.

