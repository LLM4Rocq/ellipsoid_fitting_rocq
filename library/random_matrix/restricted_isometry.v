From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import ereal topology normedtype sequences exp.
From mathcomp Require Import measure lebesgue_measure measurable_realfun numfun.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.matrix Require Import euclidean nets.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.probability Require Import lindeberg tuple_rows.
From GaussianAnalysis.probability Require Import subgaussian conditioning.

(**md**************************************************************************)
(* # Restricted isometry of matrices with independent psi_1 columns           *)
(*                                                                            *)
(* Theorem 5.1 of Adamczak, Litvak, Pajor and Tomczak-Jaegermann (Constr.     *)
(* Approx. 2011, arXiv 0904.4723) at r = 1, with explicit constants: the      *)
(* off-diagonal part of the Gram matrix of independent centered psi_1         *)
(* vectors is small on sparse vectors. Koehler and Sohn (arXiv 2608.27372,    *)
(* lines 2192-2221) cite it for the a priori estimates of their               *)
(* Proposition 3.1.                                                           *)
(*                                                                            *)
(* Setting: x_1, ..., x_N in 'rV[R]_n are the coordinates of x of law         *)
(* tuple_prod mu N, and every linear form <x_i, y>, |y| = 1, is centered and  *)
(* subexponential with constant psi under mu i. The rows of tuple_mx x are    *)
(* the x_i, so u *m tuple_mx x = sum_i u_i x_i.                               *)
(*                                                                            *)
(* ```                                                                        *)
(*      tuple_mx x == the N x n matrix with rows x_1, ..., x_N                *)
(*          supp u == the support of u : 'rV[R]_N                             *)
(*       restr E u == u restricted to the coordinates in E                    *)
(*  gram_off x u v == <u X, v X> - sum_i u_i v_i |x_i|^2, the off-diagonal    *)
(*                    part of the Gram form, sum_(i <> j) u_i v_j <x_i, x_j>  *)
(*       maxnorm x == max_i |x_i|                                             *)
(*   sparse_ball m == the m-sparse vectors of norm at most 1                  *)
(*   rip_const m x == B_m^2 = sup over sparse_ball m of |gram_off x u u|      *)
(*    rip_T beta K == 2100 K psi sqrt m (ln (e N / m) + ln (1 / beta))        *)
(* ```                                                                        *)
(*                                                                            *)
(* Main result:                                                               *)
(* - restricted_isometry: for 1 <= m <= N, 0 < beta <= 1/2 and K >= 1, there  *)
(*   is a measurable event G with P(not G) <= 2 (log_4 m + 2)                 *)
(*   exp (- K sqrt m ln (e N / m)) on which                                   *)
(*   B_m^2 <= 256 T^2 + 32 T C + 8 beta C^2, T = rip_T beta K and             *)
(*   C = maxnorm x. Hence |u X|^2 - sum_i u_i^2 |x_i|^2 is at most this       *)
(*   bound times |u|^2 for every m-sparse u (gram_off_rip).                   *)
(*                                                                            *)
(* The proof, after ALPT with value levels instead of sorted coordinates:     *)
(* - cross_tail: for a and b with disjoint supports, |a| <= 1 and             *)
(*   |a_i| <= al, P(|<a X, b X>| > t |b X|) <= 2 exp (- min (t^2 / (64        *)
(*   psi^2), t / (4 al psi))), by Bernstein's inequality conditionally on the *)
(*   vectors in the support of b (tuple_prod_cond_le of conditioning.v);      *)
(* - gram_off_decouple: the off-diagonal form is an average of decoupled      *)
(*   forms <restr E y X, restr (F \ E) y X> over the subsets E of F;          *)
(* - the levels of z: level k collects the coordinates with                   *)
(*   4^(k-1) < m z_i^2 <= 4^k; it has at most lsize k elements, each at most  *)
(*   alpha k = 2^k / sqrt m (level_size, level_alpha), and z is the sum of    *)
(*   its restrictions to the levels (level_sum);                              *)
(* - sparse_net: nets of the vectors supported in F with sup norm at most al, *)
(*   of size exponential in |F|; small_sets_le: there are at most             *)
(*   (e N / s)^s sets of size at most s;                                      *)
(* - rip_const_le: if every decoupled diagonal term of level k and every      *)
(*   term of level k against the levels above (upper) is at most t k times    *)
(*   the norm of its second vector, then B_m^2 <= 256 T^2 + 32 T C +          *)
(*   8 beta C^2 with T = sum_k t k (the approximation by nets, the triangular *)
(*   expansion gram_off_tri and the bound A_m^2 <= B_m^2 + C^2 in place of    *)
(*   the A_m of ALPT);                                                        *)
(* - bad_event_le, conf_size, tk_exp: the union bound over the finite lists   *)
(*   wconf k and xconf k of configurations, whose sizes are at most           *)
(*   2 exp (2 H_k) with H_k = (4 m / 4^k) (9 + ln (N / m) - ln beta + 3 k)    *)
(*   (ccount_le); tk_sum: the thresholds t k sum to at most rip_T beta K.     *)
(*                                                                            *)
(* Planned: the isometry constant delta_m of tuple_mx x / sqrt n from the     *)
(* concentration of the norms |x_i|^2 / n, and the operator norm of the full  *)
(* matrix when N <= C0 n, by cutting the rows into blocks of at most n.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section columns.
Context {R : realType} (N n : nat).
Implicit Types (x : N.-tuple 'rV[R]_n) (u v a b : 'rV[R]_N).

(* The N x n matrix whose rows are the vectors of x: u *m tuple_mx x is the
   combination sum_i u_i x_i. *)
Definition tuple_mx x : 'M[R]_(N, n) := \matrix_(i, j) (tnth x i) 0 j.

Definition supp u : {set 'I_N} := [set i | u 0 i != 0].

Definition restr (E : {set 'I_N}) u : 'rV[R]_N :=
  \row_i (if i \in E then u 0 i else 0).

(* The off-diagonal part of the Gram form: <u X, v X> - sum_i u_i v_i |x_i|^2,
   that is sum_(i <> j) u_i v_j <x_i, x_j>. *)
Definition gram_off x u v : R :=
  mxdot (u *m tuple_mx x) (v *m tuple_mx x) -
  \sum_i u 0 i * v 0 i * mxdot (tnth x i) (tnth x i).

Definition maxnorm x : R := \big[Num.max/0]_i frobenius (tnth x i).

Lemma tuple_mxE x u : u *m tuple_mx x = \sum_i u 0 i *: tnth x i.
Proof.
apply/rowP => j; rewrite !mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

Lemma mxdot_tuple_mx x u v : mxdot (u *m tuple_mx x) (v *m tuple_mx x) =
  \sum_i \sum_j u 0 i * v 0 j * mxdot (tnth x i) (tnth x j).
Proof.
rewrite !tuple_mxE mxdot_suml; apply: eq_bigr => i _.
rewrite mxdot_sumr; apply: eq_bigr => j _.
by rewrite mxdotZl mxdotZr mulrA.
Qed.

Lemma gram_offE x u v : gram_off x u v =
  \sum_i \sum_(j | j != i) u 0 i * v 0 j * mxdot (tnth x i) (tnth x j).
Proof.
rewrite /gram_off mxdot_tuple_mx -sumrB; apply: eq_bigr => i _.
by rewrite (bigD1 i) //= addrC addKr.
Qed.

Lemma supp_restr E u : supp (restr E u) = E :&: supp u.
Proof.
by apply/setP => i; rewrite !inE mxE; case: (i \in E); rewrite ?eqxx.
Qed.

Lemma restrE E u i : restr E u 0 i = if i \in E then u 0 i else 0.
Proof. by rewrite mxE. Qed.

Lemma restr_supp (E : {set 'I_N}) u : supp u \subset E -> restr E u = u.
Proof.
move=> /fintype.subsetP sE; apply/rowP => i; rewrite mxE.
case: ifPn => // iE; have : i \notin supp u by apply: contra iE; exact: sE.
by rewrite inE negbK => /eqP ->.
Qed.

Lemma maxnorm_ge0 x : 0 <= maxnorm x.
Proof.
by rewrite /maxnorm; elim/big_rec: _ => // i y _ y0; rewrite le_max y0 orbT.
Qed.

Lemma card_supp0 : #|supp (0 : 'rV[R]_N)| = 0%N.
Proof. by apply: eq_card0 => i; rewrite !inE mxE eqxx. Qed.

(* u and v have disjoint supports. *)
Definition disj u v := forall i, u 0 i = 0 \/ v 0 i = 0.

(* Two vectors with disjoint supports: the diagonal terms vanish. *)
Lemma gram_off_disj x a b : disj a b ->
  gram_off x a b = mxdot (a *m tuple_mx x) (b *m tuple_mx x).
Proof.
move=> ab; rewrite /gram_off big1 ?subr0 // => i _.
by case: (ab i) => ->; rewrite ?mul0r ?mulr0 ?mul0r.
Qed.

End columns.

Section measurability.
Context {R : realType} (N n : nat).

Lemma measurable_tuple_mx_comb (a : 'rV[R]_N) :
  measurable_fun [set: N.-tuple 'rV[R]_n] (fun x => a *m tuple_mx x).
Proof.
apply/measurable_fun_mxP => i j.
under eq_fun do rewrite tuple_mxE summxE.
apply: measurable_sum => k; rewrite /=.
under eq_fun do rewrite mxE.
apply: measurable_funM; first exact: measurable_cst.
exact: measurableT_comp (measurable_mxentry _ _) (measurable_tnth k).
Qed.

Lemma measurable_mxdot_comb (f g : N.-tuple 'rV[R]_n -> 'rV[R]_n) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun [set: N.-tuple 'rV[R]_n] (fun x => mxdot (f x) (g x)).
Proof.
move=> mf mg; rewrite /mxdot.
apply: measurable_sum => i; apply: measurable_sum => j.
apply: measurable_funM.
  exact: measurableT_comp (measurable_mxentry _ _) mf.
exact: measurableT_comp (measurable_mxentry _ _) mg.
Qed.

(* The event that <a X, b X> exceeds t |b X|. *)
Definition cross_event (t : R) (a b : 'rV[R]_N) : set (N.-tuple 'rV[R]_n) :=
  [set x | t * frobenius (b *m tuple_mx x) <
           `|mxdot (a *m tuple_mx x) (b *m tuple_mx x)|].

Lemma measurable_cross_event t a b : 0 <= t -> measurable (cross_event t a b).
Proof.
move=> t0.
have key (c D : R) : 0 <= c -> (c < `|D|) = (c ^+ 2 < D ^+ 2).
  by move=> c0; rewrite -[D ^+ 2]real_normK ?num_real // ltr_pXn2r // ?nnegrE.
have -> : cross_event t a b =
    [set x | t ^+ 2 * mxdot (b *m tuple_mx x) (b *m tuple_mx x) <
             mxdot (a *m tuple_mx x) (b *m tuple_mx x) ^+ 2].
  apply/seteqP; split => x /=;
    by rewrite /cross_event /= key ?mulr_ge0 ?frobenius_ge0 //
      exprMn frobenius_sqr.
rewrite -[X in measurable X]setTI.
have mb := measurable_tuple_mx_comb b; have ma := measurable_tuple_mx_comb a.
apply: (measurable_fun_ltr _ _ measurableT) => //.
  apply: measurable_funM; first exact: measurable_cst.
  exact: measurable_mxdot_comb.
apply: measurable_funX; exact: measurable_mxdot_comb.
Qed.

End measurability.

Section cross_tail.
Context {R : realType} (N n : nat) (mu : nat -> probability 'rV[R]_n R)
  (psi : R).
Hypothesis psi0 : 0 < psi.
(* The columns are centered psi_1 vectors. *)
Hypothesis sub : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  subexponential (mu i) (fun v => mxdot v y) psi.
Hypothesis cen : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  \int[mu i]_v mxdot v y = 0.

Let coef (a : 'rV[R]_N) (k : nat) : R :=
  if insub k is Some i then a 0 i else 0.

Let coefE (a : 'rV[R]_N) (i : 'I_N) : coef a i = a 0 i.
Proof. by rewrite /coef valK. Qed.

(* Conditionally on the vectors in the support of b, <a X, b X> is a sum of
   independent centered psi_1 variables: Bernstein's inequality. *)
Lemma cross_tail (a b : 'rV[R]_N) (al t : R) : disj a b ->
  mxdot a a <= 1 -> (forall i, `|a 0 i| <= al) -> 0 < t ->
  (tuple_prod mu N (cross_event t a b) <=
   (2 * expR (- Num.min (t ^+ 2 / (64 * psi ^+ 2))
                        (t / (4 * (al * psi)))))%:E)%E.
Proof.
move=> ab a1 aal t0.
set bound := (2 * expR _)%R.
have bound0 : (0 <= bound)%R by rewrite mulr_ge0 ?expR_ge0.
pose S : {pred 'I_N} := [pred i | b 0 i != 0].
have mE : measurable (@cross_event R N n t a b).
  exact: measurable_cross_event (ltW t0).
have b0E : (0 <= bound%:E)%E by rewrite lee_fin.
(* condition on the vectors in the support of b *)
have h := @tuple_prod_cond_le _ _ R N S mu (cross_event t a b) setT
  (fun=> bound%:E) mE measurableT (measurable_cst _) (fun=> b0E)
  (fun _ _ => erefl).
rewrite setIT integral_cst // in h.
apply: (le_trans (h _)).
2: by rewrite -[X in (_ <= X)%E]mule1; apply: lee_wpmul2l => //;
  exact: probability_le1.
move=> x _.
set Y := b *m tuple_mx x.
have eb y : b *m tuple_mx (tuple_merge S x y) = Y.
  rewrite /Y !tuple_mxE; apply: eq_bigr => i _; rewrite tnth_merge.
  by case: ifPn => // /negPn /eqP ->; rewrite !scale0r.
have ea y : a *m tuple_mx (tuple_merge S x y) = a *m tuple_mx y.
  rewrite !tuple_mxE; apply: eq_bigr => i _; rewrite tnth_merge.
  case: ifPn => // /= bi; case: (ab i) => [->|/eqP]; first by rewrite !scale0r.
  by rewrite (negPf bi).
have -> : [set y | cross_event t a b (tuple_merge S x y)] =
    [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|].
  by apply/seteqP; split => y; rewrite /cross_event /= ea eb.
have [Y0|Yn0] := eqVneq Y 0.
  have -> : [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|] = set0.
    apply/seteqP; split => y //=.
    by rewrite Y0 mxdot0r frobenius0 mulr0 normr0 ltxx.
  by rewrite measure0 lee_fin.
(* <a X, Y> = |Y| sum_i a_i <x_i, u> with u = Y / |Y| *)
have r0 : 0 < frobenius Y by rewrite frobenius_gt0.
set u := (frobenius Y)^-1 *: Y.
have uu : mxdot u u = 1.
  rewrite /u mxdotZl mxdotZr -frobenius_sqr mulrA -expr2 -exprMn.
  by rewrite mulVf ?gt_eqF // expr1n.
have sY y : mxdot (a *m tuple_mx y) Y =
    frobenius Y * \sum_(i < N) coef a i * mxdot (tnth y i) u.
  rewrite tuple_mxE mxdot_suml mulr_sumr; apply: eq_bigr => i _.
  rewrite coefE mxdotZl /u mxdotZr.
  by rewrite mulrCA [frobenius Y * _]mulrA mulfV ?gt_eqF ?mul1r.
have sf i : (i < N)%N ->
    subexponential (mu i) ((fun=> fun v => mxdot v u) i) ((fun=> psi) i).
  by move=> iN; exact: sub.
have cf i : (i < N)%N -> \int[mu i]_v (fun=> fun v => mxdot v u) i v = 0.
  by move=> iN; exact: cen.
have hb := bernstein (coef a) sf cf (ltW t0).
have [a0|an0] := eqVneq a 0.
  have -> : [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|] = set0.
    apply/seteqP; split => y //=; rewrite a0 mul0mx mxdot0l normr0.
    by rewrite ltNge mulr_ge0 ?frobenius_ge0 // ltW.
  by rewrite measure0 lee_fin.
have m1 : measurable [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|].
  have -> : [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|] =
      [set y | cross_event t a b (tuple_merge S x y)].
    by apply/seteqP; split => y; rewrite /cross_event /= ea eb.
  exact: measurable_merge_section.
have mdu : measurable_fun [set: 'rV[R]_n] (fun v => mxdot v u).
  rewrite /mxdot; apply: measurable_sum => i; apply: measurable_sum => j.
  apply: measurable_funM; last exact: measurable_cst.
  exact: measurable_mxentry.
have m2 : measurable [set y : N.-tuple 'rV[R]_n |
    t <= `|\sum_(i < N) coef a i * mxdot (tnth y i) u|].
  rewrite -[X in measurable X]setTI.
  apply: (measurable_fun_ler (measurable_cst t) _ measurableT) => //.
  apply: measurableT_comp => //; apply: measurable_sum => i.
  apply: measurable_funM; first exact: measurable_cst.
  exact: measurableT_comp mdu (measurable_tnth i).
have sub12 : [set y | t * frobenius Y < `|mxdot (a *m tuple_mx y) Y|] `<=`
    [set y | t <= `|\sum_(i < N) coef a i * mxdot (tnth y i) u|].
  move=> y /=; rewrite sY normrM (ger0_norm (ltW r0)) mulrC ltr_pM2l // => h1.
  exact: ltW.
apply: le_trans (le_measure _ (mem_set m1) (mem_set m2) sub12) _.
apply: le_trans hb _; rewrite lee_fin /bound ler_pM2l // ler_expR lerN2.
(* compare the constants of Bernstein's inequality *)
have aa0 : 0 < mxdot a a by rewrite mxdot_gt0.
have sE : \sum_(i < N) coef a i ^+ 2 * psi ^+ 2 = psi ^+ 2 * mxdot a a.
  rewrite /mxdot big_ord1 mulr_sumr; apply: eq_bigr => i _.
  by rewrite coefE mulrC expr2.
have [i0 ai0] : exists i, a 0 i != 0.
  apply/existsP; apply: contraNT an0 => /existsPn h0.
  by apply/eqP/rowP => i; rewrite mxE; move/negPn/eqP: (h0 i).
have M0 : 0 < \big[maxr/0]_(i < N) (`|coef a i| * psi).
  rewrite (bigD1 i0) //= lt_max; apply/orP; left.
  by rewrite coefE mulr_gt0 // normr_gt0.
have Mle : \big[maxr/0]_(i < N) (`|coef a i| * psi) <= al * psi.
  have al0 : 0 <= al by exact: le_trans (normr_ge0 _) (aal i0).
  apply: bigmax_le; first by rewrite mulr_ge0 // ltW.
  by move=> i _; rewrite coefE ler_pM2r.
rewrite sE; set M := \big[maxr/0]_(i < N) _ in M0 Mle *.
have p2 : 0 < psi ^+ 2 by rewrite exprn_gt0.
have hA : t ^+ 2 / (64 * psi ^+ 2) <= t ^+ 2 / (64 * (psi ^+ 2 * mxdot a a)).
  rewrite ler_pM2l ?exprn_gt0 // lef_pV2 ?posrE ?mulr_gt0 //.
  by rewrite ler_pM2l // -[leRHS]mulr1 ler_pM2l.
have hB : t / (4 * (al * psi)) <= t / (4 * M).
  rewrite ler_pM2l // lef_pV2 ?posrE ?mulr_gt0 ?(lt_le_trans M0 Mle) //.
    by rewrite -(pmulr_lgt0 _ psi0); exact: lt_le_trans M0 Mle.
  by rewrite ler_pM2l.
by rewrite le_min !ge_min hA hB orbT.
Qed.

End cross_tail.

Section decoupling.
Context {R : realType} (N n : nat).
Implicit Types (x : N.-tuple 'rV[R]_n) (y : 'rV[R]_N).

(* For i <> j, a uniform random subset contains i and not j with
   probability 1/4. *)
Lemma sum_ffun_sel (i j : 'I_N) : i != j ->
  4 * \sum_(f : {ffun 'I_N -> bool}) ((f i && ~~ f j)%:R : R) = 2 ^+ N.
Proof.
move=> ij.
pose F (k : 'I_N) (b : bool) : R :=
  if k == i then b%:R else if k == j then (~~ b)%:R else 1.
have e1 (f : {ffun 'I_N -> bool}) :
    ((f i && ~~ f j)%:R : R) = \prod_k F k (f k).
  rewrite (bigD1 i) //= (bigD1 j) /=; first by rewrite eq_sym ij.
  rewrite big1 ?mulr1.
    by move=> k /andP[ki kj]; rewrite /F (negPf ki) (negPf kj).
  rewrite /F eqxx eq_sym (negPf ij) eqxx.
  by case: (f i); case: (f j); rewrite /= ?mul1r ?mul0r.
under eq_bigr do rewrite e1.
rewrite -bigA_distr_bigA /=.
have -> : 2 ^+ N = \prod_(k < N) (2 : R) by rewrite prodr_const card_ord.
rewrite (bigD1 i) //= [in RHS](bigD1 i) //= (bigD1 j) /=.
  by rewrite eq_sym ij.
rewrite [in RHS](bigD1 j) /=; first by rewrite eq_sym ij.
rewrite !big_bool /F eqxx eq_sym (negPf ij) eqxx /=.
rewrite (eq_bigr (fun=> 2)).
  by move=> k /andP[ki kj]; rewrite big_bool (negPf ki) (negPf kj).
by rewrite addr0 add0r !mul1r mulrA; congr (_ * _); ring.
Qed.

(* The off-diagonal Gram form is an average of decoupled forms. *)
Lemma gram_off_decouple x (F : {set 'I_N}) y (c : R) :
  supp y \subset F ->
  (forall E : {set 'I_N}, E \subset F ->
    `|mxdot (restr E y *m tuple_mx x)
            (restr (F :\: E) y *m tuple_mx x)| <= c) ->
  `|gram_off x y y| <= 4 * c.
Proof.
move=> sF hc.
have c0 : 0 <= c by exact: le_trans (normr_ge0 _) (hc F (subxx F)).
(* sel f true and sel f false: the restrictions to {f = 1} and {f = 0} *)
pose sel (f : {ffun 'I_N -> bool}) (s : bool) : 'rV[R]_N :=
  \row_i (if f i == s then y 0 i else 0).
have selE f s i : sel f s 0 i = ((f i == s)%:R : R) * y 0 i.
  by rewrite mxE; case: (f i == s); rewrite ?mul1r ?mul0r.
have key : 2 ^+ N * gram_off x y y =
    4 * \sum_(f : {ffun 'I_N -> bool})
      mxdot (sel f true *m tuple_mx x) (sel f false *m tuple_mx x).
  under [in RHS]eq_bigr do rewrite mxdot_tuple_mx.
  rewrite gram_offE mulr_sumr exchange_big mulr_sumr /=.
  apply: eq_bigr => i _.
  rewrite exchange_big mulr_sumr [in RHS](bigD1 i) //=.
  have -> : \sum_(f : {ffun 'I_N -> bool})
      sel f true 0 i * sel f false 0 i * mxdot (tnth x i) (tnth x i) = 0.
    rewrite big1 // => f _; rewrite !selE.
    by case: (f i) => /=; rewrite !(mul0r, mulr0).
  rewrite add0r mulr_sumr; apply: eq_bigr => j ji.
  have -> : \sum_(f : {ffun 'I_N -> bool})
      sel f true 0 i * sel f false 0 j * mxdot (tnth x i) (tnth x j) =
      \sum_(f : {ffun 'I_N -> bool}) ((f i && ~~ f j)%:R : R) *
        (y 0 i * y 0 j * mxdot (tnth x i) (tnth x j)).
    apply: eq_bigr => f _; rewrite !selE.
    by case: (f i); case: (f j) => /=; rewrite !(mul0r, mulr0, mul1r).
  rewrite -mulr_suml mulrA [RHS]mulrA sum_ffun_sel; first by rewrite eq_sym.
  by rewrite [RHS]mulrA.
have hsel (f : {ffun 'I_N -> bool}) :
    `|mxdot (sel f true *m tuple_mx x) (sel f false *m tuple_mx x)| <= c.
  have yF i : i \notin F -> y 0 i = 0.
    move=> iF; apply/eqP; apply: contraNT iF => yi.
    by apply: (fintype.subsetP sF); rewrite inE.
  have e1 : sel f true = restr [set i in F | f i] y.
    apply/rowP => i; rewrite selE restrE !inE.
    case: (f i); case: (boolP (i \in F)) => iF /=.
    - by rewrite mul1r.
    - by rewrite mul1r yF.
    - by rewrite mul0r.
    - by rewrite mul0r.
  have e2 : sel f false = restr (F :\: [set i in F | f i]) y.
    apply/rowP => i; rewrite selE restrE !inE.
    case: (f i); case: (boolP (i \in F)) => iF /=.
    - by rewrite mul0r.
    - by rewrite mul0r.
    - by rewrite mul1r.
    - by rewrite mul1r yF.
  rewrite e1 e2; apply: hc; apply/fintype.subsetP => i.
  by rewrite inE => /andP[].
have p0 : 0 < 2 ^+ N :> R by rewrite exprn_gt0.
rewrite -(ler_pM2l p0).
have -> : 2 ^+ N * `|gram_off x y y| = `|2 ^+ N * gram_off x y y|.
  by rewrite normrM (ger0_norm (ltW p0)).
rewrite key normrM (ger0_norm (ler0n _ 4)) mulrCA ler_pM2l ?ltr0n //.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (ler_sum _ (fun f _ => hsel f)) _.
rewrite sumr_const card_ffun card_bool card_ord -mulr_natl.
by rewrite -[c *+ 2 ^ N]mulr_natl natrX mulr1.
Qed.

End decoupling.

Section sparse_nets.
Context {R : realType} (N : nat).

(* The vectors supported in F of norm at most 1 with coordinates at most al
   in absolute value. *)
Definition sball (F : {set 'I_N}) (al : R) : set 'rV[R]_N :=
  [set y | [/\ supp y \subset F, mxdot y y <= 1 & forall i, `|y 0 i| <= al]].

Section embedding.
Variable F : {set 'I_N}.

(* The coordinates of F, in the order of enum_val. *)
Let emb (w : 'cV[R]_#|F|) : 'rV[R]_N := \sum_j w j 0 *: delta_mx 0 (enum_val j).
Let proj (z : 'rV[R]_N) : 'cV[R]_#|F| := \col_j z 0 (enum_val j).

Let embE w i : emb w 0 i = \sum_j w j 0 * (enum_val j == i)%:R.
Proof.
rewrite /emb summxE; apply: eq_bigr => j _.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Let emb_val w j : emb w 0 (enum_val j) = w j 0.
Proof.
rewrite embE (bigD1 j) //= eqxx mulr1 big1 ?addr0 // => k kj.
by rewrite (inj_eq enum_val_inj) (negPf kj) mulr0.
Qed.

Let emb_out w i : i \notin F -> emb w 0 i = 0.
Proof.
move=> iF; rewrite embE big1 // => j _.
case: eqP => [ji|]; last by rewrite mulr0.
by move: iF; rewrite -ji enum_valP.
Qed.

Let emb_dot w w' : mxdot (emb w) (emb w') = mxdot w w'.
Proof.
transitivity (\sum_(j < #|F|) emb w 0 (enum_val j) * emb w' 0 (enum_val j)).
  rewrite /mxdot big_ord1 (bigID (mem F)) /= [X in _ + X]big1 ?addr0.
    by move=> i iF; rewrite emb_out ?mul0r.
  by rewrite big_enum_val.
rewrite /mxdot; apply: eq_bigr => j _.
by rewrite big_ord1 !emb_val.
Qed.

Lemma emb_proj z : supp z \subset F -> emb (proj z) = z.
Proof.
move=> sF; apply/rowP => i; rewrite embE.
case: (boolP (i \in F)) => iF.
  rewrite (bigD1 (enum_rank_in iF i)) //= enum_rankK_in // eqxx mulr1.
  rewrite big1 ?addr0 ?mxE ?enum_rankK_in // => j ji.
  case: eqP => [e|]; last by rewrite mulr0.
  have h := enum_valK_in iF j; rewrite e in h.
  by rewrite h eqxx in ji.
have -> : z 0 i = 0.
  apply/eqP; apply: contraNT iF => zi.
  by apply: (fintype.subsetP sF); rewrite inE.
rewrite big1 // => j _; case: eqP => [ji|]; last by rewrite mulr0.
by move: iF; rewrite -ji enum_valP.
Qed.

Let embB w w' : emb (w - w') = emb w - emb w'.
Proof.
rewrite /emb -sumrB; apply: eq_bigr => j _.
by rewrite !mxE scalerBl.
Qed.

Let proj_dot z : supp z \subset F -> mxdot (proj z) (proj z) = mxdot z z.
Proof. by move=> sF; rewrite -emb_dot emb_proj. Qed.

(* A net of the sparse vectors supported in F, of size exponential in |F|. *)
Lemma sparse_net (al eps : R) : 0 <= al -> 0 < eps ->
  exists S : seq 'rV[R]_N, [/\ forall y, y \in S -> sball F al y,
    forall z, sball F al z ->
      exists2 y, y \in S & mxdot (z - y) (z - y) <= eps ^+ 2 &
    (size S)%:R <= (2 * expR 1 * (1 + 2 / eps)) ^+ #|F|].
Proof.
move=> al0 e0.
pose SF : set 'cV[R]_#|F| :=
  [set w | mxdot w w <= 1 /\ forall j, `|w j 0| <= al].
have SFr w : SF w -> frobenius w <= 1.
  by move=> [w1 _]; rewrite /frobenius -sqrtr1 ler_sqrt.
have [M [MS SM Msize]] := net_exists ler01 e0 SFr.
rewrite mulr1 in Msize.
exists (map emb M); split.
- move=> y /mapP [w wM ->]; have [w1 wal] := MS w wM; split.
  + apply/fintype.subsetP => i; rewrite inE; apply: contraR => iF.
    by rewrite emb_out.
  + by rewrite emb_dot.
  + move=> i; case: (boolP (i \in F)) => iF; last by rewrite emb_out ?normr0.
    by rewrite -(enum_rankK_in iF iF) emb_val.
- move=> z [sF z1 zal].
  have Pz : SF (proj z).
    split; first by rewrite proj_dot.
    by move=> j; rewrite mxE.
  have [w wM hw] := SM _ Pz.
  exists (emb w); first exact: map_f.
  rewrite -[z in z - _](emb_proj sF) -embB emb_dot -frobenius_sqr.
  by rewrite lerXn2r // ?nnegrE ?frobenius_ge0 // ltW.
- by rewrite size_map.
Qed.

End embedding.

End sparse_nets.

Section counting.
Context {R : realType}.

Lemma card_small_sets N s :
  #|[set F : {set 'I_N} | (#|F| <= s)%N]%SET| = (\sum_(j < s.+1) 'C(N, j))%N.
Proof.
elim: s => [|s IH].
  rewrite big_ord1 -[in RHS](card_ord N) -(card_draws 'I_N 0).
  by apply: eq_card => F; rewrite !inE leqn0.
rewrite big_ord_recr /= -IH.
have -> : [set F : {set 'I_N} | (#|F| <= s.+1)%N]%SET =
    ([set F : {set 'I_N} | (#|F| <= s)%N] :|:
     [set F : {set 'I_N} | #|F| == s.+1])%SET.
  by apply/setP => F; rewrite !inE leq_eqVlt ltnS orbC.
rewrite cardsU.
have -> : #|([set F : {set 'I_N} | (#|F| <= s)%N] :&:
    [set F : {set 'I_N} | #|F| == s.+1])%SET| = 0%N.
  apply: eq_card0 => F; rewrite !inE.
  by case: (boolP (#|F| == s.+1)) => [/eqP ->|]; rewrite ?ltnn ?andbF ?andbT.
by rewrite subn0 (card_draws 'I_N) card_ord.
Qed.

(* There are at most (e N / s)^s subsets of size at most s. *)
Lemma small_sets_le N s : (0 < s)%N -> (s <= N)%N ->
  (#|[set F : {set 'I_N} | (#|F| <= s)%N]%SET|)%:R <=
  (expR 1 * N%:R / s%:R) ^+ s :> R.
Proof.
move=> s0 sN.
have N0 : (0 < N)%N by apply: leq_trans sN.
rewrite card_small_sets natr_sum.
(* weight the binomial coefficients by l^(j - s), l = s / N <= 1 *)
set l : R := s%:R / N%:R.
have l0 : 0 < l by rewrite divr_gt0 ?ltr0n.
have l1 : l <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r ler_nat.
have step1 : \sum_(j < s.+1) ('C(N, j))%:R <=
    l ^- s * \sum_(j < s.+1) ('C(N, j))%:R * l ^+ j :> R.
  rewrite mulr_sumr; apply: ler_sum => j _.
  rewrite mulrCA -[X in X <= _]mulr1 ler_wpM2l ?ler0n //.
  have js : (j <= s)%N by rewrite -ltnS.
  rewrite -(ler_pM2l (exprn_gt0 s l0)) mulr1 mulrA mulfV ?expf_neq0 ?gt_eqF //.
  by rewrite mul1r; apply: ler_wiXn2l => //; rewrite ltW.
have step2 : \sum_(j < s.+1) ('C(N, j))%:R * l ^+ j <= (l + 1) ^+ N.
  rewrite exprD1n (big_ord_widen N.+1 (fun j => ('C(N, j))%:R * l ^+ j)) //.
  rewrite [leLHS]big_mkcond /=; apply: ler_sum => j _.
  case: ifP => _; first by rewrite mulr_natl.
  by rewrite mulrn_wge0 // exprn_ge0 // ltW.
have step3 : (l + 1) ^+ N <= expR (s%:R) :> R.
  apply: le_trans (_ : expR l ^+ N <= _).
    have h1 : 0 <= l + 1 by rewrite addr_ge0 // ltW.
    by rewrite lerXn2r ?nnegrE ?expR_ge0 // addrC expR_ge1Dx.
  by rewrite -expRM_natr /l mulfVK ?pnatr_eq0 -?lt0n.
apply: le_trans step1 _.
have ls0 : 0 <= l ^- s by rewrite invr_ge0 exprn_ge0 // ltW.
apply: le_trans (ler_wpM2l ls0 (le_trans step2 step3)) _.
rewrite -[s%:R]mulr1 expRM_natl -exprVn invf_div -exprMn.
by rewrite mulr1 mulrC mulrA.
Qed.

End counting.

Section gram_off_props.
Context {R : realType} (N n : nat) (x : N.-tuple 'rV[R]_n).
Implicit Types (u v w : 'rV[R]_N).

Lemma gram_offC u v : gram_off x u v = gram_off x v u.
Proof.
rewrite /gram_off mxdotC; congr (_ - _); apply: eq_bigr => i _.
by rewrite (mulrC (u 0 i)).
Qed.

Lemma gram_offDl u v w : gram_off x (u + v) w = gram_off x u w + gram_off x v w.
Proof.
rewrite /gram_off mulmxDl mxdotDl.
rewrite (eq_bigr (fun i => u 0 i * w 0 i * mxdot (tnth x i) (tnth x i) +
  v 0 i * w 0 i * mxdot (tnth x i) (tnth x i))).
  by move=> i _; rewrite mxE !mulrDl.
by rewrite big_split /=; ring.
Qed.

Lemma gram_offZl a u w : gram_off x (a *: u) w = a * gram_off x u w.
Proof.
rewrite /gram_off -scalemxAl mxdotZl mulrBr; congr (_ - _).
by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite mxE !mulrA.
Qed.

Lemma gram_off0l w : gram_off x 0 w = 0.
Proof. by have := gram_offZl 0 0 w; rewrite scale0r mul0r. Qed.

Lemma gram_off_suml (I : Type) (r : seq I) (P : pred I)
    (F : I -> 'rV[R]_N) w :
  gram_off x (\sum_(i <- r | P i) F i) w =
  \sum_(i <- r | P i) gram_off x (F i) w.
Proof.
elim/big_rec2: _ => [|i y1 y2 _ <-]; first exact: gram_off0l.
by rewrite gram_offDl.
Qed.

Lemma gram_offDr u v w : gram_off x u (v + w) = gram_off x u v + gram_off x u w.
Proof. by rewrite gram_offC gram_offDl !(gram_offC u). Qed.

Lemma gram_off_sumr (I : Type) (r : seq I) (P : pred I)
    (F : I -> 'rV[R]_N) u :
  gram_off x u (\sum_(i <- r | P i) F i) =
  \sum_(i <- r | P i) gram_off x u (F i).
Proof.
rewrite gram_offC gram_off_suml; apply: eq_bigr => i _; exact: gram_offC.
Qed.

(* The diagonal part is bounded by the largest squared norm of the x_i. *)
Lemma diag_part_le u v :
  `|\sum_i u 0 i * v 0 i * mxdot (tnth x i) (tnth x i)| <=
  maxnorm x ^+ 2 * (frobenius u * frobenius v).
Proof.
have C0 := maxnorm_ge0 x.
have Xi i : mxdot (tnth x i) (tnth x i) <= maxnorm x ^+ 2.
  rewrite -frobenius_sqr lerXn2r ?nnegrE ?frobenius_ge0 //.
  by rewrite /maxnorm (bigD1 i) //= le_max lexx.
apply: le_trans (ler_norm_sum _ _ _) _.
apply: le_trans (_ : \sum_i maxnorm x ^+ 2 * (`|u 0 i| * `|v 0 i|) <= _).
  apply: ler_sum => i _; rewrite !normrM (ger0_norm (mxdot_ge0 _)) mulrC.
  by rewrite ler_wpM2r ?mulr_ge0.
rewrite -mulr_sumr ler_wpM2l ?exprn_ge0 //.
(* Cauchy-Schwarz for the vectors of absolute values *)
pose au : 'rV[R]_N := map_mx normr u.
pose av : 'rV[R]_N := map_mx normr v.
have fa (y : 'rV[R]_N) : frobenius (map_mx normr y) = frobenius y.
  rewrite /frobenius /mxdot; congr Num.sqrt; apply: eq_bigr => i _.
  by apply: eq_bigr => j _; rewrite mxE -normrM ger0_norm // -expr2 sqr_ge0.
have := ler_mxdot au av; rewrite !fa /mxdot big_ord1.
by under eq_bigr do rewrite !mxE.
Qed.

End gram_off_props.

Section rip_constant.
Context {R : realType} (N n m : nat) (x : N.-tuple 'rV[R]_n).

(* The m-sparse vectors of the unit ball. *)
Definition sparse_ball : set 'rV[R]_N :=
  [set u | (#|supp u| <= m)%N /\ mxdot u u <= 1].

(* B_m^2 of Adamczak, Litvak, Pajor and Tomczak-Jaegermann: the largest
   off-diagonal part of |sum_i u_i x_i|^2 over the m-sparse unit vectors. *)
Definition rip_const : R := sup [set `|gram_off x u u| | u in sparse_ball].

Lemma has_sup_rip : has_sup [set `|gram_off x u u| | u in sparse_ball].
Proof.
split; first by exists `|gram_off x 0 0|, 0 => //; split;
  [rewrite card_supp0|rewrite mxdot0l ler01].
exists (\sum_i \sum_j `|mxdot (tnth x i) (tnth x j)|) => _ [u [_ u1] <-].
have ui i : `|u 0 i| <= 1.
  have h := le_trans (mxdot_entry u 0 i) u1.
  rewrite -(ler_pXn2r (n := 2)) // ?nnegrE // expr1n.
  by rewrite real_normK ?num_real.
rewrite gram_offE; apply: le_trans (ler_norm_sum _ _ _) _.
apply: ler_sum => i _; apply: le_trans (ler_norm_sum _ _ _) _.
rewrite [leRHS](bigD1 i) //= -[X in X <= _]add0r lerD ?normr_ge0 //.
apply: ler_sum => j _; rewrite !normrM -[X in _ <= X]mul1r ler_wpM2r //.
by rewrite -[1]mulr1 ler_pM ?normr_ge0.
Qed.

Lemma rip_const_ge0 : 0 <= rip_const.
Proof.
apply: le_trans (normr_ge0 (gram_off x 0 0)) _.
apply: ub_le_sup; first exact: has_sup_rip.2.
by exists 0 => //; split; [rewrite card_supp0|rewrite mxdot0l ler01].
Qed.

Lemma supp_scale (a : R) (u : 'rV[R]_N) : a != 0 -> supp (a *: u) = supp u.
Proof. by move=> a0; apply/setP => i; rewrite !inE mxE mulf_eq0 negb_or a0. Qed.

(* Homogeneity: |gram_off x u u| <= B_m^2 |u|^2 for every m-sparse u. *)
Lemma gram_off_rip (u : 'rV[R]_N) : (#|supp u| <= m)%N ->
  `|gram_off x u u| <= rip_const * mxdot u u.
Proof.
move=> um.
have [->|u0] := eqVneq u 0.
  by rewrite gram_off0l normr0 mxdot0l mulr0.
have f0 : 0 < frobenius u by rewrite frobenius_gt0.
set v := (frobenius u)^-1 *: u.
have vv : mxdot v v = 1.
  rewrite /v mxdotZl mxdotZr -frobenius_sqr mulrA -expr2 -exprMn.
  by rewrite mulVf ?gt_eqF // expr1n.
have vB : sparse_ball v.
  by split; [rewrite supp_scale ?invr_eq0 ?gt_eqF|rewrite vv].
have h : `|gram_off x v v| <= rip_const.
  by apply: (ub_le_sup has_sup_rip.2); exists v.
have uE : u = frobenius u *: v by rewrite /v scalerA mulfV ?gt_eqF ?scale1r.
have -> : gram_off x u u = frobenius u ^+ 2 * gram_off x v v.
  by rewrite {1 2}uE gram_offZl gram_offC gram_offZl mulrA -expr2.
rewrite normrM (ger0_norm (exprn_ge0 _ (ltW f0))) frobenius_sqr mulrC.
by rewrite ler_wpM2r ?mxdot_ge0.
Qed.

Lemma tuple_mx_rip (u : 'rV[R]_N) : (#|supp u| <= m)%N ->
  frobenius (u *m tuple_mx x) <=
  Num.sqrt (rip_const + maxnorm x ^+ 2) * frobenius u.
Proof.
move=> um.
have h1 : mxdot (u *m tuple_mx x) (u *m tuple_mx x) <=
    (rip_const + maxnorm x ^+ 2) * mxdot u u.
  have -> : mxdot (u *m tuple_mx x) (u *m tuple_mx x) = gram_off x u u +
      \sum_i u 0 i * u 0 i * mxdot (tnth x i) (tnth x i).
    by rewrite /gram_off subrK.
  rewrite mulrDl; apply: lerD.
    exact: le_trans (ler_norm _) (gram_off_rip um).
  apply: le_trans (ler_norm _) _; apply: le_trans (diag_part_le _ _ _) _.
  by rewrite -expr2 frobenius_sqr.
have C0 := maxnorm_ge0 x.
rewrite /frobenius -sqrtrM ?addr_ge0 ?rip_const_ge0 ?exprn_ge0 //.
exact: ler_wsqrtr.
Qed.

Lemma gram_off_rip2 (u v : 'rV[R]_N) :
  (#|supp u| <= m)%N -> (#|supp v| <= m)%N ->
  `|gram_off x u v| <=
  (rip_const + 2 * maxnorm x ^+ 2) * (frobenius u * frobenius v).
Proof.
move=> um vm.
rewrite /gram_off; apply: le_trans (ler_normB _ _) _.
have hB : 0 <= rip_const + maxnorm x ^+ 2.
  by rewrite addr_ge0 ?rip_const_ge0 ?sqr_ge0.
have h1 : `|mxdot (u *m tuple_mx x) (v *m tuple_mx x)| <=
    (rip_const + maxnorm x ^+ 2) * (frobenius u * frobenius v).
  apply: le_trans (mxdot_le _ _) _.
  rewrite -[rip_const + _](sqr_sqrtr hB) expr2 mulrACA.
  by rewrite ler_pM ?frobenius_ge0 ?tuple_mx_rip.
have -> : (rip_const + 2 * maxnorm x ^+ 2) * (frobenius u * frobenius v) =
    (rip_const + maxnorm x ^+ 2) * (frobenius u * frobenius v) +
    maxnorm x ^+ 2 * (frobenius u * frobenius v) by ring.
by apply: lerD; [exact: h1|exact: diag_part_le].
Qed.

End rip_constant.

Section levels.
Context {R : realType} (N m : nat).
Implicit Types (z : 'rV[R]_N).

(* Level k of z collects the coordinates with 4^(k-1) < m z_i^2 <= 4^k
   (0 < m z_i^2 <= 1 for k = 0): it has at most lsize k elements, each at
   most alpha k = 2^k / sqrt m in absolute value. *)
Definition lvl_lo (k : nat) : R := if k is k'.+1 then 4 ^+ k' else 0.

Definition level z k : {set 'I_N} :=
  [set i | lvl_lo k < m%:R * z 0 i ^+ 2 <= 4 ^+ k].

Definition lsize k : nat := if k is k'.+1 then (m %/ 4 ^ k')%N else m.

Definition alpha k : R := 2 ^+ k / Num.sqrt m%:R.

Lemma lvl_lo_ge0 k : 0 <= lvl_lo k.
Proof. by case: k => [|k] //=; rewrite exprn_ge0. Qed.

Lemma level_supp z k : level z k \subset supp z.
Proof.
apply/fintype.subsetP => i; rewrite !inE => /andP[h _].
apply/eqP => zi; move: h; rewrite zi expr0n /= mulr0.
by rewrite ltNge lvl_lo_ge0.
Qed.

Lemma level_uniq z k k' i : i \in level z k -> i \in level z k' -> k = k'.
Proof.
rewrite !inE => /andP[a1 a2] /andP[b1 b2].
have key j j' : (j < j')%N -> lvl_lo j' < m%:R * z 0 i ^+ 2 ->
    m%:R * z 0 i ^+ 2 <= 4 ^+ j -> False.
  case: j' => // j' jj' h1 h2.
  have h3 : (4 : R) ^+ j <= 4 ^+ j' by rewrite ler_eXn2l // ltr1n.
  by have := lt_le_trans h1 (le_trans h2 h3); rewrite ltxx.
case: (ltngtP k k') => // kk; exfalso.
  exact: key kk b1 a2.
exact: key kk a1 b2.
Qed.

Lemma level_cover z l : (0 < m)%N -> mxdot z z <= 1 -> (m <= 4 ^ l)%N ->
  forall i, z 0 i != 0 -> exists2 k, (k <= l)%N & i \in level z k.
Proof.
move=> m0 z1 ml i zi.
set q := m%:R * z 0 i ^+ 2.
have q0 : 0 < q.
  by rewrite mulr_gt0 ?ltr0n // lt0r sqr_ge0 andbT sqrf_eq0.
have ql : q <= 4 ^+ l.
  apply: (@le_trans _ _ m%:R).
    rewrite -[leRHS]mulr1 ler_wpM2l ?ler0n //.
    exact: le_trans (mxdot_entry z 0 i) z1.
  by rewrite -natrX ler_nat.
(* the least k with q <= 4^k *)
have exP : exists k, q <= 4 ^+ k by exists l.
case: (ex_minnP exP) => k Pk mink.
exists k; first exact: mink.
rewrite inE Pk andbT; case: k Pk mink => [|k] Pk mink //=.
by rewrite ltNge; apply/negP => /mink; rewrite ltnn.
Qed.

Lemma level_size z k : (#|supp z| <= m)%N -> mxdot z z <= 1 ->
  (#|level z k| <= lsize k)%N.
Proof.
move=> zm z1; case: k => [|k] /=.
  exact: leq_trans (subset_leq_card (level_supp z 0)) zm.
(* |level| 4^k <= sum over the level of m z_i^2 <= m |z|^2 <= m *)
rewrite leq_divRL ?expn_gt0 // -(ler_nat R) natrM natrX.
have -> : (#|level z k.+1|%:R * 4 ^+ k : R) = \sum_(i in level z k.+1) 4 ^+ k.
  by rewrite sumr_const mulr_natl.
apply: (@le_trans _ _ (\sum_(i in level z k.+1) m%:R * z 0 i ^+ 2)).
  by apply: ler_sum => i; rewrite inE => /andP[/ltW].
apply: (@le_trans _ _ (\sum_i m%:R * z 0 i ^+ 2)).
  rewrite [leRHS](bigID (mem (level z k.+1))) /= lerDl.
  by apply: sumr_ge0 => i _; rewrite mulr_ge0 ?ler0n ?sqr_ge0.
rewrite -mulr_sumr -[leRHS]mulr1 ler_wpM2l ?ler0n //.
apply: le_trans z1; rewrite /mxdot big_ord1.
by apply: ler_sum => i _; rewrite expr2.
Qed.

Lemma level_alpha z k i : (0 < m)%N -> i \in level z k -> `|z 0 i| <= alpha k.
Proof.
move=> m0; rewrite inE => /andP[_ h].
have sm : 0 < Num.sqrt m%:R :> R by rewrite sqrtr_gt0 ltr0n.
have a0 : 0 <= alpha k by rewrite /alpha divr_ge0 ?exprn_ge0 // ltW.
rewrite -(ler_pXn2r (n := 2)) ?nnegrE //.
rewrite real_normK ?num_real // /alpha expr_div_n sqr_sqrtr ?ler0n //.
have e : (2 : R) ^+ k ^+ 2 = 4 ^+ k.
  by rewrite -exprM mulnC exprM; congr (_ ^+ _); ring.
by rewrite e ler_pdivlMr ?ltr0n // mulrC.
Qed.

Lemma level_sum z l : (0 < m)%N -> mxdot z z <= 1 -> (m <= 4 ^ l)%N ->
  z = \sum_(k < l.+1) restr (level z k) z.
Proof.
move=> m0 z1 ml; apply/rowP => i; rewrite summxE.
under eq_bigr do rewrite restrE.
have [zi|zi] := eqVneq (z 0 i) 0.
  by rewrite zi big1 // => k _; case: ifP.
have [k kl ik] := level_cover m0 z1 ml zi.
rewrite (bigD1 (Ordinal (n := l.+1) (m := k) kl)) //= ik big1 ?addr0 //.
move=> k' kk'; case: ifP => // ik'; move: kk'; rewrite -val_eqE /=.
by rewrite (level_uniq ik' ik) eqxx.
Qed.

End levels.

Section supports.
Context {R : realType} (N : nat).
Implicit Types (u v : 'rV[R]_N) (S : {set 'I_N}).

(* u vanishes outside S. *)
Definition supported S u := forall i, i \notin S -> u 0 i = 0.

Lemma supportedP S u : supported S u <-> supp u \subset S.
Proof.
split=> [h|/fintype.subsetP h i iS].
  apply/fintype.subsetP => i; rewrite inE; apply: contraR => iS.
  by rewrite h.
by apply/eqP; apply: contraNT iS => ui; apply: h; rewrite inE.
Qed.

Lemma supported_sum (I : Type) (r : seq I) (P : pred I) (F : I -> 'rV[R]_N) S :
  (forall i, P i -> supported S (F i)) -> supported S (\sum_(i <- r | P i) F i).
Proof.
move=> h j jS; rewrite summxE.
by rewrite big1 // => i Pi; exact: h.
Qed.

Lemma supportedB S u v : supported S u -> supported S v -> supported S (u - v).
Proof. by move=> hu hv i iS; rewrite !mxE hu ?hv ?subr0. Qed.

Lemma supported_restr S E u : supported S u -> supported S (restr E u).
Proof. by move=> h i iS; rewrite restrE h //; case: ifP. Qed.

Lemma supported_restrE E u : supported E (restr E u).
Proof. by move=> i iE; rewrite restrE (negPf iE). Qed.

Lemma supported_sub S S' u : S \subset S' -> supported S u -> supported S' u.
Proof.
move=> /fintype.subsetP sS h i iS'; apply: h; apply: contra iS'.
exact: sS.
Qed.

Lemma supported_card S u (m : nat) : supported S u -> (#|S| <= m)%N ->
  (#|supp u| <= m)%N.
Proof.
move=> /supportedP h; exact: leq_trans (subset_leq_card h).
Qed.

Lemma disj_supported S S' u v : supported S u -> supported S' v ->
  (forall i, i \in S -> i \in S' -> False) -> disj u v.
Proof.
move=> hu hv h i; case: (boolP (i \in S)) => iS; last by left; exact: hu.
by right; apply: hv; apply/negP; exact: h.
Qed.

Lemma mxdot_disj u v : disj u v -> mxdot u v = 0.
Proof.
move=> h; rewrite /mxdot big_ord1 big1 // => i _.
by case: (h i) => ->; rewrite ?mul0r ?mulr0.
Qed.

Lemma mxdot_restr E u : mxdot (restr E u) (restr E u) <= mxdot u u.
Proof.
rewrite /mxdot !big_ord1; apply: ler_sum => i _; rewrite restrE.
by case: ifP => _; rewrite ?mulr0 // -expr2 sqr_ge0.
Qed.

(* Pythagoras for vectors with pairwise disjoint supports. *)
Lemma mxdot_sum_disj (I : eqType) (r : seq I) (F : I -> 'rV[R]_N) : uniq r ->
  (forall i j, i != j -> disj (F i) (F j)) ->
  mxdot (\sum_(i <- r) F i) (\sum_(i <- r) F i) =
  \sum_(i <- r) mxdot (F i) (F i).
Proof.
elim: r => [|i r IH] /=; first by rewrite !big_nil mxdot0l.
move=> /andP[ir ur] h; rewrite !big_cons mxdotDl !mxdotDr IH //.
have -> : mxdot (F i) (\sum_(j <- r) F j) = 0.
  rewrite mxdot_sumr big1_seq // => j /andP[_ jr]; apply: mxdot_disj; apply: h.
  by apply: contraNneq ir => ->.
rewrite mxdotC.
have -> : mxdot (F i) (\sum_(j <- r) F j) = 0.
  rewrite mxdot_sumr big1_seq // => j /andP[_ jr]; apply: mxdot_disj; apply: h.
  by apply: contraNneq ir => ->.
by rewrite addr0 add0r.
Qed.

End supports.

Section triangular.
Context {R : realType} (N n : nat) (x : N.-tuple 'rV[R]_n).

(* The form of a sum: the diagonal terms and twice the terms of each vector
   against the sum of the later ones. *)
Lemma gram_off_tri (a : nat -> 'rV[R]_N) k L : (k <= L)%N ->
  gram_off x (\sum_(k <= r < L) a r) (\sum_(k <= r < L) a r) =
  \sum_(k <= j < L) (gram_off x (a j) (a j) +
    2 * gram_off x (a j) (\sum_(j.+1 <= r < L) a r)).
Proof.
move=> kL; have [d ->] : exists d, L = (k + d)%N.
  by exists (L - k)%N; rewrite subnKC.
elim: d k {kL} => [|d IH] k.
  by rewrite addn0 !big_geq // gram_off0l.
rewrite addnS big_ltn ?ltnS ?leq_addr // [in RHS]big_ltn ?ltnS ?leq_addr //.
have e : (k + d).+1 = (k.+1 + d)%N by rewrite addSn.
rewrite e gram_offDl !gram_offDr IH.
rewrite [gram_off x (\sum_(_ <= _ < _) _) (a k)]gram_offC.
ring.
Qed.

End triangular.

Section deterministic.
Context {R : realType} (N n m l : nat) (x : N.-tuple 'rV[R]_n).
Hypotheses (m0 : (0 < m)%N) (ml : (m <= 4 ^ l)%N).
Variables (eps t : nat -> R) (beta : R).
Variable nt : nat -> {set 'I_N} -> seq 'rV[R]_N.
(* nt k F is a net of mesh eps k of the vectors supported in F of norm at most
   1 and coordinates at most alpha k. *)
Hypothesis ntP : forall k F y, y \in nt k F -> sball F (alpha m k) y.
Hypothesis ntN : forall k F z, sball F (alpha m k) z ->
  exists2 y, y \in nt k F & mxdot (z - y) (z - y) <= eps k ^+ 2.
Hypothesis eps_sum : \sum_(0 <= k < l.+1) eps k ^+ 2 <= beta ^+ 2 / 9.
Hypotheses (beta0 : 0 <= beta) (beta1 : beta <= 1 / 2).
Hypothesis t0 : forall k, 0 <= t k.

(* The sums of net points of the levels above k. *)
Definition upper (k : nat) (v : 'rV[R]_N) := exists yr : nat -> 'rV[R]_N,
  (forall r, (k < r <= l)%N ->
    exists2 F : {set 'I_N}, (#|F| <= lsize m r)%N & yr r \in nt r F) /\
  v = \sum_(k.+1 <= r < l.+1) yr r.

(* The complement of the bad events of the union bound. *)
Hypothesis goodW : forall k (F E : {set 'I_N}) y, (k <= l)%N ->
  (#|F| <= lsize m k)%N -> E \subset F -> y \in nt k F ->
  `|mxdot (restr E y *m tuple_mx x) (restr (F :\: E) y *m tuple_mx x)| <=
  t k * frobenius (restr (F :\: E) y *m tuple_mx x).
Hypothesis goodX : forall k (F : {set 'I_N}) y v, (k <= l)%N ->
  (#|F| <= lsize m k)%N -> y \in nt k F -> upper k v ->
  `|mxdot (y *m tuple_mx x) (restr (~: F) v *m tuple_mx x)| <=
  t k * frobenius (restr (~: F) v *m tuple_mx x).

Lemma gram_off_ball z : sparse_ball m z ->
  `|gram_off x z z| <=
  8 * (\sum_(0 <= k < l.+1) t k) * Num.sqrt (rip_const m x + maxnorm x ^+ 2) +
  beta * (rip_const m x + 2 * maxnorm x ^+ 2).
Proof.
move=> [zm z1].
set B := rip_const m x; set C := maxnorm x.
have B0 : 0 <= B := rip_const_ge0 m x.
have C0 : 0 <= C := maxnorm_ge0 x.
set S := B + C ^+ 2.
have S0 : 0 <= S by rewrite addr_ge0 ?sqr_ge0.
(* the levels of z and the restrictions of z to them *)
set L := level m z.
pose zk k := restr (L k) z.
have zkB k : sball (L k) (alpha m k) (zk k).
  split.
  - by apply/supportedP; exact: supported_restrE.
  - exact: le_trans (mxdot_restr _ _) z1.
  - move=> i; rewrite restrE; case: ifP => iL; first exact: level_alpha.
    by rewrite normr0 /alpha divr_ge0 ?exprn_ge0 ?sqrtr_ge0.
(* a net point for each level *)
have [y hy] : exists y : nat -> 'rV[R]_N, forall k,
    y k \in nt k (L k) /\ mxdot (zk k - y k) (zk k - y k) <= eps k ^+ 2.
  have h : forall k, exists y, y \in nt k (L k) /\
      mxdot (zk k - y) (zk k - y) <= eps k ^+ 2.
    by move=> k; have [y yn yd] := ntN (zkB k); exists y.
  by have [f hf] := choice h; exists f.
have ysupp k : supported (L k) (y k).
  by have [h _ _] := ntP (hy k).1; apply/supportedP.
have y1 k : mxdot (y k) (y k) <= 1 by have [_ h _] := ntP (hy k).1.
have Ldisj k r : k != r -> forall i, i \in L k -> i \in L r -> False.
  by move=> kr i ik ir; move/eqP: kr; apply; exact: level_uniq ik ir.
have Lz k : L k \subset supp z := level_supp m z k.
have sz (u : 'rV[R]_N) : supported (supp z) u -> (#|supp u| <= m)%N.
  by move=> h; exact: supported_card h zm.
have yz k : supported (supp z) (y k) := supported_sub (Lz k) (ysupp k).
have Lsize k : (#|L k| <= lsize m k)%N := level_size k zm z1.
(* the approximation xa of z and the error w *)
set xa := \sum_(0 <= k < l.+1) y k.
have zE : z = \sum_(0 <= k < l.+1) zk k.
  by rewrite big_mkord; exact: level_sum.
set w := z - xa.
have wE : w = \sum_(0 <= k < l.+1) (zk k - y k) by rewrite /w zE -sumrB.
have xaz : supported (supp z) xa by apply: supported_sum => k _.
have wz : supported (supp z) w.
  by apply: supportedB => //; apply/supportedP.
have dsj (a : nat -> 'rV[R]_N) : (forall k, supported (L k) (a k)) ->
    forall k r, k != r -> disj (a k) (a r).
  by move=> ha k r kr; apply: (disj_supported (ha k) (ha r)); exact: Ldisj.
have w2 : mxdot w w <= beta ^+ 2 / 9.
  rewrite wE mxdot_sum_disj ?iota_uniq //; last first.
    by apply: le_trans eps_sum; apply: ler_sum => k _; exact: (hy k).2.
  apply: (dsj (fun k => zk k - y k)) => k; apply: supportedB.
    exact: supported_restrE.
  exact: ysupp.
have fw : frobenius w <= beta / 3.
  rewrite /frobenius -(ger0_norm (divr_ge0 beta0 (ler0n R 3))) -sqrtr_sqr.
  by apply: ler_wsqrtr; rewrite expr_div_n (_ : (3 : R) ^+ 2 = 9) //; ring.
have fz : frobenius z <= 1 by rewrite /frobenius -sqrtr1 ler_wsqrtr.
have xaE : xa = z - w by rewrite /w opprB addrC subrK.
have fxa : frobenius xa <= 2.
  rewrite xaE; apply: le_trans (frobeniusB _ _) _.
  apply: le_trans (lerD fz fw) _.
  have b1 : beta <= 1.
    by apply: le_trans beta1 _; rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
  have b3 : beta / 3 <= 1.
    by rewrite ler_pdivrMr ?ltr0n // mul1r; apply: le_trans b1 _; rewrite ler1n.
  by apply: le_trans (lerD (lexx 1) b3) _; rewrite -[X in _ <= X]/(1 + 1).
have zxw : z = xa + w by rewrite /w addrC subrK.
have split1 : gram_off x z z =
    gram_off x xa xa + gram_off x w xa + gram_off x z w.
  rewrite -[in LHS](_ : xa + w = z) // gram_offDr.
  by rewrite gram_offDl -zxw.
(* the error terms *)
set D := B + 2 * C ^+ 2.
have D0 : 0 <= D by rewrite addr_ge0 ?mulr_ge0 ?sqr_ge0.
have err : `|gram_off x w xa| + `|gram_off x z w| <= beta * D.
  have h1 : `|gram_off x w xa| <= D * (beta / 3 * 2).
    apply: le_trans (gram_off_rip2 x (sz _ wz) (sz _ xaz)) _.
    by rewrite ler_wpM2l // ler_pM ?frobenius_ge0.
  have h2 : `|gram_off x z w| <= D * (1 * (beta / 3)).
    apply: le_trans (gram_off_rip2 x zm (sz _ wz)) _.
    by rewrite ler_wpM2l // ler_pM ?frobenius_ge0.
  apply: le_trans (lerD h1 h2) _.
  have -> : D * (beta / 3 * 2) + D * (1 * (beta / 3)) = beta * D by field.
  exact: lexx.
(* each level: the decoupled diagonal term and the term against the levels
   above *)
have hM (u : 'rV[R]_N) : supported (supp z) u ->
    frobenius (u *m tuple_mx x) <= Num.sqrt S * frobenius u.
  by move=> hu; exact: tuple_mx_rip (sz _ hu).
have sS : 0 <= Num.sqrt S := sqrtr_ge0 _.
have fy k : frobenius (y k) <= 1.
  by rewrite /frobenius -sqrtr1 ler_wsqrtr.
have diagk k : (k <= l)%N ->
    `|gram_off x (y k) (y k)| <= 4 * (t k * Num.sqrt S).
  move=> kl; apply: gram_off_decouple; first exact/supportedP.
  move=> E EL; apply: le_trans (goodW kl (Lsize k) EL (hy k).1) _.
  rewrite ler_wpM2l //; apply: le_trans (hM _ _) _.
    exact: supported_restr.
  rewrite -[leRHS]mulr1 ler_wpM2l //; apply: le_trans (fy k).
  rewrite /frobenius ler_wsqrtr //; exact: mxdot_restr.
pose v k := \sum_(k.+1 <= r < l.+1) y r.
have vsupp k : supported (~: L k) (v k).
  rewrite /v big_seq; apply: supported_sum => r.
  rewrite mem_index_iota => /andP[kr _] i; rewrite inE negbK => ik.
  apply: (ysupp r); apply/negP => ir.
  by apply: (Ldisj k r) ik ir; rewrite neq_ltn kr.
have vz k : supported (supp z) (v k) by apply: supported_sum.
have nxa : mxdot xa xa = \sum_(0 <= r < l.+1) mxdot (y r) (y r).
  by rewrite mxdot_sum_disj ?iota_uniq //; exact: dsj.
have fv k : (k <= l)%N -> frobenius (v k) <= 2.
  move=> kl; apply: le_trans fxa; rewrite /frobenius ler_wsqrtr // nxa.
  rewrite /v mxdot_sum_disj ?iota_uniq //.
    by move=> a b ab; exact: dsj ysupp a b ab.
  rewrite [leRHS](big_cat_nat _ (n := k.+1)) //= ?ltnS // lerDr.
  by apply: sumr_ge0 => r _; exact: mxdot_ge0.
have crossk k : (k <= l)%N ->
    `|gram_off x (y k) (v k)| <= 2 * (t k * Num.sqrt S).
  move=> kl.
  have dk : disj (y k) (v k).
    apply: (disj_supported (ysupp k) (vsupp k)) => i ik.
    by rewrite inE ik.
  have rv : restr (~: L k) (v k) = v k.
    by apply: restr_supp; exact/supportedP.
  have up : upper k (v k).
    exists y; split => // r /andP[kr rl]; exists (L r) => //.
    exact: (hy r).1.
  rewrite gram_off_disj //.
  have := goodX kl (Lsize k) (hy k).1 up; rewrite rv => h.
  apply: le_trans h _; rewrite mulrCA ler_wpM2l //.
  apply: le_trans (hM _ (vz k)) _.
  by rewrite mulrC ler_wpM2r // fv.
(* sum over the levels *)
have main : `|gram_off x xa xa| <=
    8 * (\sum_(0 <= k < l.+1) t k) * Num.sqrt S.
  rewrite /xa gram_off_tri //; apply: le_trans (ler_norm_sum _ _ _) _.
  rewrite mulr_sumr mulr_suml big_seq [leRHS]big_seq; apply: ler_sum => k.
  rewrite mem_index_iota ltnS => /andP[_ kl].
  apply: le_trans (ler_normD _ _) _; rewrite normrM ger0_norm ?ler0n //.
  have := lerD (diagk k kl) (ler_wpM2l (ler0n R 2) (crossk k kl)).
  move/le_trans; apply.
  have -> : 4 * (t k * Num.sqrt S) + 2 * (2 * (t k * Num.sqrt S)) =
    8 * t k * Num.sqrt S by ring.
  exact: lexx.
apply: le_trans (_ : `|gram_off x xa xa| +
  (`|gram_off x w xa| + `|gram_off x z w|) <= _).
  rewrite split1 -addrA; apply: le_trans (ler_normD _ _) _.
  by rewrite lerD2l ler_normD.
exact: lerD main err.
Qed.

Theorem rip_const_le : rip_const m x <=
  256 * (\sum_(0 <= k < l.+1) t k) ^+ 2 +
  32 * (\sum_(0 <= k < l.+1) t k) * maxnorm x + 8 * beta * maxnorm x ^+ 2.
Proof.
set T := \sum_(0 <= k < l.+1) t k.
set B := rip_const m x; set C := maxnorm x.
have B0 : 0 <= B := rip_const_ge0 m x.
have C0 : 0 <= C := maxnorm_ge0 x.
have T0 : 0 <= T by apply: sumr_ge0 => k _.
have hB : B <= 8 * T * Num.sqrt (B + C ^+ 2) + beta * (B + 2 * C ^+ 2).
  apply: ge_sup; first exact: (has_sup_rip m x).1.
  by move=> _ [z zB <-]; exact: gram_off_ball.
have sq : Num.sqrt (B + C ^+ 2) <= Num.sqrt B + C.
  rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?sqrtr_ge0 ?addr_ge0 ?sqrtr_ge0 //.
  rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 // sqrrD sqr_sqrtr //.
  by rewrite -addrA lerD2l lerDr mulrn_wge0 // mulr_ge0 ?sqrtr_ge0.
(* b^2 <= 16 T b + 16 T C + 4 beta C^2, and 16 T b <= b^2 / 2 + 128 T^2 *)
set b := Num.sqrt B.
have bB : b ^+ 2 = B by rewrite sqr_sqrtr.
have b0 : 0 <= b := sqrtr_ge0 _.
have h1 : B <= 8 * T * (b + C) + beta * (B + 2 * C ^+ 2).
  by apply: le_trans hB _; rewrite lerD2r ler_wpM2l // mulr_ge0.
have hb : beta * B <= B / 2.
  have := ler_wpM2r B0 beta1; rewrite mul1r mulrC [B / 2]mulrC => h.
  by apply: le_trans h _; rewrite mulrC.
have hs := sqr_ge0 (b - 16 * T).
rewrite -bB in h1 hb *.
nra.
Qed.

End deterministic.

Lemma measure_bigsetU_le d (T : measurableType d) (R : realType)
    (mu : {measure set T -> \bar R}) (I : Type) (r : seq I) (F : I -> set T) :
  (forall i, measurable (F i)) ->
  (mu (\big[setU/set0]_(i <- r) F i) <= \sum_(i <- r) mu (F i))%E.
Proof.
move=> mF; elim: r => [|i r IH]; first by rewrite !big_nil measure0.
rewrite !big_cons; apply: le_trans (measureU2 _ _ _) _ => //.
  exact: bigsetU_measurable.
by rewrite leeD2l.
Qed.

Section numeric.
Context {R : realType}.

Lemma ln_le_sub1 (x : R) : 0 < x -> ln x <= x - 1.
Proof.
move=> x0; have := @le_ln1Dx R (x - 1).
rewrite addrCA subrr addr0; apply.
by rewrite ltrBrDl subrr.
Qed.

Lemma ln2_le1 : ln (2 : R) <= 1.
Proof.
by apply: le_trans (ln_le_sub1 _) _; rewrite // (_ : (2 : R) - 1 = 1) //; ring.
Qed.

Lemma lnX_le (x : R) (k : nat) : 0 < x -> ln (x ^+ k) = k%:R * ln x.
Proof. by move=> x0; rewrite lnXn // mulr_natl. Qed.

(* s ln (sigma / s) <= sigma. *)
Lemma slog_le (s sigma : R) : 0 < s -> s <= sigma ->
  s * ln (sigma / s) <= sigma.
Proof.
move=> s0 ss.
have sg : 0 < sigma by exact: lt_le_trans s0 ss.
apply: le_trans (_ : s * (sigma / s - 1) <= _).
  apply: ler_wpM2l; first exact: ltW.
  by apply: ln_le_sub1; rewrite divr_gt0.
by rewrite mulrBr mulr1 mulrCA mulfV ?gt_eqF // mulr1 lerBlDr lerDl ltW.
Qed.

End numeric.

Section configurations.
Context {R : realType} (N m l : nat) (beta : R).
Hypotheses (m0 : (0 < m)%N) (beta0 : 0 < beta).

(* The mesh of the net of level k. *)
Definition mesh k : R := beta / 2 ^+ k.+2.

Lemma mesh_gt0 k : 0 < mesh k.
Proof. by rewrite divr_gt0 // exprn_gt0. Qed.

Lemma alpha_ge0 k : 0 <= alpha m k :> R.
Proof. by rewrite /alpha divr_ge0 ?exprn_ge0 ?sqrtr_ge0. Qed.

Definition net_spec k (F : {set 'I_N}) (S : seq 'rV[R]_N) :=
  [/\ forall y, y \in S -> sball F (alpha m k) y,
    forall z, sball F (alpha m k) z ->
      exists2 y, y \in S & mxdot (z - y) (z - y) <= mesh k ^+ 2 &
    (size S)%:R <= (2 * expR 1 * (1 + 2 / mesh k)) ^+ #|F|].

(* A net of level k for the vectors supported in F. *)
Definition net k F : seq 'rV[R]_N := xget [::] (net_spec k F).

Lemma netP k F : net_spec k F (net k F).
Proof.
apply: xgetPex; have [S [h1 h2 h3]] := sparse_net F (alpha_ge0 k) (mesh_gt0 k).
by exists S; split.
Qed.

Definition sets_le s : seq {set 'I_N} :=
  enum [set F : {set 'I_N} | (#|F| <= s)%N]%SET.

(* The pairs of the decoupled diagonal terms of level k. *)
Definition wconf k : seq ('rV[R]_N * 'rV[R]_N) :=
  flatten [seq flatten [seq [seq (restr E y, restr (F :\: E) y) | y <- net k F]
    | E <- enum (powerset F)] | F <- sets_le (lsize m k)].

Definition allnet r : seq 'rV[R]_N :=
  flatten [seq net r F | F <- sets_le (lsize m r)].

(* The sums of net points of the levels l - d + 1, ..., l. *)
Fixpoint vlist d : seq 'rV[R]_N :=
  if d is d'.+1 then [seq y + v | y <- allnet (l - d'), v <- vlist d']
  else [:: 0].

(* The pairs of the terms of level k against the levels above. *)
Definition xconf k : seq ('rV[R]_N * 'rV[R]_N) :=
  flatten [seq flatten [seq [seq (y, restr (~: F) v) | v <- vlist (l - k)]
    | y <- net k F] | F <- sets_le (lsize m k)].

Lemma mem_sets_le s F : (F \in sets_le s) = (#|F| <= s)%N.
Proof. by rewrite mem_enum inE. Qed.

Lemma mem_wconf k (F E : {set 'I_N}) y : (#|F| <= lsize m k)%N ->
  E \subset F -> y \in net k F -> (restr E y, restr (F :\: E) y) \in wconf k.
Proof.
move=> Fs EF yn; apply/flattenP; exists
  (flatten [seq [seq (restr E' y', restr (F :\: E') y') | y' <- net k F]
    | E' <- enum (powerset F)]).
  by apply/mapP; exists F => //; rewrite mem_sets_le.
apply/flattenP; exists [seq (restr E y', restr (F :\: E) y') | y' <- net k F].
  by apply/mapP; exists E => //; rewrite mem_enum powersetE.
by apply/mapP; exists y.
Qed.

Lemma mem_xconf k (F : {set 'I_N}) y v : (#|F| <= lsize m k)%N ->
  y \in net k F -> v \in vlist (l - k) -> (y, restr (~: F) v) \in xconf k.
Proof.
move=> Fs yn vv; apply/flattenP; exists
  (flatten [seq [seq (y', restr (~: F) v') | v' <- vlist (l - k)]
    | y' <- net k F]).
  by apply/mapP; exists F => //; rewrite mem_sets_le.
apply/flattenP; exists [seq (y, restr (~: F) v') | v' <- vlist (l - k)].
  by apply/mapP; exists y.
by apply/mapP; exists v.
Qed.

Lemma mem_allnet r (F : {set 'I_N}) y : (#|F| <= lsize m r)%N ->
  y \in net r F -> y \in allnet r.
Proof.
move=> Fs yn; apply/flattenP; exists (net r F) => //.
by apply/mapP; exists F => //; rewrite mem_sets_le.
Qed.

(* Every sum of net points of the levels above k is in vlist (l - k). *)
Lemma upper_vlist k v : (k <= l)%N -> upper m l net k v -> v \in vlist (l - k).
Proof.
move=> kl [yr [hy ->]].
suff h : forall d k, l = (k + d)%N ->
    (forall r, (k < r <= l)%N ->
      exists2 F : {set 'I_N}, (#|F| <= lsize m r)%N & yr r \in net r F) ->
    \sum_(k.+1 <= r < l.+1) yr r \in vlist d.
  by apply: h => //; rewrite subnKC.
elim=> [|d IH] k' lE hy'.
  by rewrite lE addn0 big_geq // mem_seq1.
have kl' : (k'.+1 < l.+1)%N by rewrite lE ltnS addnS ltnS leq_addr.
rewrite big_ltn //=.
have -> : (l - d)%N = k'.+1 by rewrite lE addnS -addSn addnK.
apply: allpairs_f.
  have h1 : (k' < k'.+1 <= l)%N by rewrite ltnSn lE addnS ltnS leq_addr.
  have [F Fs yF] := hy' k'.+1 h1.
  exact: mem_allnet Fs yF.
apply: IH; first by rewrite lE addnS addSn.
by move=> r /andP[kr rl]; apply: hy'; rewrite rl andbT ltnW.
Qed.

(* Sizes of the configuration lists. *)
Definition nbase k : R := 2 * expR 1 * (1 + 2 / mesh k).

Lemma nbase_ge1 k : 1 <= nbase k.
Proof.
have e1 : 1 <= expR 1 :> R by rewrite -expR0 ler_expR.
have h1 : 1 <= 1 + 2 / mesh k by rewrite lerDl divr_ge0 // ltW // mesh_gt0.
have h2 : 1 <= 2 * expR 1 :> R.
  by apply: le_trans e1 _; rewrite ler_peMl ?expR_ge0 // ler1n.
by have := ler_pM ler01 ler01 h2 h1; rewrite mul1r.
Qed.

Lemma size_net k (F : {set 'I_N}) s : (#|F| <= s)%N ->
  (size (net k F))%:R <= nbase k ^+ s.
Proof.
move=> Fs; have [_ _ h] := netP k F; apply: le_trans h _.
exact: (ler_weXn2l (nbase_ge1 k) Fs).
Qed.

Definition ccount k : R :=
  (#|[set F : {set 'I_N} | (#|F| <= lsize m k)%N]%SET|)%:R *
  (2 * nbase k) ^+ lsize m k.

Lemma ccount_ge1 k : 1 <= ccount k.
Proof.
have h1 : 1 <= (#|[set F : {set 'I_N} | (#|F| <= lsize m k)%N]%SET|)%:R :> R.
  rewrite ler1n lt0n; apply/eqP => /eqP; rewrite cards_eq0 => /eqP h.
  have : (finset.set0 : {set 'I_N}) \in
      [set F : {set 'I_N} | (#|F| <= lsize m k)%N]%SET.
    by rewrite inE cards0.
  by rewrite h inE.
have h2 : 1 <= (2 * nbase k) ^+ lsize m k.
  apply: exprn_ege1; apply: le_trans (nbase_ge1 k) _.
  by rewrite ler_peMl ?ler1n // (le_trans ler01 (nbase_ge1 k)).
by have := ler_pM ler01 ler01 h1 h2; rewrite mul1r.
Qed.

Lemma size_wconf k : (size (wconf k))%:R <= ccount k.
Proof.
rewrite /wconf size_flatten sumnE big_map natr_sum.
have hF (F : {set 'I_N}) : (#|F| <= lsize m k)%N ->
    (size (flatten [seq [seq (restr E y, restr (F :\: E) y) | y <- net k F]
      | E <- enum (powerset F)]))%:R <= (2 * nbase k) ^+ lsize m k :> R.
  move=> Fs; rewrite size_flatten sumnE big_map natr_sum big_map.
  under eq_bigr do rewrite size_map.
  rewrite big_const_seq count_predT iter_addr addr0 -cardE card_powerset.
  rewrite -[X in X <= _]mulr_natl natrX exprMn.
  apply: ler_pM; rewrite ?exprn_ge0 ?ler0n //; last exact: size_net.
  by rewrite ler_eXn2l // ltr1n.
rewrite big_map big_seq.
apply: le_trans (_ : \sum_(F <- sets_le (lsize m k) | F \in sets_le (lsize m k))
  (2 * nbase k) ^+ lsize m k <= _).
  by apply: ler_sum => F; rewrite mem_sets_le; exact: hF.
rewrite -big_seq big_const_seq count_predT iter_addr addr0 -mulr_natl.
rewrite mulr1 /ccount /sets_le -cardE.
by rewrite [X in _ <= X]mulr_natl.
Qed.

Lemma size_allnet r : (size (allnet r))%:R <= ccount r.
Proof.
rewrite /allnet size_flatten sumnE natr_sum big_map big_map big_seq.
apply: le_trans (_ : \sum_(F <- sets_le (lsize m r) | F \in sets_le (lsize m r))
  (2 * nbase r) ^+ lsize m r <= _).
  apply: ler_sum => F; rewrite mem_sets_le => Fs.
  have hn := le_trans ler01 (nbase_ge1 r).
  apply: le_trans (size_net r Fs) _; rewrite lerXn2r ?nnegrE //.
    by rewrite mulr_ge0.
  by rewrite ler_peMl // ler1n.
rewrite -big_seq big_const_seq count_predT iter_addr addr0 -mulr_natl.
rewrite mulr1 /ccount /sets_le -cardE.
by rewrite [X in _ <= X]mulr_natl.
Qed.

Lemma size_vlist d : (size (vlist d))%:R <= \prod_(j < d) ccount (l - j).
Proof.
elim: d => [|d IH]; first by rewrite big_ord0.
rewrite /= size_allpairs natrM big_ord_recr /= mulrC.
by apply: ler_pM; rewrite ?ler0n //; last exact: size_allnet.
Qed.

Lemma size_xconf k :
  (size (xconf k))%:R <= ccount k * \prod_(j < l - k) ccount (l - j).
Proof.
have hv := size_vlist (l - k).
have hp : 0 <= \prod_(j < l - k) ccount (l - j).
  by apply: prodr_ge0 => j _; exact: le_trans ler01 (ccount_ge1 _).
rewrite /xconf size_flatten sumnE natr_sum big_map big_map big_seq.
apply: le_trans (_ : \sum_(F <- sets_le (lsize m k) | F \in sets_le (lsize m k))
  ((2 * nbase k) ^+ lsize m k * \prod_(j < l - k) ccount (l - j)) <= _).
  apply: ler_sum => F; rewrite mem_sets_le => Fs.
  rewrite size_flatten sumnE natr_sum big_map big_map.
  under eq_bigr do rewrite size_map.
  rewrite big_const_seq count_predT iter_addr addr0 -mulr_natl.
  have hn := le_trans ler01 (nbase_ge1 k).
  rewrite mulr1 -[X in X <= _]mulr_natl.
  apply: ler_pM; rewrite ?ler0n //.
  apply: le_trans (size_net k Fs) _; rewrite lerXn2r ?nnegrE ?mulr_ge0 //.
  1,2: by rewrite addr_ge0 // divr_ge0 // ltW // mesh_gt0.
  by rewrite ler_peMl // ler1n.
rewrite -big_seq big_const_seq count_predT iter_addr addr0.
rewrite /ccount /sets_le -cardE -mulrA.
by rewrite [X in _ <= X]mulr_natl.
Qed.

Lemma lnb2_le k : beta <= 1 -> ln (2 * nbase k) <= k%:R + 7 - ln beta.
Proof.
move=> b1.
have p2 : 0 < (2 : R) ^+ k.+3 by rewrite exprn_gt0.
have hm : 2 / mesh k = 2 ^+ k.+3 / beta.
  by rewrite /mesh invf_div mulrA -exprS.
have h1 : 1 <= 2 ^+ k.+3 / beta.
  rewrite ler_pdivlMr // mul1r; apply: le_trans b1 _.
  by apply: exprn_ege1; rewrite ler1n.
(* 2 nbase k = 4 e (1 + q) <= 8 e q with q = 2^(k+3) / beta >= 1 *)
have h2 : 2 * nbase k <= expR 1 * (8 * (2 ^+ k.+3 / beta)).
  rewrite /nbase hm.
  set q := 2 ^+ k.+3 / beta.
  have e0 : 0 <= expR 1 :> R := expR_ge0 _.
  have hq : 1 <= q := h1.
  have hq1 : 0 <= q - 1 by rewrite subr_ge0.
  have hh := mulr_ge0 e0 hq1.
  nra.
have nb1 := nbase_ge1 k.
have pos1 : 0 < 2 * nbase k by rewrite mulr_gt0 // (lt_le_trans ltr01 nb1).
have pos2 : 0 < 2 ^+ k.+3 / beta by rewrite divr_gt0.
have e0 : 0 < expR 1 :> R := expR_gt0 _.
have p8 : 0 < (8 : R) by rewrite ltr0n.
apply: le_trans (_ : ln (expR 1 * (8 * (2 ^+ k.+3 / beta))) <= _).
  have pos3 : 0 < expR 1 * (8 * (2 ^+ k.+3 / beta)).
    by apply: mulr_gt0 => //; apply: mulr_gt0.
  by rewrite ler_ln.
have pb : 0 < beta^-1 by rewrite invr_gt0.
have p3 : 0 < 8 * (2 ^+ k.+3 / beta) by apply: mulr_gt0.
rewrite (lnM e0 p3) (lnM p8 pos2) (lnM p2 pb) lnV // expRK.
rewrite (_ : (8 : R) = 2 ^+ 3); first by rewrite !exprS expr0; ring.
rewrite !lnX_le ?ltr0n //.
have l2 := @ln2_le1 R.
have l20 : 0 <= ln (2 : R) by rewrite ln_ge0 // ler1n.
rewrite -[k.+3]addn3 natrD.
have k0 : 0 <= k%:R :> R := ler0n _ _.
have l2' : 0 <= 1 - ln (2 : R) by rewrite subr_ge0.
have hk := mulr_ge0 k0 l2'.
nra.
Qed.

(* The logarithm of the number of configurations of level k. *)
Lemma ccount_le k : (m <= N)%N -> beta <= 1 ->
  ccount k <= expR (4 * m%:R / 4 ^+ k *
    (9 + ln (N%:R / m%:R) - ln beta + 3 * k%:R)).
Proof.
move=> mN b1.
have mR : 0 < m%:R :> R by rewrite ltr0n.
have NR : 0 < N%:R :> R by rewrite ltr0n (leq_trans m0 mN).
have p4 : 0 < (4 : R) ^+ k by rewrite exprn_gt0.
(* the size of level k is at most sigma = 4 m / 4^k *)
have ssig : (lsize m k)%:R <= 4 * m%:R / 4 ^+ k :> R.
  case: k p4 => [|k] p4 /=.
    by rewrite expr0 divr1 -[X in X <= _]mul1r ler_wpM2r ?ler0n ?ler1n.
  have p4' : 0 < (4 : R) ^+ k by rewrite exprn_gt0.
  have -> : 4 * m%:R / 4 ^+ k.+1 = m%:R / 4 ^+ k :> R.
    by rewrite exprS; field; rewrite gt_eqF.
  rewrite ler_pdivlMr // -natrX -natrM ler_nat.
  by rewrite leq_divM.
set sig : R := 4 * m%:R / 4 ^+ k in ssig *.
set A : R := 9 + ln (N%:R / m%:R) - ln beta + 3 * k%:R.
have sig0 : 0 < sig.
  rewrite /sig; apply: mulr_gt0; last by rewrite invr_gt0.
  by apply: mulr_gt0 => //; rewrite ltr0n.
have lNm : 0 <= ln (N%:R / m%:R) :> R.
  by rewrite ln_ge0 // ler_pdivlMr // mul1r ler_nat.
have lb : ln beta <= 0 by rewrite ln_le0.
have k0 : 0 <= k%:R :> R := ler0n _ _.
have A0 : 0 <= A by rewrite /A; nra.
set s := lsize m k in ssig *.
case: (posnP s) => [s0|spos].
  rewrite /ccount -/s s0 expr0 mulr1 card_small_sets big_ord1 bin0.
  have h := mulr_ge0 (ltW sig0) A0.
  by rewrite -expR0 ler_expR.
have sm : (s <= m)%N by rewrite /s; case: (k) => [|k'] //=; exact: leq_div.
have sN : (s <= N)%N := leq_trans sm mN.
have sR : 0 < s%:R :> R by rewrite ltr0n.
have nb1 := nbase_ge1 k.
have nbp : 0 < 2 * nbase k by rewrite mulr_gt0 // (lt_le_trans ltr01 nb1).
(* ccount k <= X^s with X = e N / s * 2 nbase k *)
set X := expR 1 * N%:R / s%:R * (2 * nbase k).
have e0 : 0 < expR 1 :> R := expR_gt0 _.
have X0 : 0 < X.
  by rewrite /X; apply: mulr_gt0 => //; apply: divr_gt0 => //; apply: mulr_gt0.
apply: le_trans (_ : X ^+ s <= _).
  rewrite /ccount -/s /X exprMn.
  rewrite /ccount -/s /X [in X in _ <= X]exprMn.
  rewrite -[2 ^+ s * _]exprMn.
  apply: ler_pM.
  - exact: ler0n.
  - by rewrite exprn_ge0 // ltW.
  - exact: (small_sets_le (R := R) spos sN).
  - exact: lexx.
have Xs : 0 < X ^+ s by rewrite exprn_gt0.
rewrite -[X ^+ s](lnK Xs) ler_expR lnX_le //.
(* ln X = 1 + ln (N / m) + ln (sigma / s) + ln (m / sigma) + ln (2 nbase k) *)
have XE : X = expR 1 * (N%:R / s%:R) * (2 * nbase k).
  by rewrite /X [expR 1 * (_ / _)]mulrA.
have e1 : N%:R / s%:R = (N%:R / m%:R) * (m%:R / s%:R) :> R.
  by rewrite mulrA divfK ?gt_eqF.
have e2 : m%:R / s%:R = (sig / s%:R) * (m%:R / sig) :> R.
  by rewrite [RHS]mulrC mulrA divfK ?gt_eqF.
have p1 : 0 < N%:R / m%:R :> R by rewrite divr_gt0.
have p2 : 0 < sig / s%:R by rewrite divr_gt0.
have p3 : 0 < m%:R / sig by rewrite divr_gt0.
have pNs : 0 < N%:R / s%:R :> R by rewrite divr_gt0.
have pms : 0 < m%:R / s%:R :> R by rewrite divr_gt0.
have q1 : 0 < expR 1 * (N%:R / s%:R) := mulr_gt0 e0 pNs.
rewrite XE (lnM q1 nbp) (lnM e0 pNs) expRK e1 (lnM p1 pms) e2 (lnM p2 p3).
have h1 : s%:R * ln (sig / s%:R) <= sig := slog_le sR ssig.
have h3 : ln (2 * nbase k) <= k%:R + 7 - ln beta := lnb2_le k b1.
have l2 := @ln2_le1 R.
have l20 : 0 <= ln (2 : R) by rewrite ln_ge0 // ler1n.
have h2 : ln (m%:R / sig) <= 2 * k%:R.
  have -> : m%:R / sig = 4 ^+ k / 4 :> R.
    have m0' : m%:R != 0 :> R by rewrite gt_eqF.
    have p4' : (4 : R) ^+ k != 0 by rewrite gt_eqF.
    have f4 : (4 : R) != 0 by rewrite pnatr_eq0.
    by rewrite /sig; field; rewrite f4 m0' p4'.
  have p40 : 0 < (4 : R) by rewrite ltr0n.
  have p4i : 0 < (4 : R)^-1 by rewrite invr_gt0.
  rewrite (lnM p4 p4i) lnV ?posrE // lnX_le //.
  rewrite (_ : (4 : R) = 2 ^+ 2); first by rewrite expr2; ring.
  rewrite lnX_le ?ltr0n //.
  have k0' : 0 <= k%:R :> R := ler0n _ _.
  have l2' : 0 <= 1 - ln (2 : R) by rewrite subr_ge0.
  have hk := mulr_ge0 k0' l2'.
  nra.
have sR0 := ltW sR.
have g1 : 0 <= s%:R * (2 * k%:R - ln (m%:R / sig)).
  by rewrite mulr_ge0 // subr_ge0.
have g2 : 0 <= s%:R * (k%:R + 7 - ln beta - ln (2 * nbase k)).
  by rewrite mulr_ge0 // subr_ge0.
have ss : 0 <= sig - s%:R by rewrite subr_ge0.
have g3 : 0 <= (sig - s%:R) * (1 + ln (N%:R / m%:R)).
  by rewrite mulr_ge0 // addr_ge0.
have g4 : 0 <= (sig - s%:R) * (3 * k%:R + 7 - ln beta).
  rewrite mulr_ge0 //; rewrite -addrA addr_ge0 ?mulr_ge0 //.
  by rewrite addr_ge0 // oppr_ge0.
rewrite /A; nra.
Qed.

(* The pairs of the union bound satisfy the hypotheses of cross_tail. *)
Lemma mesh_sum n : \sum_(0 <= k < n) mesh k ^+ 2 <= beta ^+ 2 / 9.
Proof.
have e k : mesh k ^+ 2 = beta ^+ 2 / 4 ^+ k.+2.
  rewrite /mesh expr_div_n -exprM mulnC exprM (_ : (2 : R) ^+ 2 = 4) //.
  by ring.
have h : \sum_(0 <= k < n) mesh k ^+ 2 + beta ^+ 2 / (12 * 4 ^+ n) =
    beta ^+ 2 / 12.
  elim: n => [|n IH]; first by rewrite big_geq // add0r expr0 mulr1.
  rewrite big_nat_recr //= e -IH -addrA; congr (_ + _).
  by rewrite !exprS; field; rewrite !expf_neq0 //.
apply: le_trans (_ : beta ^+ 2 / 12 <= _); last first.
  by rewrite ler_pM2l ?exprn_gt0 // lef_pV2 ?posrE // ler_nat.
by rewrite -h lerDl divr_ge0 ?sqr_ge0 // mulr_ge0 ?exprn_ge0.
Qed.

Lemma conf_ok k c : c \in wconf k ++ xconf k ->
  [/\ disj c.1 c.2, mxdot c.1 c.1 <= 1 & forall i, `|c.1 0 i| <= alpha m k].
Proof.
rewrite mem_cat => /orP[|].
  move=> /flattenP[s1 /mapP[F _ ->] /flattenP[s2 /mapP[E _ ->] /mapP[y yn ->]]].
  have [h1 _ _] := netP k F; have [_ y1 ya] := h1 y yn.
  split => /=.
  - move=> i; rewrite !restrE !inE.
    by case: (i \in E); [right|left].
  - exact: le_trans (mxdot_restr _ _) y1.
  - move=> i; rewrite restrE; case: ifP => _; first exact: ya.
    by rewrite normr0 alpha_ge0.
move=> /flattenP[s1 /mapP[F _ ->] /flattenP[s2 /mapP[y yn ->] /mapP[v _ ->]]].
have [h1 _ _] := netP k F; have [yF y1 ya] := h1 y yn.
split => //=.
move=> i; rewrite restrE inE.
case: (boolP (i \in F)) => iF /=; first by right.
by left; have := (supportedP F y).2 yF; apply.
Qed.

End configurations.

Section union_bound.
Context {R : realType} (N n m l : nat) (mu : nat -> probability 'rV[R]_n R)
  (psi beta : R).
Hypothesis psi0 : 0 < psi.
Hypothesis sub : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  subexponential (mu i) (fun v => mxdot v y) psi.
Hypothesis cen : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  \int[mu i]_v mxdot v y = 0.
Hypotheses (m0 : (0 < m)%N) (ml : (m <= 4 ^ l)%N).
Hypotheses (beta0 : 0 < beta) (beta1 : beta <= 1 / 2).
Variable t : nat -> R.
Hypothesis t0 : forall k, 0 < t k.

Let conf k := @wconf R N m beta k ++ @xconf R N m l beta k.

(* The union of the bad events of all levels. *)
Definition bad_event : set (N.-tuple 'rV[R]_n) :=
  \big[setU/set0]_(k < l.+1)
    \big[setU/set0]_(c <- conf k) cross_event (t k) c.1 c.2.

Lemma measurable_bad_event : measurable bad_event.
Proof.
apply: bigsetU_measurable => k _; apply: bigsetU_measurable => c _.
exact: measurable_cross_event (ltW (t0 k)).
Qed.

Lemma bad_event_le : (tuple_prod mu N bad_event <=
  (\sum_(k < l.+1) (size (conf k))%:R *
    (2 * expR (- Num.min (t k ^+ 2 / (64 * psi ^+ 2))
                         (t k / (4 * (alpha m k * psi))))))%:E)%E.
Proof.
rewrite /bad_event.
apply: le_trans (measure_bigsetU_le _ _ _) _.
  move=> k; apply: bigsetU_measurable => c _.
  exact: measurable_cross_event (ltW (t0 k)).
rewrite -sumEFin; apply: lee_sum => k _.
apply: le_trans (measure_bigsetU_le _ _ _) _.
  by move=> c; exact: measurable_cross_event (ltW (t0 k)).
apply: le_trans (_ : (\sum_(c <- conf k) (2 * expR (- Num.min
    (t k ^+ 2 / (64 * psi ^+ 2)) (t k / (4 * (alpha m k * psi)))))%:E <= _)%E).
  rewrite big_seq [leRHS]big_seq; apply: lee_sum => c cin.
  have [hd h1 ha] := conf_ok beta0 cin.
  exact: cross_tail.
rewrite sumEFin lee_fin big_const_seq count_predT iter_addr addr0.
by rewrite -[X in X <= _]mulr_natl.
Qed.

Lemma bigsetU_mem (T : Type) (I : eqType) (r : seq I) (F : I -> set T) i z :
  i \in r -> F i z -> (\big[setU/set0]_(j <- r) F j) z.
Proof.
elim: r => [//|j r IH]; rewrite inE big_cons => /orP[/eqP <- h|ir h].
  by left.
by right; exact: IH.
Qed.

(* Outside the bad event, B_m^2 is bounded by the sum T of the t k. *)
Theorem rip_good x : ~ bad_event x ->
  rip_const m x <= 256 * (\sum_(0 <= k < l.+1) t k) ^+ 2 +
    32 * (\sum_(0 <= k < l.+1) t k) * maxnorm x + 8 * beta * maxnorm x ^+ 2.
Proof.
move=> nb.
have notin k c : (k <= l)%N -> c \in conf k ->
    `|mxdot (c.1 *m tuple_mx x) (c.2 *m tuple_mx x)| <=
    t k * frobenius (c.2 *m tuple_mx x).
  move=> kl cin; rewrite leNgt; apply/negP => h; apply: nb.
  have kl' : (k < l.+1)%N by rewrite ltnS.
  apply: (bigsetU_mem (i := Ordinal kl')); first exact: mem_index_enum.
  exact: bigsetU_mem cin h.
apply: (@rip_const_le R N n m l x m0 ml (mesh beta) t beta (net m beta)).
- by move=> k F y yn; have [h _ _] := netP m beta0 k F; exact: h.
- by move=> k F z zB; have [_ h _] := netP m beta0 k F; exact: h.
- exact: mesh_sum.
- exact: ltW.
- exact: beta1.
- by move=> k; exact: ltW.
- move=> k F E y kl Fs EF yn.
  apply: (notin k (restr E y, restr (F :\: E) y) kl).
  by rewrite mem_cat mem_wconf.
- move=> k F y v kl Fs yn up.
  apply: (notin k (y, restr (~: F) v) kl).
  by rewrite mem_cat mem_xconf ?orbT // upper_vlist.
Qed.

End union_bound.

Section series.
Context {R : realType}.

Lemma sum_pow2 n : \sum_(k < n) (2 : R) ^+ k <= 2 ^+ n.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0 expr0 ler01.
rewrite big_ord_recr /= exprS mulr2n mulrDl mul1r lerD2r.
exact: IH.
Qed.

(* sum_k 2^-k (a + 3 k) <= 4 a for a >= 6 *)
Lemma sum_geo_lin (a : R) n : 6 <= a ->
  \sum_(k < n) (a + 3 * k%:R) / 2 ^+ k <= 4 * a.
Proof.
move=> a6; pose f k : R := (a + 3 * k%:R) / 2 ^+ k.
(* the terms decrease by a factor 3/4 at least *)
have fs k : f k.+1 <= 3 / 4 * f k.
  rewrite /f exprS -[k.+1]addn1 natrD.
  have p : 0 < (2 : R) ^+ k by rewrite exprn_gt0.
  have k0 : 0 <= k%:R :> R := ler0n _ _.
  rewrite ler_pdivrMr ?mulr_gt0 //.
  have -> : 3 / 4 * ((a + 3 * k%:R) / 2 ^+ k) * (2 * 2 ^+ k) =
      3 / 2 * (a + 3 * k%:R).
    by field; rewrite gt_eqF.
  lra.
suff h : \sum_(k < n) f k + 4 * f n <= 4 * f 0.
  have : 0 <= f n.
    rewrite /f divr_ge0 ?exprn_ge0 // addr_ge0 ?mulr_ge0 ?ler0n //.
    exact: le_trans _ a6.
  move=> fn0.
  have h' : \sum_(k < n) f k <= 4 * f 0 by lra.
  by move: h'; rewrite /f expr0 divr1 mulr0 addr0.
elim: n => [|n IH]; first by rewrite big_ord0 add0r.
rewrite big_ord_recr /=; have := fs n; lra.
Qed.

Lemma sq_le_pow2 l : (l.+1 ^ 2 <= 8 * 2 ^ l)%N.
Proof.
elim: l => [//|l IH].
have h2 : (l < 2 ^ l)%N by rewrite ltn_expl.
rewrite -(ler_nat R) in IH *; rewrite -(ltr_nat R) in h2.
rewrite !natrM !natrX in IH *; rewrite natrX in h2.
rewrite -(ler_nat R) natrM !natrX exprS.
have hl : 0 <= l%:R :> R := ler0n _ _.
rewrite -[l.+2]addn1 -[l.+1]addn1 !natrD in IH *.
rewrite expr1 exprD expr1.
have p1 : 1 <= (2 : R) ^+ l by apply: exprn_ege1; rewrite ler1n.
nra.
Qed.

End series.

Section parameters.
Context {R : realType} (N n m l : nat) (psi beta K : R).
Hypotheses (m0 : (0 < m)%N) (mN : (m <= N)%N).
Hypotheses (ml : (m <= 4 ^ l)%N) (lm : (4 ^ l <= 4 * m)%N).
Hypotheses (psi0 : 0 < psi) (beta0 : 0 < beta) (beta1 : beta <= 1 / 2).
Hypothesis K1 : 1 <= K.

(* Lp = ln (e N / m) and the exponent of the count of level k. *)
Definition Lp : R := 1 + ln (N%:R / m%:R).
Definition Lz : R := 9 + ln (N%:R / m%:R) - ln beta.
Definition Hk k : R := 4 * m%:R / 4 ^+ k * (Lz + 3 * k%:R).
Definition uk k : R := ln 2 + 2 * Hk k + K * Num.sqrt m%:R * Lp.
(* The thresholds of the union bound. *)
Definition tk k : R := 4 * psi * alpha m k * uk k + 8 * psi * Num.sqrt (uk k).

Lemma Lp_ge1 : 1 <= Lp.
Proof.
have mR : 0 < m%:R :> R by rewrite ltr0n.
have hN : 0 <= ln (N%:R / m%:R) :> R.
  by rewrite ln_ge0 // ler_pdivlMr // mul1r ler_nat.
by rewrite /Lp lerDl.
Qed.

Lemma Lz_ge9 : 9 <= Lz.
Proof.
have mR : 0 < m%:R :> R by rewrite ltr0n.
have hN : 0 <= ln (N%:R / m%:R) :> R.
  by rewrite ln_ge0 // ler_pdivlMr // mul1r ler_nat.
have hb : ln beta <= 0.
  by rewrite ln_le0 // (le_trans beta1) // ler_pdivrMr ?ltr0n // mul1r ler1n.
by rewrite /Lz -addrA lerDl addr_ge0 // oppr_ge0.
Qed.

Lemma Hk_ge0 k : 0 <= Hk k.
Proof.
have := Lz_ge9; rewrite /Hk => h.
by rewrite mulr_ge0 ?divr_ge0 ?mulr_ge0 ?exprn_ge0 ?ler0n // addr_ge0
  ?mulr_ge0 ?ler0n // (le_trans _ h) // ler0n.
Qed.

Lemma uk_gt0 k : 0 < uk k.
Proof.
have l2 : 0 <= ln (2 : R) by rewrite ln_ge0 // ler1n.
have h := Hk_ge0 k.
have s0 : 0 < Num.sqrt m%:R :> R by rewrite sqrtr_gt0 ltr0n.
have kp : 0 < K * Num.sqrt m%:R * Lp.
  by rewrite !mulr_gt0 // ?(lt_le_trans ltr01 K1) ?(lt_le_trans ltr01 Lp_ge1).
rewrite /uk; apply: lt_le_trans kp _.
by rewrite lerDr addr_ge0 // mulr_ge0.
Qed.

Lemma tk_gt0 k : 0 < tk k.
Proof.
have u0 := uk_gt0 k.
have a0 : 0 <= alpha m k :> R by rewrite /alpha divr_ge0 ?exprn_ge0 ?sqrtr_ge0.
rewrite /tk; apply: lt_le_trans (_ : 0 < 8 * psi * Num.sqrt (uk k)) _.
  by rewrite !mulr_gt0 // sqrtr_gt0.
by rewrite lerDr !mulr_ge0 // ltW.
Qed.

Lemma tk_exp k : expR (- Num.min (tk k ^+ 2 / (64 * psi ^+ 2))
  (tk k / (4 * (alpha m k * psi)))) <= expR (- uk k).
Proof.
have u0 := uk_gt0 k.
have a0 : 0 < alpha m k :> R.
  by rewrite /alpha divr_gt0 ?exprn_gt0 // sqrtr_gt0 ltr0n.
have su : 0 <= Num.sqrt (uk k) := sqrtr_ge0 _.
rewrite ler_expR lerN2 le_min; apply/andP; split.
  (* t >= 8 psi sqrt u *)
  have h : 8 * psi * Num.sqrt (uk k) <= tk k.
    by rewrite /tk lerDr !mulr_ge0 // ?ltW.
  rewrite ler_pdivlMr ?mulr_gt0 ?exprn_gt0 //.
  apply: le_trans (_ : (8 * psi * Num.sqrt (uk k)) ^+ 2 <= _).
    rewrite !exprMn sqr_sqrtr; first exact: ltW u0.
    have -> : (8 : R) ^+ 2 = 64 by rewrite expr2 -natrM.
    by rewrite mulrC mulrA.
  have e0 : 0 <= 8 * psi * Num.sqrt (uk k) by rewrite !mulr_ge0 // ltW.
  by rewrite lerXn2r ?nnegrE // (le_trans e0 h).
(* t >= 4 psi alpha u *)
have h : 4 * psi * alpha m k * uk k <= tk k.
  by rewrite /tk lerDl !mulr_ge0 // ltW.
have d0 : 0 < 4 * (alpha m k * psi) by rewrite mulr_gt0 ?ltr0n // mulr_gt0.
rewrite ler_pdivlMr //.
apply: le_trans h; rewrite mulrC.
by rewrite [alpha m k * psi]mulrC mulrA.
Qed.

(* Each level weighs at most half of the previous one. *)
Lemma Hk_step r : Hk r.+1 <= Hk r / 2.
Proof.
have z := Lz_ge9.
have p4 : 0 < (4 : R) ^+ r by rewrite exprn_gt0.
have mR : 0 <= m%:R :> R := ler0n _ _.
rewrite /Hk exprS -[r.+1]addn1 natrD.
set a := 4 * m%:R / 4 ^+ r.
have -> : 4 * m%:R / (4 * 4 ^+ r) = a / 4.
  by rewrite /a; field; rewrite gt_eqF.
have a0 : 0 <= a by rewrite /a divr_ge0 ?mulr_ge0.
have r0 : 0 <= r%:R :> R := ler0n _ _.
nra.
Qed.

Lemma Hk_rev d : (d <= l)%N -> \sum_(j < d) Hk (l - j) <= 2 * Hk (l - d).+1.
Proof.
elim: d => [|d IH] dl; first by rewrite big_ord0 subn0 mulr_ge0 ?Hk_ge0.
rewrite big_ord_recr /=; apply: le_trans (lerD (IH (ltnW dl)) (lexx _)) _.
have e : (l - d.+1).+1 = (l - d)%N by rewrite subnS prednK // subn_gt0.
rewrite e; have := Hk_step (l - d); have := Hk_ge0 (l - d); lra.
Qed.

Lemma Hk_sum k : (k <= l)%N -> \sum_(k <= r < l.+1) Hk r <= 2 * Hk k.
Proof.
(* each level weighs at most half of the previous one *)
have Hstep r : Hk r.+1 <= Hk r / 2.
  have z := Lz_ge9.
  have p4 : 0 < (4 : R) ^+ r by rewrite exprn_gt0.
  have mR : 0 <= m%:R :> R := ler0n _ _.
  rewrite /Hk exprS -[r.+1]addn1 natrD.
  set a := 4 * m%:R / 4 ^+ r.
  have -> : 4 * m%:R / (4 * 4 ^+ r) = a / 4.
    by rewrite /a; field; rewrite gt_eqF.
  have a0 : 0 <= a by rewrite /a divr_ge0 ?mulr_ge0.
  have r0 : 0 <= r%:R :> R := ler0n _ _.
  nra.
move=> kl; have [d ld] : exists d, l = (k + d)%N.
  by exists (l - k)%N; rewrite subnKC.
elim: d k {kl} ld => [|d IH] k ld.
  rewrite ld addn0 big_nat1; have := Hk_ge0 k; lra.
rewrite big_ltn ?ld ?ltnS ?leq_addr //.
have := IH k.+1; rewrite addSnnS -ld => /(_ erefl) h.
have := Hstep k; have := Hk_ge0 k; lra.
Qed.

Lemma conf_size k : (k <= l)%N ->
  (size (@wconf R N m beta k ++ @xconf R N m l beta k))%:R <=
  2 * expR (2 * Hk k).
Proof.
move=> kl.
have b1 : beta <= 1.
  by apply: le_trans beta1 _; rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
have cE r : ccount N m beta r <= expR (Hk r) := ccount_le m0 beta0 r mN b1.
have cP r : 0 <= ccount N m beta r := le_trans ler01 (ccount_ge1 N m beta0 r).
rewrite size_cat natrD.
have hw := le_trans (size_wconf N m beta0 k) (cE k).
have hx := size_xconf N m l beta0 k.
have hp : \prod_(j < l - k) ccount N m beta (l - j) <=
    expR (\sum_(j < l - k) Hk (l - j)).
  rewrite expR_sum; apply: ler_prod => j _; rewrite cP /=; exact: cE.
have hs : \sum_(j < l - k) Hk (l - j) <= Hk k.
  apply: le_trans (Hk_rev (leq_subr k l)) _.
  rewrite subKn //; have := Hk_step k; have := Hk_ge0 k; lra.
have h1 : (size (xconf N m l beta k))%:R <= expR (2 * Hk k).
  apply: le_trans hx _.
  apply: le_trans (ler_pM (cP k) _ (cE k) hp) _.
    by apply: prodr_ge0 => j _; exact: cP.
  by rewrite -expRD ler_expR; lra.
have h2 : (size (wconf N m beta k))%:R <= expR (2 * Hk k).
  by apply: le_trans hw _; rewrite ler_expR; have := Hk_ge0 k; lra.
lra.
Qed.

Lemma tk_sum : \sum_(0 <= k < l.+1) tk k <=
  2100 * K * psi * Num.sqrt m%:R * (Lp - ln beta).
Proof.
set sm := Num.sqrt m%:R.
have mR : 0 < m%:R :> R by rewrite ltr0n.
have s0 : 0 < sm by rewrite sqrtr_gt0.
have smm : sm ^+ 2 = m%:R by rewrite sqr_sqrtr // ltW.
have s1 : 1 <= sm by rewrite -sqrtr1 ler_wsqrtr // ler1n.
have Lp1 := Lp_ge1; have Lz9 := Lz_ge9.
have b1 : beta <= 1.
  by apply: le_trans beta1 _; rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
have lb : 0 <= - ln beta by rewrite oppr_ge0 ln_le0.
have l2 := @ln2_le1 R.
have l20 : 0 <= ln (2 : R) by rewrite ln_ge0 // ler1n.
(* 2^l <= 2 sqrt m *)
have pl : (2 : R) ^+ l <= 2 * sm.
  have q1 : 0 <= (2 : R) ^+ l by rewrite exprn_ge0.
  have q2 : 0 <= 2 * sm by rewrite mulr_ge0 // ltW.
  rewrite -(ler_pXn2r (n := 2)) ?nnegrE //.
  rewrite exprMn smm -exprM mulnC exprM.
  have -> : (2 : R) ^+ 2 = 4 by rewrite expr2 -natrM.
  by rewrite -natrX -natrM ler_nat.
have aE k : alpha m k = 2 ^+ k / sm :> R by [].
have p2 k : 0 < (2 : R) ^+ k by rewrite exprn_gt0.
(* the sums of alpha k, of alpha k H k and of sqrt (2 H k) *)
have sa : \sum_(0 <= k < l.+1) alpha m k <= 4 :> R.
  rewrite big_mkord -mulr_suml; apply: le_trans (_ : 2 ^+ l.+1 / sm <= _).
    apply: ler_wpM2r; first by rewrite invr_ge0 ltW.
    exact: sum_pow2.
  rewrite ler_pdivrMr // exprS; nra.
have aH k : alpha m k * Hk k = 4 * sm * ((Lz + 3 * k%:R) / 2 ^+ k).
  have e4 : (4 : R) ^+ k = (2 ^+ k) ^+ 2.
    by rewrite -exprM mulnC exprM (_ : (2 : R) ^+ 2 = 4) // expr2 -natrM.
  rewrite aE /Hk -smm e4.
  have h1 : sm != 0 by rewrite gt_eqF.
  have h2 : (2 : R) ^+ k != 0 by rewrite gt_eqF.
  by field; rewrite h1 h2.
have sg : \sum_(0 <= k < l.+1) (Lz + 3 * k%:R) / 2 ^+ k <= 4 * Lz.
  have h6 : (6 : R) <= Lz by apply: (le_trans _ Lz9); rewrite ler_nat.
  by rewrite big_mkord; apply: sum_geo_lin.
have sah : \sum_(0 <= k < l.+1) alpha m k * Hk k <= 16 * sm * Lz.
  under eq_bigr do rewrite aH.
  rewrite -mulr_sumr; apply: le_trans (ler_wpM2l _ sg) _.
    by rewrite mulr_ge0 // ltW.
  by rewrite mulrA mulrAC -mulrA; nra.
have sq2 k : Num.sqrt (2 * Hk k) <= 3 * sm * ((Lz + 3 * k%:R) / 2 ^+ k).
  set y := Lz + 3 * k%:R.
  have k0 : 0 <= k%:R :> R := ler0n _ _.
  have y9 : 9 <= y by rewrite /y; lra.
  have hk0 := Hk_ge0 k.
  have y0 : 0 <= y by lra.
  have r0 : 0 <= 3 * sm * (y / 2 ^+ k).
    by rewrite mulr_ge0 ?divr_ge0 // ?mulr_ge0 // ltW.
  rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?sqrtr_ge0 //.
  rewrite sqr_sqrtr; first by rewrite mulr_ge0.
  have e4 : (4 : R) ^+ k = (2 ^+ k) ^+ 2.
    by rewrite -exprM mulnC exprM (_ : (2 : R) ^+ 2 = 4) // expr2 -natrM.
  rewrite /Hk -/y e4 -smm.
  set c := sm ^+ 2 / (2 ^+ k) ^+ 2.
  have c0 : 0 <= c by rewrite /c divr_ge0 ?exprn_ge0 // ltW.
  have -> : 2 * (4 * sm ^+ 2 / 2 ^+ k ^+ 2 * y) = 8 * c * y.
    by rewrite /c; field; rewrite gt_eqF.
  have -> : (3 * sm * (y / 2 ^+ k)) ^+ 2 = 9 * c * y ^+ 2.
    by rewrite /c; field; rewrite gt_eqF.
  have hy : 0 <= 9 * y ^+ 2 - 8 * y by nra.
  have := mulr_ge0 c0 hy.
  nra.
(* the term of the K sqrt m Lp part: (l + 1) sqrt (2 w) <= 6 w *)
set w := K * sm * Lp.
have w1 : sm <= w.
  rewrite /w -[X in X <= _]mul1r -mulrA mulrC [K * _]mulrC -mulrA.
  apply: ler_wpM2l; first exact: ltW.
  have hL : 0 <= Lp - 1 by rewrite subr_ge0.
  have hK : 0 <= K - 1 by rewrite subr_ge0.
  by have := mulr_ge0 hL hK; nra.
have lw : (l.+1)%:R * Num.sqrt (2 * w) <= 6 * w.
  have hl : (l.+1)%:R ^+ 2 <= 16 * sm :> R.
    have := sq_le_pow2 l; rewrite -(ler_nat R) natrM !natrX => h.
    have h' := h R; clear h; apply: le_trans h' _; lra.
  have w0 : 0 <= w by lra.
  have l0 : 0 <= (l.+1)%:R :> R := ler0n _ _.
  rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?mulr_ge0 ?sqrtr_ge0 //.
  - exact: le_trans ler01 K1.
  - exact: le_trans ler01 Lp1.
  rewrite exprMn sqr_sqrtr; first by rewrite mulr_ge0.
  nra.
have sqD (a b : R) : 0 <= a -> 0 <= b ->
    Num.sqrt (a + b) <= Num.sqrt a + Num.sqrt b.
  move=> a0 b0; rewrite -(ler_pXn2r (n := 2)) ?nnegrE ?addr_ge0 ?sqrtr_ge0 //.
  rewrite sqr_sqrtr ?addr_ge0 // sqrrD !sqr_sqrtr //.
  by rewrite -addrA lerD2l lerDr mulrn_wge0 // mulr_ge0 ?sqrtr_ge0.
(* the bound on each t k *)
have tkb k : tk k <= 4 * psi * alpha m k * (ln 2 + w) +
    8 * psi * (alpha m k * Hk k) +
    8 * psi * (Num.sqrt (2 * w) + Num.sqrt (2 * Hk k)).
  have hk := Hk_ge0 k.
  have w0 : 0 <= w by apply: le_trans (ltW s0) w1.
  have su : Num.sqrt (uk k) <= Num.sqrt (2 * w) + Num.sqrt (2 * Hk k).
    have -> : uk k = 2 * Hk k + (ln 2 + w) by rewrite /uk -/w; ring.
    have h2 : 0 <= 2 * Hk k by rewrite mulr_ge0.
    have h3 : 0 <= ln 2 + w by rewrite addr_ge0.
    apply: le_trans (sqD _ _ h2 h3) _.
    rewrite addrC lerD2r; apply: ler_wsqrtr.
    by rewrite mulr2n mulrDl mul1r lerD2r (le_trans l2) // (le_trans s1).
  rewrite /tk; apply: lerD; last first.
    by apply: ler_wpM2l => //; rewrite mulr_ge0 // ltW.
  have e : uk k = ln 2 + w + 2 * Hk k by rewrite /uk -/w; ring.
  have a0 : 0 <= alpha m k :> R.
    by rewrite /alpha divr_ge0 ?exprn_ge0 ?sqrtr_ge0.
  rewrite e mulrDr; apply: lerD => //.
  have -> : 4 * psi * alpha m k * (2 * Hk k) =
    8 * psi * (alpha m k * Hk k) by ring.
  exact: lexx.
(* summation *)
apply: le_trans (ler_sum _ (fun k _ => tkb k)) _.
rewrite !big_split /= -!mulr_sumr -mulr_suml big_split /=.
have s2w : \sum_(0 <= k < l.+1) Num.sqrt (2 * w) =
    (l.+1)%:R * Num.sqrt (2 * w).
  rewrite big_const_nat subn0 iter_addr addr0.
  by rewrite [RHS]mulr_natl.
have s2h : \sum_(0 <= k < l.+1) Num.sqrt (2 * Hk k) <= 12 * sm * Lz.
  apply: le_trans (ler_sum _ (fun k _ => sq2 k)) _.
  rewrite -mulr_sumr; apply: le_trans (ler_wpM2l _ sg) _.
    by rewrite mulr_ge0 // ltW.
  have -> : 3 * sm * (4 * Lz) = 12 * sm * Lz by ring.
  exact: lexx.
rewrite s2w -mulr_sumr.
set SA := \sum_(0 <= i < l.+1) alpha m i in sa *.
set SH := \sum_(0 <= i < l.+1) alpha m i * Hk i in sah *.
set S2 := \sum_(0 <= i < l.+1) Num.sqrt (2 * Hk i) in s2h *.
set Q := (l.+1)%:R * Num.sqrt (2 * w) in lw *.
clear aE aH sg sq2 sqD tkb s2w.
have SA0 : 0 <= SA.
  rewrite /SA; apply: sumr_ge0 => i _.
  by rewrite /alpha divr_ge0 ?exprn_ge0 ?sqrtr_ge0.
have w0 : 0 <= w by apply: le_trans (ltW s0) w1.
have LzE : Lz = Lp + 8 - ln beta by rewrite /Lz /Lp; ring.
have key : 16 * ln 2 + 64 * w + 224 * sm * Lz <=
    2100 * K * sm * (Lp - ln beta).
  rewrite LzE /w.
  set lam := - ln beta in lb *.
  have sm0 := ltW s0.
  have K0 : 0 <= K - 1 by rewrite subr_ge0.
  have L0 : 0 <= Lp - 1 by rewrite subr_ge0.
  have h1 : 0 <= (K - 1) * (sm * Lp).
    by apply: mulr_ge0 => //; apply: mulr_ge0 => //; exact: le_trans ler01 Lp1.
  have h2 : 0 <= sm * (Lp - 1) by apply: mulr_ge0.
  have h4 : 0 <= sm * lam by apply: mulr_ge0.
  have h3 : 0 <= (K - 1) * (sm * lam) by apply: mulr_ge0.
  nra.
have p0 := ltW psi0.
have lw0 : 0 <= ln 2 + w by rewrite addr_ge0.
have e1 : 4 * psi * SA * (ln 2 + w) <= 16 * psi * (ln 2 + w).
  have := ler_wpM2r lw0 (ler_wpM2l (mulr_ge0 (ler0n R 4) p0) sa).
  move=> h; apply: le_trans h _.
  have -> : 4 * psi * 4 * (ln 2 + w) = 16 * psi * (ln 2 + w) by ring.
  exact: lexx.
have e2 : 8 * psi * SH <= 8 * psi * (16 * sm * Lz).
  by apply: ler_wpM2l => //; rewrite mulr_ge0.
have e3 : 8 * psi * (Q + S2) <= 8 * psi * (6 * w + 12 * sm * Lz).
  by apply: ler_wpM2l; rewrite ?mulr_ge0 // lerD.
have e4 : psi * (16 * ln 2 + 64 * w + 224 * sm * Lz) <=
    psi * (2100 * K * sm * (Lp - ln beta)) by exact: ler_wpM2l.
have -> : 2100 * K * psi * sm * (Lp - ln beta) =
    psi * (2100 * K * sm * (Lp - ln beta)) by ring.
apply: le_trans e4; lra.
Qed.

End parameters.

Section restricted_isometry.
Context {R : realType} (N n m : nat) (mu : nat -> probability 'rV[R]_n R)
  (psi : R).
Hypothesis psi0 : 0 < psi.
Hypothesis sub : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  subexponential (mu i) (fun v => mxdot v y) psi.
Hypothesis cen : forall i (y : 'rV[R]_n), (i < N)%N -> mxdot y y = 1 ->
  \int[mu i]_v mxdot v y = 0.

(* The scale T = 2100 K psi sqrt m (ln (e N / m) + ln (1 / beta)). *)
Definition rip_T (beta K : R) : R :=
  2100 * K * psi * Num.sqrt m%:R * (1 + ln (N%:R / m%:R) - ln beta).

(* Theorem 5.1 of Adamczak, Litvak, Pajor and Tomczak-Jaegermann for psi_1
   columns, with explicit constants. *)
Theorem restricted_isometry (beta K : R) : (0 < m)%N -> (m <= N)%N ->
  0 < beta -> beta <= 1 / 2 -> 1 <= K ->
  exists G : set (N.-tuple 'rV[R]_n), [/\ measurable G,
    (tuple_prod mu N (~` G) <= (2 * (trunc_log 4 m).+2%:R *
      expR (- (K * Num.sqrt m%:R * (1 + ln (N%:R / m%:R)))))%:E)%E &
    forall x, G x -> rip_const m x <=
      256 * rip_T beta K ^+ 2 + 32 * rip_T beta K * maxnorm x +
      8 * beta * maxnorm x ^+ 2].
Proof.
move=> m0 mN beta0 beta1 K1.
(* the levels 0, ..., l with 4^(l - 1) <= m < 4^l *)
set l := (trunc_log 4 m).+1.
have ml : (m <= 4 ^ l)%N by rewrite ltnW // trunc_log_ltn.
have lm : (4 ^ l <= 4 * m)%N by rewrite /l expnS leq_mul2l /= trunc_logP.
pose t := tk N m psi beta K.
have t0 k : 0 < t k by exact: tk_gt0.
have mb : measurable (@bad_event R N n m l beta t) :=
  measurable_bad_event m l beta t0.
exists (~` bad_event m l beta t); split.
- exact: measurableC.
- (* the union bound *)
  rewrite setCK; apply: le_trans (bad_event_le m l psi0 sub cen beta0 t0) _.
  rewrite lee_fin.
  set X := K * Num.sqrt m%:R * (1 + ln (N%:R / m%:R)).
  apply: le_trans (_ : \sum_(k < l.+1) 2 * expR (- X) <= _); last first.
    rewrite sumr_const card_ord.
    have -> : 2 * expR (- X) *+ l.+1 = 2 * l.+1%:R * expR (- X).
      by rewrite -mulr_natl; ring.
    exact: lexx.
  apply: ler_sum => k _.
  have kl : (k <= l)%N by rewrite -ltnS.
  have h1 := conf_size m0 mN beta0 beta1 kl.
  have h2 := tk_exp m0 mN psi0 beta1 K1 k.
  apply: le_trans (ler_pM _ _ h1 (ler_wpM2l _ h2)) _.
  + exact: ler0n.
  + by rewrite mulr_ge0 ?expR_ge0.
  + by rewrite ler0n.
  rewrite /uk -/X.
  have -> : 2 * expR (2 * Hk N m beta k) *
      (2 * expR (- (ln 2 + 2 * Hk N m beta k + X))) =
      4 * expR (- ln 2) * expR (- X).
    set H := Hk N m beta k.
    have -> : - (ln 2 + 2 * H + X) = - ln 2 + - (2 * H) + - X by ring.
    rewrite !expRD [expR (- (2 * H))]expRN.
    have e0 : expR (2 * H) != 0 by rewrite gt_eqF ?expR_gt0.
    by field.
  rewrite expRN lnK ?posrE //.
  have -> : 4 * 2^-1 * expR (- X) = 2 * expR (- X) :> R by field.
  exact: lexx.
- (* outside the bad event *)
  move=> x Gx.
  have h := rip_good m0 ml beta0 beta1 t0 Gx.
  have hT := tk_sum m0 mN lm psi0 beta1 K1.
  have T0 : 0 <= \sum_(0 <= k < l.+1) t k.
    by apply: sumr_ge0 => k _; exact: ltW.
  have C0 := maxnorm_ge0 x.
  apply: le_trans h _.
  have eT : rip_T beta K =
    2100 * K * psi * Num.sqrt m%:R * (Lp N m - ln beta) by [].
  rewrite eT; set T' := \sum_(0 <= k < l.+1) t k in T0 hT *.
  set T := 2100 * K * psi * Num.sqrt m%:R * (Lp N m - ln beta) in hT *.
  have TT : T' ^+ 2 <= T ^+ 2 by rewrite lerXn2r ?nnegrE // (le_trans T0).
  rewrite lerD2r lerD ?ler_wpM2l ?ler_wpM2r //.
  by rewrite ler_wpM2l.
Qed.

End restricted_isometry.

