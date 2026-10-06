From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear archimedean boolp classical_sets.
From mathcomp Require Import reals sequences exp ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.

(**md**************************************************************************)
(* # Nets in Euclidean spaces                                                 *)
(*                                                                            *)
(* A finite eps-net of a set S of column vectors is a finite sequence N such  *)
(* that every point of S lies within Euclidean distance eps of a point of N.  *)
(* The operator norm of a matrix is controlled by its values on a net of the  *)
(* unit ball or of the unit sphere (opnorm_net, opnorm_net_bilinear,          *)
(* opnorm_net_sphere, opnorm_net_sym). Every set in the ball of radius r of   *)
(* 'cV[R]_n has an eps-net of at most (2 e (1 + 2 r / eps))^n of its own      *)
(* points (net_exists, unit_ball_net, unit_sphere_net). The proof rounds each *)
(* point to a grid of mesh h = eps / (2 sqrt n) and counts the grid points: a *)
(* point of the ball has at most 2^n C(n + k, n) possible roundings, with k = *)
(* floor(2 n r / eps).                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*      is_net S N eps == every x in S has a point y of N with                *)
(*                        frobenius (x - y) <= eps                            *)
(*        unit_ball n == the closed unit ball [set x | frobenius x <= 1] of   *)
(*                        'cV[R]_n                                            *)
(*      unit_sphere n == the unit sphere [set x | frobenius x = 1] of         *)
(*                        'cV[R]_n                                            *)
(*         budget n k == the lists of n natural numbers with sum at most k    *)
(*       sign_lists n == the lists of n booleans                              *)
(* grid_point h (a, s) == the column with coordinates (-1)^(s_i) h a_i        *)
(*      grid_code h x == the code (a, s) of the column x: a_i is the integer  *)
(*                        part of |x_i| / h, and s_i says whether x_i < 0     *)
(*     grid_codes n k == the codes (a, s) with a in budget n k                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section nets.
Variable R : realType.
Implicit Types m n : nat.

Definition is_net n (S : set 'cV[R]_n) (N : seq 'cV[R]_n) (eps : R) :=
  forall x, S x -> exists2 y, y \in N & frobenius (x - y) <= eps.

Definition unit_ball n : set 'cV[R]_n := [set x | frobenius x <= 1].

Lemma unit_ball0 n : @unit_ball n 0.
Proof. by rewrite /unit_ball /= frobenius0 ler01. Qed.

Definition unit_sphere n : set 'cV[R]_n := [set x | frobenius x = 1].

Lemma unit_sphere_ball n : @unit_sphere n `<=` @unit_ball n.
Proof. by move=> x; rewrite /unit_sphere /unit_ball /= => ->. Qed.

Lemma is_net_sub n (S T : set 'cV[R]_n) N eps :
  S `<=` T -> is_net T N eps -> is_net S N eps.
Proof. by move=> ST TN x /ST/TN. Qed.

Lemma is_net_le n (S : set 'cV[R]_n) N eps eps' :
  eps <= eps' -> is_net S N eps -> is_net S N eps'.
Proof. by move=> ee SN x /SN[y yN xy]; exists y => //; exact: le_trans ee. Qed.

(* The values of A on a net of the unit ball control its operator norm. *)
Lemma opnorm_net m n (A : 'M[R]_(m, n)) (N : seq 'cV[R]_n) (eps b : R) :
  0 <= eps < 1 -> is_net (@unit_ball n) N eps ->
  (forall y, y \in N -> frobenius (A *m y) <= b) ->
  opnorm A <= b / (1 - eps).
Proof.
move=> /andP[e0 e1] AN Ab; have e1' : 0 < 1 - eps by rewrite subr_gt0.
have : opnorm A <= b + opnorm A * eps.
  apply: opnorm_le => x /AN[y yN xy].
  rewrite -[x](subrK y) mulmxDr addrC (le_trans (frobeniusD _ _)) //.
  rewrite lerD ?Ab //.
  by rewrite (le_trans (frobenius_mulmx_opnorm _ _)) // ler_wpM2l ?opnorm_ge0.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

Lemma mxdot_net_bound m n (A : 'M[R]_(m, n)) (y u : 'cV[R]_m) (x v : 'cV[R]_n) :
  frobenius y <= 1 -> frobenius x <= 1 -> frobenius u <= 1 ->
  `|mxdot y (A *m x)| <=
    `|mxdot u (A *m v)| + opnorm A * (frobenius (y - u) + frobenius (x - v)).
Proof.
move=> y1 x1 u1.
have -> : mxdot y (A *m x) =
    mxdot u (A *m v) + mxdot (y - u) (A *m x) + mxdot u (A *m (x - v)).
  by rewrite mulmxBr mxdotBl mxdotBr; ring.
rewrite -addrA (le_trans (ler_normD _ _)) // lerD2l mulrDr.
rewrite (le_trans (ler_normD _ _)) // lerD //.
  rewrite (le_trans (mxdot_opnorm _ _ _)) // -mulrA ler_wpM2l ?opnorm_ge0 //.
  by rewrite -[leRHS]mulr1 ler_wpM2l ?frobenius_ge0.
rewrite (le_trans (mxdot_opnorm _ _ _)) // -mulrA ler_wpM2l ?opnorm_ge0 //.
by rewrite -[leRHS]mul1r ler_wpM2r ?frobenius_ge0.
Qed.

(* Bilinear values on nets of both unit spheres control the operator norm. *)
Lemma opnorm_net_sphere m n (A : 'M[R]_(m, n)) (U : seq 'cV[R]_m)
    (V : seq 'cV[R]_n) (eps b : R) :
  0 <= eps -> 2 * eps < 1 -> 0 <= b ->
  is_net (@unit_sphere m) U eps -> (forall u, u \in U -> frobenius u <= 1) ->
  is_net (@unit_sphere n) V eps ->
  (forall u v, u \in U -> v \in V -> `|mxdot u (A *m v)| <= b) ->
  opnorm A <= b / (1 - 2 * eps).
Proof.
move=> e0 e1 b0 UN Ub VN Ab.
have e1' : 0 < 1 - 2 * eps by rewrite subr_gt0.
have : opnorm A <= b + opnorm A * (2 * eps).
  apply: opnorm_le => x x1.
  have [Ax0|Axn0] := eqVneq (A *m x) 0.
    by rewrite Ax0 frobenius0 addr_ge0 ?mulr_ge0 ?opnorm_ge0.
  have x0 : x != 0 by apply: contraNneq Axn0 => ->; rewrite mulmx0.
  have xp : 0 < frobenius x by rewrite frobenius_gt0.
  set z := (frobenius x)^-1 *: x.
  have z1 : frobenius z = 1.
    by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
  have xz : A *m x = frobenius x *: (A *m z).
    by rewrite /z -scalemxAr scalerA mulfV ?gt_eqF // scale1r.
  have Azn0 : A *m z != 0.
    by apply: contraNneq Axn0; rewrite xz => ->; rewrite scaler0.
  have Az_gt0 : 0 < frobenius (A *m z) by rewrite frobenius_gt0.
  rewrite xz frobeniusZ ger0_norm ?frobenius_ge0 //.
  apply: le_trans (_ : frobenius (A *m z) <= _).
    by rewrite -[leRHS]mul1r ler_wpM2r ?frobenius_ge0.
  set y := (frobenius (A *m z))^-1 *: (A *m z).
  have y1 : frobenius y = 1.
    by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
  have yE : frobenius (A *m z) = mxdot y (A *m z).
    by rewrite /y mxdotZl -frobenius_sqr expr2 mulKf ?gt_eqF.
  have [u uU yu] := UN y y1; have [v vV zv] := VN z z1.
  rewrite yE (le_trans (ler_norm _)) //.
  have y1' : frobenius y <= 1 by rewrite y1.
  have z1' : frobenius z <= 1 by rewrite z1.
  rewrite (le_trans (mxdot_net_bound A v y1' z1' (Ub u uU))) //.
  by rewrite lerD ?Ab // ler_wpM2l ?opnorm_ge0 // mulrDl mul1r lerD.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

(* Bilinear values on nets of both unit balls control the operator norm. *)
Lemma opnorm_net_bilinear m n (A : 'M[R]_(m, n)) (U : seq 'cV[R]_m)
    (V : seq 'cV[R]_n) (eps b : R) :
  0 <= eps -> 2 * eps < 1 ->
  is_net (@unit_ball m) U eps -> (forall u, u \in U -> frobenius u <= 1) ->
  is_net (@unit_ball n) V eps ->
  (forall u v, u \in U -> v \in V -> `|mxdot u (A *m v)| <= b) ->
  opnorm A <= b / (1 - 2 * eps).
Proof.
move=> e0 e1 UN Ub VN Ab; apply: (@opnorm_net_sphere m n A U V) => //.
- have [u uU _] := UN 0 (unit_ball0 m); have [v vV _] := VN 0 (unit_ball0 n).
  exact: le_trans (normr_ge0 _) (Ab u v uU vV).
- exact: is_net_sub (@unit_sphere_ball m) UN.
- exact: is_net_sub (@unit_sphere_ball n) VN.
Qed.

Lemma form_unit_ball_le n (A : 'M[R]_n) (c : R) :
  (forall x : 'cV[R]_n, frobenius x <= 1 -> `|mxdot x (A *m x)| <= c) ->
  forall x : 'cV[R]_n, `|mxdot x (A *m x)| <= c * mxdot x x.
Proof.
move=> Ac x; have [->|x0] := eqVneq x 0; first by rewrite !mxdot0l normr0 mulr0.
have xp : 0 < frobenius x by rewrite frobenius_gt0.
set z := (frobenius x)^-1 *: x.
have z1 : frobenius z <= 1.
  by rewrite frobeniusZ ger0_norm ?invr_ge0 ?frobenius_ge0 // mulVf ?gt_eqF.
have := Ac z z1; rewrite /z -scalemxAr mxdotZl mxdotZr mulrA normrM.
rewrite ger0_norm ?mulr_ge0 ?invr_ge0 ?frobenius_ge0 //.
rewrite -invfM -expr2 frobenius_sqr.
by rewrite mulrC ler_pdivrMr ?mxdot_gt0 // mulrC.
Qed.

(* Values of the quadratic form on a net of the unit ball control the
   operator norm of a symmetric matrix. *)
Lemma opnorm_net_sym n (A : 'M[R]_n) (V : seq 'cV[R]_n) (eps b : R) :
  A \is symmetricmx -> 0 <= eps -> 2 * eps < 1 ->
  is_net (@unit_ball n) V eps -> (forall v, v \in V -> frobenius v <= 1) ->
  (forall v, v \in V -> `|mxdot v (A *m v)| <= b) ->
  opnorm A <= b / (1 - 2 * eps).
Proof.
move=> Asym e0 e1 VN Vb Ab.
have e1' : 0 < 1 - 2 * eps by rewrite subr_gt0.
have b0 : 0 <= b.
  have [v vV _] := VN 0 (unit_ball0 n).
  exact: le_trans (normr_ge0 _) (Ab v vV).
have : opnorm A <= b + opnorm A * (2 * eps).
  apply/opnorm_symP => //; first by rewrite addr_ge0 ?mulr_ge0 ?opnorm_ge0.
  apply: form_unit_ball_le => x x1; have [v vV xv] := VN x x1.
  rewrite (le_trans (mxdot_net_bound A v x1 x1 (Vb v vV))) //.
  by rewrite lerD ?Ab // ler_wpM2l ?opnorm_ge0 // mulrDl mul1r lerD.
by rewrite ler_pdivlMr // mulrBr mulr1 lerBlDr.
Qed.

End nets.

(* Lists of natural numbers with a bounded sum, and lists of signs: the codes
   of the points of a grid. *)
Section codes.

Fixpoint budget (n k : nat) : seq (seq nat) :=
  if n is n'.+1 then
    flatten [seq [seq a :: t | t <- budget n' (k - a)] | a <- iota 0 k.+1]
  else [:: [::]].

Lemma mem_budget n k (a : seq nat) :
  size a = n -> (sumn a <= k)%N -> a \in budget n k.
Proof.
elim: n k a => [|n IH] k [|x a] // sa sk.
apply/flattenP; exists [seq x :: t | t <- budget n (k - x)].
  apply/mapP; exists x => //; rewrite mem_iota /= add0n ltnS.
  exact: leq_trans (leq_addr _ _) sk.
apply/mapP; exists a => //; apply: IH; first by case: sa.
by rewrite -(leq_add2l x) subnKC // (leq_trans (leq_addr _ _) sk).
Qed.

(* The hockey-stick identity. *)
Lemma sum_bin_hockey n k :
  (\sum_(a < k.+1) 'C(n + (k - a), n) = 'C(n.+1 + k, n.+1))%N.
Proof.
elim: k => [|k IH]; first by rewrite big_ord1 !addn0 !binn.
rewrite big_ord_recl subn0.
under eq_bigr => a _ do rewrite lift0 /= subSS.
by rewrite IH !addSn !addnS binS addnC.
Qed.

Lemma size_budget n k : size (budget n k) = 'C(n + k, n).
Proof.
elim: n k => [|n IH] k; first by rewrite bin0.
rewrite /budget -/budget size_flatten /shape -map_comp sumnE big_map.
rewrite -[iota 0 k.+1]/(index_iota 0 k.+1) big_mkord.
under eq_bigr do rewrite /= size_map IH.
by rewrite sum_bin_hockey.
Qed.

Fixpoint sign_lists (n : nat) : seq (seq bool) :=
  if n is n'.+1 then [seq b :: s | b <- [:: false; true], s <- sign_lists n']
  else [:: [::]].

Lemma size_sign_lists n : size (sign_lists n) = 2 ^ n.
Proof.
by elim: n => // n IH; rewrite /sign_lists -/sign_lists size_allpairs IH expnS.
Qed.

Lemma mem_sign_lists n (s : seq bool) : size s = n -> s \in sign_lists n.
Proof.
elim: n s => [|n IH] [|b s] // [sn]; rewrite /sign_lists -/sign_lists.
by apply: (allpairs_f (fun b s => b :: s)); rewrite ?IH // !inE; case: b.
Qed.

Lemma leq_ffact_expn m n : (m ^_ n <= m ^ n)%N.
Proof.
elim: n m => [|n IH] m //; rewrite ffactnS expnS leq_mul2l.
apply/orP; right; apply: leq_trans (IH _) _.
by case: n {IH} => [|n]; rewrite ?expn0 // leq_exp2r // leq_pred.
Qed.

End codes.

Section binomial_bound.
Variable R : realType.

(* 'C(m, n) <= (e m / n)^n. *)
Lemma bin_le_expR m n : ('C(m, n))%:R <= (expR 1 * m%:R / n%:R) ^+ n :> R.
Proof.
case: n => [|n]; first by rewrite bin0 expr0.
have f0 : 0 < (n.+1)`!%:R :> R by rewrite ltr0n fact_gt0.
have n0 : 0 < n.+1%:R :> R by rewrite ltr0n.
have H := @expR_ge1Dxn R n.+1%:R n (ler0n _ _).
have E : expR n.+1%:R = expR 1 ^+ n.+1 :> R by rewrite -expRM_natl mulr1.
rewrite E in H.
have Hf : n.+1%:R ^+ n.+1 / (n.+1)`!%:R <= expR 1 ^+ n.+1 :> R.
  by apply: le_trans H; rewrite lerDr.
have Cf : ('C(m, n.+1))%:R * (n.+1)`!%:R <= m%:R ^+ n.+1 :> R.
  by rewrite -natrM bin_ffact -natrX ler_nat leq_ffact_expn.
rewrite expr_div_n exprMn ler_pdivlMr ?exprn_gt0 //.
rewrite ler_pdivrMr // in Hf.
apply: le_trans (_ : 'C(m, n.+1)%:R * (expR 1 ^+ n.+1 * (n.+1)`!%:R) <= _).
  by rewrite ler_wpM2l ?ler0n.
by rewrite mulrCA ler_wpM2l ?exprn_ge0 ?expR_ge0.
Qed.

End binomial_bound.

Section net_existence.
Variable R : realType.
Implicit Types n : nat.

(* The grid point of mesh h with code (a, s): its i-th coordinate is
   h * a_i, with the sign - if s_i holds. *)
Definition grid_point n (h : R) (c : seq nat * seq bool) : 'cV[R]_n :=
  \col_(i < n) ((-1) ^+ nth false c.2 i * (h * (nth 0%N c.1 i)%:R)).
Arguments grid_point {n}.

(* The code of x: the integer parts of the |x_i| / h and the signs of the
   x_i. Its grid point is within h of x in each coordinate. *)
Definition grid_code n (h : R) (x : 'cV[R]_n) : seq nat * seq bool :=
  ([seq Num.truncn (`|x i 0| / h) | i <- enum 'I_n],
   [seq x i 0 < 0 | i <- enum 'I_n]).

Lemma grid_point_code n (h : R) (x : 'cV[R]_n) i :
  grid_point h (grid_code h x) i 0 =
    (-1) ^+ (x i 0 < 0)%R * (h * (Num.truncn (`|x i 0| / h))%:R).
Proof.
rewrite mxE /= (nth_map i) ?size_enum_ord // (nth_map i) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Lemma grid_code_near n (h : R) (x : 'cV[R]_n) i :
  0 < h -> `|x i 0 - grid_point h (grid_code h x) i 0| <= h.
Proof.
move=> h0; rewrite grid_point_code {1}(numEsign (x i 0)) -mulrBr normrM normrX.
rewrite normrN1 expr1n mul1r.
have := truncn_itv (divr_ge0 (normr_ge0 (x i 0)) (ltW h0)).
set t := Num.truncn _ => /andP[t1 t2].
rewrite (@ger0_norm _ (`|x i 0| - h * t%:R)).
  by rewrite subr_ge0 mulrC -ler_pdivlMr.
rewrite lerBlDl -[X in _ <= _ + X]mulr1 -mulrDr mulrC -ler_pdivrMr //.
by apply: ltW; rewrite natr1.
Qed.

Lemma frobenius_col_sqr n (x : 'cV[R]_n) :
  frobenius x ^+ 2 = \sum_i x i 0 ^+ 2.
Proof.
by rewrite frobenius_sqr /mxdot; apply: eq_bigr => i _; rewrite big_ord1 expr2.
Qed.

Lemma grid_code_dist n (h : R) (x : 'cV[R]_n) :
  0 < h -> frobenius (x - grid_point h (grid_code h x)) ^+ 2 <= n%:R * h ^+ 2.
Proof.
move=> h0; rewrite frobenius_col_sqr.
have -> : n%:R * h ^+ 2 = \sum_(i < n) h ^+ 2.
  by rewrite sumr_const card_ord mulr_natl.
apply: ler_sum => i _; rewrite mxE -real_normK ?num_real // mxE.
by rewrite lerXn2r ?nnegrE ?(ltW h0) //; exact: grid_code_near.
Qed.

Lemma sum_abs_col_le n (x : 'cV[R]_n) :
  \sum_i `|x i 0| <= Num.sqrt n%:R * frobenius x.
Proof.
rewrite -(@ler_pXn2r _ 2) ?nnegrE ?sumr_ge0 ?mulr_ge0 ?sqrtr_ge0
  ?frobenius_ge0 //.
rewrite exprMn sqr_sqrtr ?ler0n // frobenius_col_sqr.
have := sum_cauchy_schwarz (fun=> 1) (fun i => `|x i 0|).
under eq_bigr do rewrite mul1r.
under [X in _ <= X * _]eq_bigr do rewrite mulr1.
rewrite sumr_const card_ord.
under [X in _ <= _ * X]eq_bigr do rewrite -expr2 real_normK ?num_real //.
done.
Qed.

(* The codes of the grid points: n naturals with sum at most k, and n
   signs. *)
Definition grid_codes n k : seq (seq nat * seq bool) :=
  [seq (a, s) | a <- budget n k, s <- sign_lists n].

Lemma size_grid_codes n k : size (grid_codes n k) = ('C(n + k, n) * 2 ^ n)%N.
Proof. by rewrite size_allpairs size_budget size_sign_lists. Qed.

Lemma grid_code_mem n k (h : R) (x : 'cV[R]_n) : 0 < h ->
  \sum_i `|x i 0| < k.+1%:R * h -> grid_code h x \in grid_codes n k.
Proof.
move=> h0 xk; apply: allpairs_f; last first.
  by apply: mem_sign_lists; rewrite size_map size_enum_ord.
apply: mem_budget; first by rewrite size_map size_enum_ord.
rewrite -ltnS -(ltr_nat R) sumnE big_map big_enum natr_sum.
apply: le_lt_trans (_ : \sum_i `|x i 0| / h < _).
  by apply: ler_sum => i _; rewrite truncn_le divr_ge0 // ltW.
by rewrite -mulr_suml ltr_pdivrMr.
Qed.

(* A set whose points have small codes has a net of points of the set, one
   for each code. *)
Lemma grid_net n (S : set 'cV[R]_n) (h eps : R) (k : nat) :
  0 < h -> 0 <= eps -> n%:R * h ^+ 2 <= (eps / 2) ^+ 2 ->
  (forall x, S x -> \sum_i `|x i 0| < k.+1%:R * h) ->
  exists N : seq 'cV[R]_n, [/\ forall y, y \in N -> S y, is_net S N eps &
    (size N <= 'C(n + k, n) * 2 ^ n)%N].
Proof.
move=> h0 e0 hn Sk.
pose P c : set 'cV[R]_n :=
  [set y | S y /\ frobenius (y - grid_point h c) <= eps / 2].
exists [seq xget 0 (P c) | c <- grid_codes n k & `[< exists y, P c y >]]; split.
- move=> y /mapP[c]; rewrite mem_filter => /andP[/asboolP Pc _] ->.
  by have [] := xgetPex 0 Pc.
- move=> x Sx; set c := grid_code h x.
  have Px : P c x.
    split => //; rewrite -(@ler_pXn2r _ 2) ?nnegrE ?frobenius_ge0 ?divr_ge0 //.
    exact: le_trans (grid_code_dist _ h0) hn.
  have [Sy dy] := xgetPex 0 (ex_intro _ x Px).
  exists (xget 0 (P c)).
    apply: map_f; rewrite mem_filter grid_code_mem ?Sk // andbT.
    by apply/asboolP; exists x.
  have -> : x - xget 0 (P c) =
      (x - grid_point h c) + (grid_point h c - xget 0 (P c)).
    by rewrite addrA subrK.
  rewrite (le_trans (frobeniusD _ _)) // -[grid_point h c - _]opprB frobeniusN.
  by rewrite [leRHS](splitr eps); apply: lerD => //; case: Px.
- rewrite size_map size_filter (leq_trans (count_size _ _)) //.
  by rewrite size_grid_codes.
Qed.

(* Every set in the ball of radius r has an eps-net of at most
   (2 e (1 + 2 r / eps))^n of its own points. *)
Lemma net_exists n (S : set 'cV[R]_n) (r eps : R) : 0 <= r -> 0 < eps ->
  (forall x, S x -> frobenius x <= r) ->
  exists N : seq 'cV[R]_n, [/\ forall y, y \in N -> S y, is_net S N eps &
    (size N)%:R <= (2 * expR 1 * (1 + 2 * r / eps)) ^+ n].
Proof.
move=> r0 e0 Sr; case: n S Sr => [|n] S Sr.
  have h1 : 0%:R * 1 ^+ 2 <= (eps / 2) ^+ 2 :> R by rewrite mul0r sqr_ge0.
  have k1 (x : 'cV[R]_0) : S x -> \sum_(i < 0) `|x i 0| < 1%:R * 1.
    by rewrite big_ord0 mul1r ltr01.
  have [N [NS SN Nk]] := grid_net ltr01 (ltW e0) h1 k1.
  exists N; split => //.
  by rewrite expr0 -[1]/(1%:R) ler_nat (leq_trans Nk) // bin0.
set h := eps / (2 * Num.sqrt n.+1%:R).
have sn0 : 0 < Num.sqrt n.+1%:R :> R by rewrite sqrtr_gt0 ltr0n.
have h0 : 0 < h by rewrite divr_gt0 // mulr_gt0.
have n0 : 0 < n.+1%:R :> R by rewrite ltr0n.
have rr : 0 <= 2 * r / eps by rewrite divr_ge0 ?(ltW e0) // mulr_ge0 ?ler0n.
set k := Num.truncn (2 * n.+1%:R * r / eps).
have kE : k%:R <= 2 * n.+1%:R * r / eps.
  by rewrite truncn_le divr_ge0 ?(ltW e0) // mulr_ge0 // mulr_ge0 ?ler0n.
have hn : n.+1%:R * h ^+ 2 <= (eps / 2) ^+ 2.
  rewrite /h expr_div_n exprMn sqr_sqrtr ?ler0n // [leRHS]expr_div_n.
  by rewrite invfM mulrA mulrCA [n.+1%:R * _]mulrC mulfK ?pnatr_eq0 // mulrC.
have Sk x : S x -> \sum_i `|x i 0| < k.+1%:R * h.
  move=> Sx; apply: le_lt_trans (sum_abs_col_le x) _.
  apply: le_lt_trans (ler_wpM2l (ltW sn0) (Sr x Sx)) _.
  have -> : Num.sqrt n.+1%:R * r = 2 * n.+1%:R * r / eps * h.
    by rewrite /h -{2}(sqr_sqrtr (ler0n R n.+1)); field by rewrite gt_eqF.
  by rewrite ltr_pM2r // truncnS_gt.
have [N [NS SN Nk]] := grid_net h0 (ltW e0) hn Sk.
exists N; split => //.
apply: le_trans (_ : ('C(n.+1 + k, n.+1) * 2 ^ n.+1)%:R <= _).
  by rewrite ler_nat.
rewrite natrM natrX.
apply: le_trans (ler_wpM2r (exprn_ge0 _ (ler0n _ _)) (bin_le_expR _ _ _)) _.
rewrite -exprMn; apply: lerXn2r; rewrite ?nnegrE.
- by rewrite mulr_ge0 ?divr_ge0 ?mulr_ge0 ?expR_ge0 ?ler0n.
- by rewrite !mulr_ge0 ?expR_ge0 ?ler0n ?addr_ge0.
rewrite mulrC -!mulrA ler_wpM2l ?ler0n // ler_wpM2l ?expR_ge0 // mulrA.
rewrite natrD mulrDl divff ?gt_eqF // lerD2l ler_pdivrMr //.
by rewrite mulrAC [2 * r * _]mulrAC.
Qed.

Corollary unit_ball_net n (eps : R) : 0 < eps ->
  exists N : seq 'cV[R]_n, [/\ forall y, y \in N -> frobenius y <= 1,
    is_net (@unit_ball R n) N eps &
    (size N)%:R <= (2 * expR 1 * (1 + 2 / eps)) ^+ n].
Proof.
move=> e0; have [N [NS SN Nk]] :=
  @net_exists n (@unit_ball R n) 1 eps ler01 e0 (fun x => id).
by exists N; split => //; rewrite mulr1 in Nk.
Qed.

Corollary unit_sphere_net n (eps : R) : 0 < eps ->
  exists N : seq 'cV[R]_n, [/\ forall y, y \in N -> frobenius y = 1,
    is_net (@unit_sphere R n) N eps &
    (size N)%:R <= (2 * expR 1 * (1 + 2 / eps)) ^+ n].
Proof.
move=> e0; have [N [NS SN Nk]] :=
  @net_exists n (@unit_sphere R n) 1 eps ler01 e0 (@unit_sphere_ball R n).
by exists N; split => //; rewrite mulr1 in Nk.
Qed.

End net_existence.

Arguments grid_point {R n}.
