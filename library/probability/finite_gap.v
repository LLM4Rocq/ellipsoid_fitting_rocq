From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import sesquilinear boolp reals.
From mathcomp Require Import arithmetic_tactic ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean real_spectral.
From GaussianAnalysis.matrix Require Import spectral_gap.

(**md**************************************************************************)
(* # Spectral gaps on a finite space                                          *)
(*                                                                            *)
(* For a finite type X and weights w x > 0, wdot w f g = sum_x w x f x g x is *)
(* the inner product of L^2(w). The map f |-> (sqrt (w x) f x)_x (wvec, with  *)
(* inverse wfun) is an isometry of L^2(w) onto 'cV[R]_#|X| (mxdot_wvec), and  *)
(* an operator L on the functions on X has the matrix wop_mx w L in the basis *)
(* wbasis that wvec maps to the canonical basis (wop_mx_mul, wop_mx_form).    *)
(*                                                                            *)
(* Let L be linear, self-adjoint in L^2(w) and nonnegative:                   *)
(* <f, L g>_w = <L f, g>_w and <f, L f>_w >= 0. If                            *)
(* k <f, L f>_w <= <L f, L f>_w for every f, then                             *)
(*   k <f, f>_w <= <f, L f>_w                                                 *)
(* for every f orthogonal to the kernel of L (wgap_from_square): the matrix   *)
(* of L is symmetric and positive semidefinite, and psd_square_gap of         *)
(* matrix/spectral_gap.v applies to it. If moreover the weights sum to one    *)
(* and the kernel of L is the constants, this is the Poincare inequality      *)
(*   k Var_w(f) <= <f, L f>_w                                                 *)
(* (wpoincare_from_square): a bound of the Dirichlet form by the norm of the  *)
(* generator gives a spectral gap.                                            *)
(*                                                                            *)
(* Part of target T4 of phase 12: a Rocq formalization of the credited        *)
(* argument of the end of the proof of the proposition 'Gap and covariance    *)
(* under scaled interactions and fields' (rcut:prop:uniform-gap) of 'Cutoff   *)
(* throughout the high-temperature Sherrington-Kirkpatrick phase' (family 227 *)
(* of the OpenAI math collection, revision 1581d4cbd, file                    *)
(* appendices/entropy.tex). The manuscript reads ||A f||^2 >= kappa <f, A f>  *)
(* as a spectral gap of the self-adjoint nonnegative operator A, whose kernel *)
(* is the constants, by applying it to the eigenfunctions; here the spectral  *)
(* theorem enters through the matrix of the operator. It follows the TeX, not *)
(* a Lean module of the collection.                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*    wdot w f g == sum_x w x * f x * g x, the inner product of L^2(w)        *)
(*        wvec f == the column (sqrt (w x) * f x)_x, indexed by enum_val      *)
(*        wfun u == x |-> u_(enum_rank x) / sqrt (w x), the inverse of wvec   *)
(*      wbasis k == wfun of the k-th canonical column                         *)
(*    wop_mx w L == the matrix of L in the basis wbasis                       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section finite_gap.
Context {R : realType} {X : finType}.
Variable w : X -> R.

Local Notation N := #|X|.

(* The inner product of L^2(w): <f, g>_w = sum_x w x f x g x. *)
Definition wdot (f g : X -> R) : R := \sum_x w x * f x * g x.

Lemma wdotC f g : wdot f g = wdot g f.
Proof. by apply: eq_bigr => x _; rewrite mulrAC. Qed.

(* The map f |-> (sqrt (w x) f x)_x of L^2(w) onto 'cV[R]_N, and its
   inverse. *)
Definition wvec (f : X -> R) : 'cV[R]_N :=
  \col_k (Num.sqrt (w (enum_val k)) * f (enum_val k)).

Definition wfun (u : 'cV[R]_N) (x : X) : R :=
  u (enum_rank x) 0 / Num.sqrt (w x).

Hypothesis w0 : forall x, 0 < w x.

Lemma sqrt_w_gt0 x : 0 < Num.sqrt (w x).
Proof. by rewrite sqrtr_gt0 w0. Qed.

Lemma wvecK u : wvec (wfun u) = u.
Proof.
apply/matrixP => k l; rewrite (ord1 l) mxE /wfun enum_valK.
have s0 : Num.sqrt (w (enum_val k)) != 0 := lt0r_neq0 (sqrt_w_gt0 _).
by field.
Qed.

Lemma wfunK f : wfun (wvec f) = f.
Proof.
apply/funext => x; rewrite /wfun mxE enum_rankK.
have s0 : Num.sqrt (w x) != 0 := lt0r_neq0 (sqrt_w_gt0 _).
by field.
Qed.

Lemma sum_enum_val (F : X -> R) : \sum_(k < N) F (enum_val k) = \sum_x F x.
Proof.
rewrite [RHS](reindex (enum_val : 'I_N -> X)) //.
by exists enum_rank => [k _|x _]; [exact: enum_valK | exact: enum_rankK].
Qed.

Lemma mxdot_wvec f g : mxdot (wvec f) (wvec g) = wdot f g.
Proof.
rewrite /mxdot /wdot -sum_enum_val; apply: eq_bigr => k _.
rewrite big_ord1 !mxE mulrACA -expr2 sqr_sqrtr ?mulrA //.
exact: ltW (w0 _).
Qed.

Lemma wvec_eq0 f : wvec f = 0 -> forall x, f x = 0.
Proof.
move=> f0 x; have := congr1 (fun u : 'cV[R]_N => u (enum_rank x) 0) f0.
rewrite !mxE enum_rankK => /eqP; rewrite mulf_eq0 (gt_eqF (sqrt_w_gt0 x)) /=.
by move/eqP.
Qed.

(* The basis of L^2(w) that wvec maps to the canonical basis, and the
   inner products with it. *)
Definition wbasis (k : 'I_N) : X -> R := wfun (delta_mx k 0).

Lemma wfun_sum u : wfun u = fun x => \sum_k u k 0 * wbasis k x.
Proof.
apply/funext => x; rewrite /wbasis /wfun.
rewrite (bigD1 (enum_rank x)) //= big1 ?addr0.
  by move=> k kx; rewrite mxE eq_sym (negbTE kx) /= mul0r mulr0.
by rewrite mxE !eqxx mulrA mulr1.
Qed.

Lemma wdot_basis k g :
  wdot (wbasis k) g = Num.sqrt (w (enum_val k)) * g (enum_val k).
Proof.
rewrite /wdot (bigD1 (enum_val k)) //= big1 ?addr0.
  move=> x xk; rewrite /wbasis /wfun mxE.
  have -> : (enum_rank x == k) = false.
    by apply/negbTE; apply: contra xk => /eqP <-; rewrite enum_rankK.
  by rewrite /= mul0r mulr0 mul0r.
rewrite /wbasis /wfun enum_valK mxE !eqxx mul1r.
have s0 : Num.sqrt (w (enum_val k)) != 0 := lt0r_neq0 (sqrt_w_gt0 _).
have w0k : 0 <= w (enum_val k) := ltW (w0 _).
rewrite -[X in X * _ * _](sqr_sqrtr w0k) expr2.
by field.
Qed.

(* A linear operator L on functions, self-adjoint and nonnegative in
   L^2(w). *)
Variable L : (X -> R) -> X -> R.
Hypothesis L_lin : forall (a : R) (f g : X -> R) x,
  L (fun y => a * f y + g y) x = a * L f x + L g x.
Hypothesis L_sym : forall f g, wdot f (L g) = wdot (L f) g.
Hypothesis L_ge0 : forall f, 0 <= wdot f (L f).

Lemma L_cst0 x : L (fun _ => 0) x = 0.
Proof.
have := L_lin 1 (fun _ => 0) (fun _ => 0) x => /=.
have -> : (fun _ : X => 1 * 0 + 0) = (fun _ => 0 : R).
  by apply/funext => y; rewrite mul1r addr0.
rewrite mul1r; move: (L _ x) => a h.
by apply: (@addrI _ a); rewrite addr0 -h.
Qed.

Lemma L_sum (I : finType) (c : I -> R) (h : I -> X -> R) x :
  L (fun y => \sum_i c i * h i y) x = \sum_i c i * L (h i) x.
Proof.
suff hs (s : seq I) :
    L (fun y => \sum_(i <- s) c i * h i y) x = \sum_(i <- s) c i * L (h i) x.
  exact: hs.
elim: s => [|j s IH].
  have -> : (fun y => \sum_(i <- [::]) c i * h i y) = (fun _ => 0 : R).
    by apply/funext => y; rewrite big_nil.
  by rewrite big_nil L_cst0.
have -> : (fun y => \sum_(i <- j :: s) c i * h i y) =
    (fun y => c j * h j y + \sum_(i <- s) c i * h i y).
  by apply/funext => y; rewrite big_cons.
by rewrite L_lin IH big_cons.
Qed.

(* The matrix of L in the basis wbasis. *)
Definition wop_mx : 'M[R]_N := \matrix_(k, l) wdot (wbasis k) (L (wbasis l)).

Lemma wop_mx_mul u : wop_mx *m u = wvec (L (wfun u)).
Proof.
apply/matrixP => k j; rewrite (ord1 j) !mxE wfun_sum L_sum mulr_sumr.
apply: eq_bigr => l _; rewrite mxE wdot_basis.
by rewrite mulrCA mulrC.
Qed.

Lemma wop_mx_sym : wop_mx \is symmetricmx.
Proof.
apply/symmetricmxP/matrixP => k l; rewrite !mxE.
by rewrite L_sym wdotC.
Qed.

Lemma wop_mx_form u : mxdot u (wop_mx *m u) = wdot (wfun u) (L (wfun u)).
Proof.
by rewrite wop_mx_mul -{1}(wvecK u) mxdot_wvec.
Qed.

(* The gap from a bound of the form by the squared norm, for the functions
   orthogonal to the kernel. *)
Theorem wgap_from_square (k : R) :
  (forall f, k * wdot f (L f) <= wdot (L f) (L f)) ->
  forall f, (forall g, (forall x, L g x = 0) -> wdot g f = 0) ->
  k * wdot f f <= wdot f (L f).
Proof.
move=> hsq f hf.
have e1 : wdot f f = mxdot (wvec f) (wvec f) by rewrite mxdot_wvec.
have e2 : wdot f (L f) = mxdot (wvec f) (wop_mx *m wvec f).
  by rewrite wop_mx_form wfunK.
rewrite e1 e2; apply: psd_square_gap.
- exact: wop_mx_sym.
- by move=> y; rewrite wop_mx_form.
- by move=> y; rewrite wop_mx_form wop_mx_mul mxdot_wvec; exact: hsq.
- move=> y By0.
  have hL : forall x, L (wfun y) x = 0.
    by apply: wvec_eq0; rewrite -wop_mx_mul.
  by rewrite -{1}(wvecK y) mxdot_wvec hf.
Qed.

(* The Poincare inequality, when the weights sum to one and the kernel of L
   is the constants. *)
Theorem wpoincare_from_square (k : R) : \sum_x w x = 1 ->
  (forall g, (forall x, L g x = 0) <-> (forall x y, g x = g y)) ->
  (forall f, k * wdot f (L f) <= wdot (L f) (L f)) ->
  forall f, k * \sum_x w x * (f x - \sum_y w y * f y) ^+ 2 <= wdot f (L f).
Proof.
move=> w1 hker hsq f.
pose c := \sum_y w y * f y.
pose f0 := fun x => f x - c.
have Lcst (a : R) x : L (fun _ => a) x = 0.
  by apply/(proj2 (hker (fun _ => a))).
have Lf0 x : L f0 x = L f x.
  have := L_lin 1 f (fun _ => - c) x => /=.
  have -> : (fun y => 1 * f y - c) = f0 by apply/funext => y; rewrite mul1r.
  by rewrite mul1r Lcst addr0.
have hL1 : \sum_x w x * L f x = 0.
  transitivity (wdot (fun _ => 1) (L f)).
    by apply: eq_bigr => x _; rewrite mulr1.
  rewrite L_sym; apply: big1 => x _.
  by rewrite Lcst mulr0 mul0r.
have E1 : wdot f0 (L f0) = wdot f (L f).
  transitivity (\sum_x (w x * f x * L f x - c * (w x * L f x))).
    by apply: eq_bigr => x _; rewrite Lf0 /f0 /=; ring.
  by rewrite sumrB -mulr_sumr hL1 mulr0 subr0.
have orth g : (forall x, L g x = 0) -> wdot g f0 = 0.
  move=> /hker hg.
  case: (pickP (@predT X)) => [x0 _|X0].
    transitivity (g x0 * (\sum_x w x * f x - c * \sum_x w x)).
      rewrite /wdot mulr_sumr -sumrB mulr_sumr; apply: eq_bigr => x _.
      by rewrite (hg x x0) /f0 /=; ring.
    by rewrite w1 mulr1 /c subrr mulr0.
  by rewrite /wdot big1 // => x; move: (X0 x).
have Ef0 : wdot f0 f0 = \sum_x w x * (f x - c) ^+ 2.
  by apply: eq_bigr => x _; rewrite /f0 /= expr2 mulrA.
rewrite -/c -Ef0 -E1.
exact: (wgap_from_square hsq orth).
Qed.

End finite_gap.
