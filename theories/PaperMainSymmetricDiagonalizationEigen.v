(* A real eigenvector of a real symmetric matrix, from the Rayleigh maximum.
   For A : 'M[R]_(n.+1) symmetric, the quadratic form w |-> w A w^T is
   continuous on the Euclidean unit sphere of 'rV[R]_(n.+1), which is
   closed and contained in the box [-1, 1]^(n.+1), hence compact
   (rV_compact, compact_closedI). So it attains its maximum l at some w
   (compact_EVT_min applied to the opposite form). By homogeneity,
   x^T A x <= l |x|^2 for every column x, so l I - A is positive
   semidefinite, and v = w^T has v^T (l I - A) v = 0. The discriminant
   lemma paper_main_psd_form_eq0 then gives (l I - A) v = 0, that is
   A v = l v with |v| = 1. No spectral theorem, complex number or
   eigenvalue existence is assumed. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryCompact.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* Squared Euclidean norms of rows and columns. *)

Definition paper_main_symmetric_row_sq {N : nat} (w : 'rV[R]_N) : R :=
  \sum_(k < N) w 0 k ^+ 2.

Definition paper_main_symmetric_sq {N : nat} (v : 'cV[R]_N) : R :=
  \sum_(k < N) v k 0 ^+ 2.

Definition paper_main_symmetric_sphere (N : nat) : set 'rV[R]_N :=
  [set w | paper_main_symmetric_row_sq w = 1].

Lemma paper_main_symmetric_sq_tr N (w : 'rV[R]_N) :
  paper_main_symmetric_sq w^T = paper_main_symmetric_row_sq w.
Proof. by apply: eq_bigr => k _; rewrite mxE. Qed.

Lemma paper_main_symmetric_sq_ge0 N (v : 'cV[R]_N) : 0 <= paper_main_symmetric_sq v.
Proof. by apply: sumr_ge0 => k _; exact: sqr_ge0. Qed.

Lemma paper_main_symmetric_sq_dot N (v : 'cV[R]_N) :
  (v^T *m v) 0 0 = paper_main_symmetric_sq v.
Proof. by rewrite mxE; apply: eq_bigr => k _; rewrite mxE expr2. Qed.

Lemma paper_main_symmetric_sq_scale N (c : R) (v : 'cV[R]_N) :
  paper_main_symmetric_sq (c *: v) = c ^+ 2 * paper_main_symmetric_sq v.
Proof.
rewrite /paper_main_symmetric_sq mulr_sumr; apply: eq_bigr => k _.
by rewrite mxE exprMn.
Qed.

Lemma paper_main_symmetric_sq_eq0 N (v : 'cV[R]_N) :
  paper_main_symmetric_sq v = 0 -> v = 0.
Proof.
move=> H0; apply/matrixP => k j; rewrite [j]ord1 mxE.
have Hk : v k 0 ^+ 2 <= 0.
  rewrite -H0 /paper_main_symmetric_sq (bigD1 k) //= lerDl.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have Hk0 : v k 0 ^+ 2 = 0 by apply/eqP; rewrite eq_le Hk sqr_ge0.
by move: Hk0 => /eqP; rewrite sqrf_eq0 => /eqP.
Qed.

(* Continuity and compactness. *)

Lemma paper_main_symmetric_row_sq_continuous N :
  continuous (@paper_main_symmetric_row_sq N).
Proof.
rewrite /paper_main_symmetric_row_sq.
apply: (pmg_continuous_sum N 'I_N (fun k (w : 'rV[R]_N) => w 0 k ^+ 2)) => k.
have -> : (fun w : 'rV[R]_N => w 0 k ^+ 2) = (fun w => w 0 k * w 0 k).
  by apply: funext => w; rewrite expr2.
by apply: pmg_continuousM; exact: pmg_continuous_coord.
Qed.

Lemma paper_main_symmetric_form_continuous N (A : 'M[R]_N) :
  continuous (fun w : 'rV[R]_N => paper_main_quadratic_form A w^T).
Proof.
have -> : (fun w : 'rV[R]_N => paper_main_quadratic_form A w^T) =
    (fun w => \sum_(i < N) \sum_(j < N) w 0 i * A i j * w 0 j).
  apply: funext => w; apply: eq_bigr => i _; apply: eq_bigr => j _.
  by rewrite !mxE.
apply: (pmg_continuous_sum N 'I_N) => i.
apply: (pmg_continuous_sum N 'I_N) => j.
apply: pmg_continuousM; last exact: pmg_continuous_coord.
apply: pmg_continuousM; first exact: pmg_continuous_coord.
exact: pmg_continuous_cst.
Qed.

Lemma paper_main_symmetric_sphere_closed N : closed (paper_main_symmetric_sphere N).
Proof.
exact: (pmg_closed_eq N _ 1 (paper_main_symmetric_row_sq_continuous N)).
Qed.

Lemma paper_main_symmetric_sphere_box N :
  paper_main_symmetric_sphere N `<=` pmg_box N.
Proof.
move=> w Hw k.
have Hk : w 0 k ^+ 2 <= 1.
  rewrite -Hw /paper_main_symmetric_row_sq (bigD1 k) //= lerDl.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
have Hn : `|w 0 k| <= 1.
  by rewrite -[1]sqrtr1 -sqrtr_sqr; apply: ler_wsqrtr.
by rewrite /= in_itv /= -ler_norml.
Qed.

Theorem paper_main_symmetric_sphere_compact N : compact (paper_main_symmetric_sphere N).
Proof.
have -> : paper_main_symmetric_sphere N = pmg_box N `&` paper_main_symmetric_sphere N.
  rewrite predeqE => w; split=> [Hw | [_ Hw]] //; split=> //.
  exact: paper_main_symmetric_sphere_box.
by apply: compact_closedI; [exact: pmg_box_compact | exact: paper_main_symmetric_sphere_closed].
Qed.

Lemma paper_main_symmetric_sphere_neq0 n : paper_main_symmetric_sphere n.+1 !=set0.
Proof.
exists (delta_mx 0 0); rewrite /paper_main_symmetric_sphere /paper_main_symmetric_row_sq /=.
rewrite (bigD1 ord0) //= big1.
- by move=> k Hk; rewrite mxE eqxx /= (negbTE Hk) /= expr0n.
- by rewrite !mxE eqxx /= expr1n addr0.
Qed.

(* The Rayleigh maximum. *)

Theorem paper_main_symmetric_rayleigh_max n (A : 'M[R]_n.+1) :
  exists2 w, paper_main_symmetric_sphere n.+1 w &
    forall w', paper_main_symmetric_sphere n.+1 w' ->
      paper_main_quadratic_form A w'^T <= paper_main_quadratic_form A w^T.
Proof.
have Hf : continuous (fun w : 'rV[R]_n.+1 => - paper_main_quadratic_form A w^T).
  have -> : (fun w : 'rV[R]_n.+1 => - paper_main_quadratic_form A w^T) =
      (fun w => 0 - paper_main_quadratic_form A w^T).
    by apply: funext => w; rewrite sub0r.
  apply: pmg_continuousB; first exact: pmg_continuous_cst.
  exact: paper_main_symmetric_form_continuous.
have Hw : {within paper_main_symmetric_sphere n.+1,
    continuous (fun w : 'rV[R]_n.+1 => - paper_main_quadratic_form A w^T)}.
  by apply: continuous_subspaceT.
have [w0 Hw0 Hmin] := compact_EVT_min (paper_main_symmetric_sphere_neq0 n)
  (paper_main_symmetric_sphere_compact n.+1) Hw.
exists w0; first by rewrite -in_setE.
by move=> w Hw'; rewrite -lerN2; apply: Hmin; rewrite in_setE.
Qed.

(* Homogeneity of the form. *)

Lemma paper_main_symmetric_form_scale N (A : 'M[R]_N) (c : R) (v : 'cV[R]_N) :
  paper_main_quadratic_form A (c *: v) = c ^+ 2 * paper_main_quadratic_form A v.
Proof.
rewrite /paper_main_quadratic_form mulr_sumr; apply: eq_bigr => i _.
rewrite mulr_sumr; apply: eq_bigr => j _.
rewrite !mxE expr2 -!mulrA; congr (_ * _).
rewrite [A i j * (c * _)]mulrCA.
exact: mulrCA.
Qed.

Lemma paper_main_symmetric_form0 N (A : 'M[R]_N) :
  paper_main_quadratic_form A 0 = 0.
Proof.
rewrite /paper_main_quadratic_form; apply: big1 => i _; apply: big1 => j _.
by rewrite !mxE !mul0r.
Qed.

Theorem paper_main_symmetric_rayleigh_bound n (A : 'M[R]_n.+1) (w : 'rV[R]_n.+1) :
  paper_main_symmetric_sphere n.+1 w ->
  (forall w', paper_main_symmetric_sphere n.+1 w' ->
    paper_main_quadratic_form A w'^T <= paper_main_quadratic_form A w^T) ->
  forall x : 'cV[R]_n.+1,
    paper_main_quadratic_form A x <=
      paper_main_quadratic_form A w^T * paper_main_symmetric_sq x.
Proof.
move=> Hw Hmax x.
have [Hx0 | Hx0] := eqVneq (paper_main_symmetric_sq x) 0.
  by rewrite Hx0 mulr0 (paper_main_symmetric_sq_eq0 _ _ Hx0) paper_main_symmetric_form0.
have Hpos : 0 < paper_main_symmetric_sq x by rewrite lt0r Hx0 paper_main_symmetric_sq_ge0.
set c := Num.sqrt (paper_main_symmetric_sq x).
have Hc : 0 < c by rewrite sqrtr_gt0.
have Hc2 : c ^+ 2 = paper_main_symmetric_sq x by rewrite sqr_sqrtr // ltW.
have Hc0 : c != 0 by rewrite gt_eqF.
have Hsph : paper_main_symmetric_sphere n.+1 (c^-1 *: x)^T.
  rewrite /paper_main_symmetric_sphere /= -paper_main_symmetric_sq_tr trmxK.
  by rewrite paper_main_symmetric_sq_scale -Hc2 exprVn mulVf // expf_neq0.
have H := Hmax _ Hsph.
rewrite trmxK paper_main_symmetric_form_scale exprVn mulrC in H.
have Hc2p : 0 < c ^+ 2 by rewrite exprn_gt0.
by rewrite -Hc2 -(ler_pdivrMr _ _ Hc2p).
Qed.

(* The eigenvector. *)

Theorem paper_main_symmetric_eigenvector n (A : 'M[R]_n.+1) :
  paper_main_symmetric A ->
  exists v : 'cV[R]_n.+1,
    paper_main_symmetric_sq v = 1 /\
    A *m v = paper_main_quadratic_form A v *: v /\
    forall x : 'cV[R]_n.+1,
      paper_main_quadratic_form A x <=
        paper_main_quadratic_form A v * paper_main_symmetric_sq x.
Proof.
move=> HA.
have [w Hw Hmax] := paper_main_symmetric_rayleigh_max _ A.
have Hb := paper_main_symmetric_rayleigh_bound _ A w Hw Hmax.
set l := paper_main_quadratic_form A w^T in Hb.
have Hv1 : paper_main_symmetric_sq w^T = 1 by rewrite paper_main_symmetric_sq_tr.
have Hs : paper_main_symmetric (l%:M - A).
  move=> i j; rewrite !mxE (HA i j) eq_sym.
  by [].
have Hform x : paper_main_quadratic_form (l%:M - A) x =
    l * paper_main_symmetric_sq x - paper_main_quadratic_form A x.
  rewrite !paper_main_quadratic_formE mulmxBr mulmxBl mxE.
  rewrite mul_mx_scalar -scalemxAl [in X in X + _]mxE paper_main_symmetric_sq_dot.
  by rewrite [in X in _ + X]mxE.
have Hpsd : paper_main_psd (l%:M - A).
  split; first exact: Hs.
  by move=> x; rewrite Hform subr_ge0; exact: Hb.
have H0 : paper_main_quadratic_form (l%:M - A) w^T = 0.
  by rewrite Hform Hv1 mulr1 subrr.
have Hker := paper_main_psd_form_eq0 _ _ _ Hpsd H0.
exists w^T; split; first exact: Hv1.
split; last exact: Hb.
move: Hker; rewrite mulmxBl mul_scalar_mx => /eqP; rewrite subr_eq0 => /eqP <-.
by [].
Qed.
