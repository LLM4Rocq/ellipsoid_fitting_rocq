(* The orthogonal complement of a fixed head range. For any m-by-q matrix
   F (the head columns, fixed: the head data is conditioned on), there is
   an s-by-m matrix V with orthonormal rows, V V^T = I, s >= m - q and
   V F = 0 (paper_main_projected_complement_mx). Construction: diagonalize
   G = F F^T = O^T diag(a) O (PaperMainSymmetricDiagonalization) and keep the
   rows of O with a_i = 0. Each kept row u has u^T G u = |F^T u|^2 = 0, so
   u F = 0. A row with a_i <> 0 equals a_i^-1 (O F)_i F^T, so the rows with
   nonzero eigenvalue lie in the row space of F^T; being orthonormal, they
   number at most rank F <= q.
   The basis is chosen for the fixed F only (an existential); no measurable
   dependence on the head is claimed. In nat-indexed form the rows give a
   loading with paper_main_projected_orthonormal, they annihilate every
   head combination F v, and Bessel's inequality |U w| <= |w| holds. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix mxalgebra finset.
From mathcomp Require Import boolp classical_sets functions reals Rstruct cardinality.
From mathcomp Require Import topology normedtype Rstruct_topology sequences.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums GaussianCovarianceDefinitions
  GaussianProbabilityProductDefinitions GaussianProbabilityProductContinuity
  PaperMainDefinitions PaperMainMatrixDuality PaperMainGordonSetWidth PaperMainProjectedBulkEscape
  PaperMainGordonProcessCovariance PaperMainGaussianFeatureCoordinates
  PaperMainSymmetricDiagonalization PaperMainGordonEscape PaperMainProjectedBulkLaw.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* Orthonormal rows have full row rank. *)

Lemma paper_main_projected_rows_rank {k m : nat} (W : 'M[R]_(k, m)) :
  W *m W^T = 1%:M -> \rank W = k.
Proof.
move=> HW; apply/eqP; rewrite eqn_leq rank_leq_row /=.
by rewrite -{1}(mxrank1 R k) -HW mxrankM_maxl.
Qed.

(* The rows of an orthogonal matrix indexed by a set. *)

Definition paper_main_projected_select {m : nat} (O : 'M[R]_m) (Z : {set 'I_m}) :
    'M[R]_(#|Z|, m) :=
  \matrix_(k, j) O (enum_val k) j.

Lemma paper_main_projected_select_orthonormal {m : nat} (O : 'M[R]_m) (Z : {set 'I_m}) :
  O *m O^T = 1%:M ->
  paper_main_projected_select O Z *m (paper_main_projected_select O Z)^T = 1%:M.
Proof.
move=> HO; apply/matrixP => k k'.
transitivity ((O *m O^T) (enum_val k) (enum_val k')).
  rewrite !mxE; apply: eq_bigr => j _; rewrite !mxE.
  by [].
rewrite HO !mxE; congr (_%:R).
by rewrite (inj_eq enum_val_inj).
Qed.

Lemma paper_main_projected_gram_symmetric {m q : nat} (F : 'M[R]_(m, q)) :
  paper_main_symmetric (F *m F^T).
Proof.
by move=> i j; rewrite !mxE; apply: eq_bigr => k _; rewrite !mxE mulrC.
Qed.

(* The complement of the head range. *)

Theorem paper_main_projected_complement_mx (m q : nat) (F : 'M[R]_(m, q)) :
  exists (s : nat) (V : 'M[R]_(s, m)),
    (m - q <= s)%N /\ V *m V^T = 1%:M /\ V *m F = 0.
Proof.
set G := F *m F^T.
have [O [a [HO HGd]]] := paper_main_symmetric_diagonalization m G
  (paper_main_projected_gram_symmetric F).
have HO' : O *m O^T = 1%:M := mulmx1C HO.
have HOG : O *m G = diag_mx a *m O.
  by rewrite HGd !mulmxA HO' mul1mx.
have HOGO : (O *m F) *m (O *m F)^T = diag_mx a.
  by rewrite trmx_mul mulmxA -(mulmxA O F) -/G HOG -mulmxA HO' mulmx1.
set Z := [set i : 'I_m | a 0 i == 0]%SET.
(* Rows with zero eigenvalue annihilate F. *)
have HVF : paper_main_projected_select O Z *m F = 0.
  apply/matrixP => k c; rewrite !mxE.
  set i := enum_val k.
  have Hi : a 0 i = 0 by have := enum_valP k; rewrite inE => /eqP.
  have Hsum : \sum_(c' < q) (O *m F) i c' * (O *m F) i c' = 0.
    have Hii : ((O *m F) *m (O *m F)^T) i i = 0 by rewrite HOGO mxE eqxx mulr1n Hi.
    rewrite mxE in Hii; rewrite -[RHS]Hii.
    apply: eq_bigr => c' _; rewrite !mxE; by [].
  have H0 : forall c', (O *m F) i c' = 0.
    move=> c'.
    have Hnn : forall c'', true -> 0 <= (O *m F) i c'' * (O *m F) i c''.
      by move=> c'' _; rewrite -expr2 sqr_ge0.
    have := psumr_eq0P Hnn Hsum; move=> /(_ c' isT).
    by move/eqP; rewrite mulf_eq0 orbb => /eqP.
  transitivity ((O *m F) i c); last exact: H0.
  rewrite mxE; apply: eq_bigr => j _; rewrite mxE.
  by [].
(* At most q rows have a nonzero eigenvalue. *)
have Hcount : (m - q <= #|Z|)%N.
  set NZ := ~: Z.
  set W := paper_main_projected_select O NZ.
  have HW : W *m W^T = 1%:M := paper_main_projected_select_orthonormal O NZ HO'.
  have Hr := paper_main_projected_rows_rank W HW.
  pose X : 'M[R]_(#|NZ|, q) :=
    \matrix_(k, c) ((a 0 (enum_val k))^-1 * (O *m F) (enum_val k) c).
  have HWX : W = X *m F^T.
    apply/matrixP => k j.
    set i := enum_val k.
    have Hi : a 0 i != 0.
      by have := enum_valP k; rewrite /NZ inE /Z inE.
    transitivity ((a 0 i)^-1 * ((O *m G) i j)).
      have Hdiag : (O *m G) i j = a 0 i * O i j.
        rewrite HOG mxE (bigD1 i) //= big1 ?addr0; last first.
          by rewrite mxE eqxx mulr1n.
        by move=> l Hl; rewrite mxE eq_sym (negbTE Hl) mulr0n mul0r.
      rewrite Hdiag mulrA mulVf // mul1r /W /paper_main_projected_select mxE.
      by [].
    rewrite /G mulmxA [in LHS]mxE mulr_sumr [in RHS]mxE.
    apply: eq_bigr => c _; rewrite [in RHS]mxE [in RHS]mxE mulrA.
    by rewrite [(O *m F) i c]mxE.
  have Hle : (#|NZ| <= q)%N.
    rewrite -Hr HWX.
    apply: (leq_trans (mxrankM_maxr _ _)).
    by rewrite mxrank_tr; exact: rank_leq_col.
  have Hc := cardsC Z; rewrite card_ord in Hc.
  rewrite leq_subLR.
  have Hc' : (m <= #|Z| + #|NZ|)%N by rewrite /NZ Hc.
  apply: (leq_trans Hc').
  by rewrite addnC leq_add2r.
exists #|Z|, (paper_main_projected_select O Z); split => //; split => //.
exact: paper_main_projected_select_orthonormal.
Qed.

(* Bessel's inequality and the annihilation of the head: for V V^T = I and
   V F = 0, |V w|^2 <= |w + F v|^2 for every w and v. *)

Definition paper_main_projected_sqnorm {m : nat} (w : 'cV[R]_m) : R := (w^T *m w) 0 0.

Lemma paper_main_projected_sqnorm_ge0 {m : nat} (w : 'cV[R]_m) :
  0 <= paper_main_projected_sqnorm w.
Proof.
rewrite /paper_main_projected_sqnorm mxE; apply: sumr_ge0 => i _.
by rewrite mxE -expr2 sqr_ge0.
Qed.

Theorem paper_main_projected_bessel {s m q : nat} (V : 'M[R]_(s, m)) (F : 'M[R]_(m, q))
    (w : 'cV[R]_m) (v : 'cV[R]_q) :
  V *m V^T = 1%:M -> V *m F = 0 ->
  paper_main_projected_sqnorm (V *m w) <= paper_main_projected_sqnorm (w + F *m v).
Proof.
move=> HVV HVF.
set u := w + F *m v.
have HVu : V *m u = V *m w by rewrite /u mulmxDr mulmxA HVF mul0mx addr0.
rewrite -HVu.
have H := paper_main_projected_sqnorm_ge0 (u - V^T *m (V *m u)).
set p := V^T *m (V *m u) in H *.
have Htr : p^T = (V *m u)^T *m V by rewrite /p trmx_mul trmxK.
have Htr2 : (V *m u)^T = u^T *m V^T by rewrite trmx_mul.
have E1 : u^T *m p = (V *m u)^T *m (V *m u) by rewrite /p Htr2 mulmxA.
have E2 : p^T *m u = (V *m u)^T *m (V *m u) by rewrite Htr -mulmxA.
have E3 : p^T *m p = (V *m u)^T *m (V *m u).
  by rewrite Htr /p -mulmxA (mulmxA V V^T) HVV mul1mx.
move: H; rewrite /paper_main_projected_sqnorm paper_main_symmetric_dotBl.
rewrite !paper_main_symmetric_dotBr E1 E2 E3.
move=> H; rewrite -subr_ge0.
by rewrite opprB addrA subrK in H.
Qed.

(* A deletion set J is absorbed into the row isometry: the selector S_J has
   orthonormal rows and V S_J has orthonormal rows when V has. *)

Definition paper_main_projected_selector {n : nat} (J : {set 'I_n}) : 'M[R]_(#|J|, n) :=
  \matrix_(k, i) ((enum_val k == i)%:R).

Lemma paper_main_projected_selector_orthonormal {n : nat} (J : {set 'I_n}) :
  paper_main_projected_selector J *m (paper_main_projected_selector J)^T = 1%:M.
Proof.
apply/matrixP => k k'; rewrite !mxE.
rewrite (bigD1 (enum_val k)) //= big1 ?addr0.
  by move=> i Hi; rewrite /paper_main_projected_selector !mxE eq_sym (negbTE Hi) mul0r.
rewrite /paper_main_projected_selector !mxE eqxx mul1r.
by rewrite (inj_eq enum_val_inj) eq_sym.
Qed.

Lemma paper_main_projected_compose_orthonormal {s n : nat} (J : {set 'I_n})
    (V : 'M[R]_(s, #|J|)) :
  V *m V^T = 1%:M ->
  (V *m paper_main_projected_selector J) *m (V *m paper_main_projected_selector J)^T = 1%:M.
Proof.
move=> HV.
by rewrite trmx_mul mulmxA -(mulmxA V) paper_main_projected_selector_orthonormal mulmx1.
Qed.

(* The nat-indexed loading of a rectangular matrix. *)

Definition paper_main_projected_mx_loading {s m : nat} (V : 'M[R]_(s, m)) (a k : nat) : R :=
  oapp (fun a' : 'I_s => oapp (fun k' : 'I_m => V a' k') 0 (insub k)) 0 (insub a).

Lemma paper_main_projected_mx_loading_val {s m : nat} (V : 'M[R]_(s, m)) (a : 'I_s) (k : 'I_m) :
  paper_main_projected_mx_loading V a k = V a k.
Proof. by rewrite /paper_main_projected_mx_loading !valK. Qed.

Lemma paper_main_projected_mx_loading_orthonormal {s m : nat} (V : 'M[R]_(s, m)) :
  V *m V^T = 1%:M -> paper_main_projected_orthonormal s m (paper_main_projected_mx_loading V).
Proof.
move=> HV a a' Ha Ha'.
have Ha2 : (a < s)%N by apply/ssrnat.ltP.
have Ha2' : (a' < s)%N by apply/ssrnat.ltP.
transitivity ((V *m V^T) (Ordinal Ha2) (Ordinal Ha2')).
  rewrite /gaussian_covariance_entry paper_main_finite_sum_public mxE.
  apply: eq_bigr => k _.
  rewrite (paper_main_projected_mx_loading_val V (Ordinal Ha2) k).
  rewrite (paper_main_projected_mx_loading_val V (Ordinal Ha2') k).
  by rewrite mxE.
rewrite HV mxE /=.
case: (Nat.eqb_spec a a') => [Hab|Hab].
  have -> : Ordinal Ha2 = Ordinal Ha2' by apply: val_inj.
  by rewrite eqxx mulr1n.
have Hne : (Ordinal Ha2 == Ordinal Ha2') = false.
  by apply/negbTE/eqP => Heq; apply: Hab; have := congr1 val Heq.
by rewrite Hne mulr0n.
Qed.

(* The escape statistic of the projected array is a matrix norm: with
   r_i(v) = sum_j v_j x_(i D + j) (row i of the bulk array applied to v),
   the escape image of the projected array at v is W r(v). *)

Definition paper_main_projected_bulk_vector (n D : nat) (x : (n * D).-tuple (measurableTypeR R))
    (v : nat -> R) : 'cV[R]_n :=
  \col_(i < n) finite_sum (fun j => v j * List.nth (i * D + j) (tval x) 0) (List.seq 0 D).

Lemma paper_main_projected_escape_image_mx {s n D : nat} (W : 'M[R]_(s, n))
    (x : (n * D).-tuple (measurableTypeR R)) (v : nat -> R) (a : 'I_s) :
  paper_main_gordon_escape_image s D v
    (tval (paper_main_projected_map s n D (paper_main_projected_mx_loading W) x)) a =
  (W *m paper_main_projected_bulk_vector n D x v) a 0.
Proof.
rewrite /paper_main_gordon_escape_image paper_main_projected_map_val /paper_main_projected_image.
set U := paper_main_projected_mx_loading W.
transitivity (finite_sum (fun j => v j * finite_sum (fun i =>
    U a i * List.nth (i * D + j) (tval x) 0) (List.seq 0 n)) (List.seq 0 D)).
  apply: finite_sum_ext => j Hj.
  have HjD : (j < D)%coq_nat by have := in_seq_lt _ _ Hj; lia.
  have Ha : (a < s)%coq_nat by apply/ssrnat.ltP; exact: ltn_ord.
  have HaD : (a * D + j < s * D)%coq_nat.
    have Hj' : (j < D)%N by apply/ssrnat.ltP.
    apply/ssrnat.ltP.
    apply: (@leq_trans (a.+1 * D)); first by rewrite mulSnr ltn_add2l.
    by rewrite leq_mul2r ltn_ord orbT.
  congr (_ * _).
  rewrite /gaussian_covariance_image (nth_map_seq _ (s * D) (a * D + j) HaD).
  exact: paper_main_projected_row.
rewrite paper_main_finite_sum_public mxE.
transitivity (\sum_(j < D) \sum_(i < n) (v j * (U a i * List.nth (i * D + j) (tval x) 0))).
  apply: eq_bigr => j _.
  rewrite paper_main_finite_sum_public big_distrr /=.
  by apply: eq_bigr => i _.
rewrite exchange_big /=; apply: eq_bigr => i _.
have HU : U a i = W a i by rewrite /U (paper_main_projected_mx_loading_val W a i).
rewrite mxE paper_main_finite_sum_public big_distrr /=.
apply: eq_bigr => j _.
by rewrite HU mulrCA.
Qed.

Lemma paper_main_projected_escape_norm_mx {s n D : nat} (W : 'M[R]_(s, n))
    (x : (n * D).-tuple (measurableTypeR R)) (v : nat -> R) :
  paper_main_gordon_escape_norm s D v
    (tval (paper_main_projected_map s n D (paper_main_projected_mx_loading W) x)) =
  sqrt (paper_main_projected_sqnorm (W *m paper_main_projected_bulk_vector n D x v)).
Proof.
rewrite /paper_main_gordon_escape_norm /euclidean_norm /squared_norm; congr sqrt.
rewrite /paper_main_projected_sqnorm mxE paper_main_finite_sum_public.
apply: eq_bigr => a _.
rewrite paper_main_projected_escape_image_mx [_^T _ _]mxE.
by rewrite RpowE expr2.
Qed.

(* The section argument for fixed head data. For a deletion set J and the
   head columns F of the rows in J (fixed), there is a row isometry U of
   s >= |J| - q rows of R^n such that, for every bulk array x, every coded
   bulk direction v and every head parameter h, the escape norm of the
   projected array at v is at most the norm of the restricted residual
   S_J r(v) + F h. *)

Theorem paper_main_projected_section n D q (J : {set 'I_n}) (F : 'M[R]_(#|J|, q)) :
  exists (s : nat) (U : nat -> nat -> R),
    (#|J| - q <= s)%N /\ paper_main_projected_orthonormal s n U /\
    forall (x : (n * D).-tuple (measurableTypeR R)) (v : nat -> R) (h : 'cV[R]_q),
      (paper_main_gordon_escape_norm s D v (tval (paper_main_projected_map s n D U x)) <=
      sqrt (paper_main_projected_sqnorm
        (paper_main_projected_selector J *m paper_main_projected_bulk_vector n D x v +
          F *m h)))%Rcoq.
Proof.
have [s [V [Hs [HV HVF]]]] := paper_main_projected_complement_mx #|J| q F.
exists s, (paper_main_projected_mx_loading (V *m paper_main_projected_selector J)).
split => //; split.
  apply: paper_main_projected_mx_loading_orthonormal.
  exact: paper_main_projected_compose_orthonormal.
move=> x v h.
rewrite paper_main_projected_escape_norm_mx.
apply: sqrt_le_1_alt.
rewrite -mulmxA.
apply/RleP.
exact: (paper_main_projected_bessel V F _ h HV HVF).
Qed.

(* The section probability bound for fixed head data: the bulk arrays for
   which some unit direction v in A and some head parameter h give a small
   restricted residual lie in a measurable event of probability at most
   exp (- u^2 / 2). The threshold uses |J| - q, a lower bound for the
   complement dimension. The measurability of the original small-residual
   set itself is not claimed. *)

(* The PSD unit sphere of size k + 1 in R^D, D = paper_main_symmetric_dimension k. *)
