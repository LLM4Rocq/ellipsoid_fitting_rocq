From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix sesquilinear.
From mathcomp Require Import boolp classical_sets reals topology normedtype.
From mathcomp Require Import derive ring_tactic field_tactic.
From GaussianAnalysis.matrix Require Import euclidean.

(**md**************************************************************************)
(* # The spectral theorem for real symmetric matrices                         *)
(*                                                                            *)
(* Every real symmetric matrix A is orthogonally diagonalizable:              *)
(* A = P^T *m diag_mx d *m P with P orthogonal (symmetric_spectral). The      *)
(* proof is the analytic one and works over any realType: the quadratic form  *)
(* of A attains its maximum on the compact unit sphere, a maximizer is an     *)
(* eigenvector, and the Householder reflection that sends it to the first     *)
(* basis vector splits off one dimension. No complex number is used.          *)
(*                                                                            *)
(* ```                                                                        *)
(*       householder w == the Householder reflection                          *)
(*                        1 - (2 / mxdot w w) *: (w *m w^T) of w : 'cV[R]_n,  *)
(*                        equal to 1 when w = 0                               *)
(*    sym_spectralmx A == an orthogonal matrix P such that                    *)
(*                        A = P^T *m diag_mx (sym_spectral_diag A) *m P when  *)
(*                        A is symmetric                                      *)
(* sym_spectral_diag A == the eigenvalues of A, in the order of the rows of   *)
(*                        sym_spectralmx A                                    *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section symmetricmx.
Variable R : fieldType.

Lemma symmetricmxP n (A : 'M[R]_n) : reflect (A^T = A) (A \is symmetricmx).
Proof.
by apply: (iffP (is_hermitianmxP _ _ _)); rewrite expr0 scale1r map_mx_id.
Qed.

Lemma symmetricmx_conj m n (A : 'M[R]_n) (P : 'M[R]_(m, n)) :
  A \is symmetricmx -> P *m A *m P^T \is symmetricmx.
Proof.
move=> /symmetricmxP AT; apply/symmetricmxP.
by rewrite !trmx_mul trmxK AT mulmxA.
Qed.

End symmetricmx.

Section continuity.
Variable R : realType.

Lemma continuous_bigsum (T : topologicalType) I (r : seq I) (f : I -> T -> R) :
  (forall i, continuous (f i)) -> continuous (fun x => \sum_(i <- r) f i x).
Proof.
move=> fc; elim: r => [|i r IH].
  by under eq_fun do rewrite big_nil; exact: cst_continuous.
under eq_fun do rewrite big_cons.
by move=> x; apply: (@continuousD _ R^o); [exact: fc | exact: IH].
Qed.

Lemma continuous_form n (A : 'M[R]_n) :
  continuous (fun w : 'rV[R]_n => (w *m A *m w^T) 0 0).
Proof.
have -> : (fun w : 'rV[R]_n => (w *m A *m w^T) 0 0) =
    (fun w => \sum_j \sum_i w 0 i * A i j * w 0 j).
  apply/funext => w; rewrite mxE; apply: eq_bigr => j _.
  by rewrite mxE [w^T j 0]mxE mulr_suml; apply: eq_bigr => i _.
apply: continuous_bigsum => j; apply: continuous_bigsum => i => w.
apply: (continuousM (s := fun v : 'rV[R]_n => v 0 i * A i j) (t := fun v => v 0 j)).
  apply: (continuousM (s := fun v : 'rV[R]_n => v 0 i) (t := fun=> A i j)).
    exact: coord_continuous.
  exact: cst_continuous.
exact: coord_continuous.
Qed.

Lemma continuous_mxdot n : continuous (fun w : 'rV[R]_n => mxdot w w).
Proof.
have -> : (fun w : 'rV[R]_n => mxdot w w) =
    (fun w => (w *m 1%:M *m w^T) 0 0) by apply/funext => w; rewrite mulmx1 mxdot_rowE.
exact: continuous_form.
Qed.

Lemma compact_unit_sphere n : compact [set w : 'rV[R]_n | mxdot w w = 1].
Proof.
apply: bounded_closed_compact.
  exists 1; split; first exact: num_real.
  move=> M M1 w /= ww1; apply: le_trans (ltW M1).
  rewrite [leLHS]/Num.Def.normr /= mx_normrE; apply/bigmax_leP; split => // ij _.
  by rewrite -[1]sqrtr1 -ww1 -/(frobenius w) frobenius_entry.
apply: (@preimage_closed _ _ (fun w : 'rV[R]_n => mxdot w w) [set 1]).
  by move=> x _; exact: continuous_mxdot.
exact: closed_eq.
Qed.

End continuity.

Section householder.
Variable R : realFieldType.
Implicit Types n : nat.

Definition householder n (w : 'cV[R]_n) : 'M[R]_n :=
  1%:M - (2 / mxdot w w) *: (w *m w^T).

Lemma householder0 n : householder (0 : 'cV[R]_n) = 1%:M.
Proof. by rewrite /householder mul0mx scaler0 subr0. Qed.

Lemma householder_tr n (w : 'cV[R]_n) : (householder w)^T = householder w.
Proof. by rewrite /householder linearB /= trmx1 linearZ /= trmx_mul trmxK. Qed.

Lemma householder_sym n (w : 'cV[R]_n) : householder w \is symmetricmx.
Proof. exact/symmetricmxP/householder_tr. Qed.

Lemma householderK n (w : 'cV[R]_n) : householder w *m householder w = 1%:M.
Proof.
have [->|w0] := eqVneq w 0; first by rewrite householder0 mulmx1.
set s := mxdot w w; have s0 : s != 0 by rewrite mxdot_eq0.
set W := w *m w^T.
have WW : W *m W = s *: W.
  rewrite /W mulmxA -(mulmxA w) [w^T *m w]mx11_scalar -mxdot_colE.
  by rewrite mul_mx_scalar -scalemxAl.
rewrite /householder -/s -/W mulmxBl mul1mx mulmxBr mulmx1 -scalemxAl.
rewrite -scalemxAr WW !scalerA -mulrA divfK // mulr_natr mulr2n scalerDl.
set X := (_ / s) *: W.
have -> : X - (X + X) = - X by rewrite opprD addrA subrr sub0r.
by rewrite opprK subrK.
Qed.

Lemma householder_orthogonal n (w : 'cV[R]_n) : householder w \is orthogonalmx.
Proof. by apply/orthogonalmxP; rewrite householder_tr householderK. Qed.

Lemma householder_swap n (u v : 'cV[R]_n) :
  mxdot u u = mxdot v v -> householder (u - v) *m u = v.
Proof.
move=> uv; have [uv0|w0] := eqVneq (u - v) 0.
  by rewrite uv0 householder0 mul1mx; apply/eqP; rewrite -subr_eq0 uv0.
set w := u - v; have s0 : mxdot w w != 0 by rewrite mxdot_eq0.
have ws : mxdot w w = 2 * mxdot w u.
  by rewrite /w !mxdotBl !mxdotBr (mxdotC v u) uv; ring.
have c0 : mxdot w u != 0 by move: s0; rewrite ws mulf_eq0 negb_or => /andP[].
rewrite /householder mulmxBl mul1mx -scalemxAl -mulmxA.
rewrite [w^T *m u]mx11_scalar -mxdot_colE mul_mx_scalar scalerA ws invfM mulrA.
by rewrite mulfV ?pnatr_eq0 // mul1r mulVf // scale1r /w opprB addrC subrK.
Qed.

End householder.

Section spectral.
Variable R : realType.
Implicit Types n : nat.

Lemma householderN n (w : 'cV[R]_n) : householder (- w) = householder w.
Proof. by rewrite /householder mxdotNl mxdotNr opprK linearN /= mulNmx mulmxN opprK. Qed.

Lemma mxdot_mulmx_sym n (M : 'M[R]_n) (x y : 'cV[R]_n) :
  M \is symmetricmx -> mxdot (M *m x) y = mxdot x (M *m y).
Proof. by move=> /symmetricmxP MT; rewrite mxdot_mulmxl MT. Qed.

(* A nonnegative symmetric form vanishes at v only if M v = 0. *)
Lemma psd_form_eq0 n (M : 'M[R]_n) (v : 'cV[R]_n) :
  M \is symmetricmx -> (forall x : 'cV[R]_n, 0 <= mxdot x (M *m x)) ->
  mxdot v (M *m v) = 0 -> M *m v = 0.
Proof.
move=> Msym Mpsd v0; set x := M *m v.
set b := mxdot x x; set c := mxdot x (M *m x).
have c0 : 0 <= c := Mpsd x.
have line t : 0 <= t * b *+ 2 + t ^+ 2 * c.
  have := Mpsd (v + t *: x).
  rewrite mulmxDr -!scalemxAr !mxdotDl !mxdotDr !mxdotZl !mxdotZr.
  rewrite v0 -[mxdot v (M *m x)]mxdot_mulmx_sym // -/x -/b -/c.
  by have -> : 0 + t * b + (t * b + t * (t * c)) = t * b *+ 2 + t ^+ 2 * c by ring.
have c1 : c + 1 != 0 by rewrite lt0r_neq0 // ltr_wpDl.
have := line (- (b / (c + 1))).
have -> : - (b / (c + 1)) * b *+ 2 + (- (b / (c + 1))) ^+ 2 * c =
    - (b ^+ 2 * (c + 2) / (c + 1) ^+ 2) by field.
rewrite oppr_ge0 pmulr_lle0 ?invr_gt0 ?exprn_gt0 ?ltr_wpDl // pmulr_lle0 ?ltr_wpDl //.
move=> b2; have /eqP : b ^+ 2 = 0 by apply/eqP; rewrite eq_le b2 sqr_ge0.
by rewrite sqrf_eq0 mxdot_eq0 => /eqP.
Qed.

Lemma rayleigh_max n (A : 'M[R]_n.+1) :
  exists2 v : 'cV[R]_n.+1, mxdot v v = 1 &
    forall x : 'cV[R]_n.+1, mxdot x (A *m x) <= mxdot v (A *m v) * mxdot x x.
Proof.
set S := [set w : 'rV[R]_n.+1 | mxdot w w = 1].
have S0 : S !=set0 by exists (delta_mx 0 0); rewrite /S /= mxdot_delta mxE !eqxx.
have f_cont : {within S, continuous (fun w : 'rV[R]_n.+1 => (w *m A *m w^T) 0 0)}.
  exact/continuous_subspaceT/continuous_form.
have [w wS wmax] := EVT_max_rV S0 (@compact_unit_sphere R n.+1) f_cont.
have formE (t : 'rV[R]_n.+1) : (t *m A *m t^T) 0 0 = mxdot t^T (A *m t^T).
  by rewrite mxdot_colE trmxK mulmxA.
exists w^T; first by rewrite mxdot_trmx; move: wS; rewrite inE.
move=> x; have [->|x0] := eqVneq x 0; first by rewrite mxdot0l mxdot0r mulr0.
have fx_gt0 : 0 < frobenius x by rewrite frobenius_gt0.
set c := frobenius x; set y := c^-1 *: x.
have yS : y^T \in S.
  rewrite inE /S /= mxdot_trmx /y mxdotZl mxdotZr mulrA -expr2 -frobenius_sqr.
  by rewrite -exprMn mulVf ?gt_eqF // expr1n.
have := wmax _ yS; rewrite !formE trmxK /y -scalemxAr mxdotZl mxdotZr mulrA.
by rewrite -expr2 exprVn mulrC ler_pdivrMr ?exprn_gt0 // frobenius_sqr.
Qed.

Lemma symmetric_eigenvector n (A : 'M[R]_n.+1) : A \is symmetricmx ->
  exists2 v : 'cV[R]_n.+1, mxdot v v = 1 & A *m v = mxdot v (A *m v) *: v.
Proof.
move=> Asym; have [v v1 vmax] := rayleigh_max A.
exists v => //; set l := mxdot v (A *m v).
have Msym : l%:M - A \is symmetricmx.
  by apply/symmetricmxP; rewrite linearB /= tr_scalar_mx (symmetricmxP _ Asym).
have Mform (x : 'cV[R]_n.+1) :
    mxdot x ((l%:M - A) *m x) = l * mxdot x x - mxdot x (A *m x).
  by rewrite mulmxBl mul_scalar_mx mxdotBr mxdotZr.
have Mpsd (x : 'cV[R]_n.+1) : 0 <= mxdot x ((l%:M - A) *m x).
  by rewrite Mform subr_ge0; exact: vmax.
have v0 : mxdot v ((l%:M - A) *m v) = 0 by rewrite Mform v1 mulr1 subrr.
have := psd_form_eq0 Msym Mpsd v0.
by rewrite mulmxBl mul_scalar_mx => /eqP; rewrite subr_eq0 => /eqP <-.
Qed.

Lemma symmetric_block_of_eigen k (M : 'M[R]_(1 + k)) (l : R) :
  M \is symmetricmx -> M *m col_mx 1%:M 0 = l *: col_mx 1%:M 0 ->
  M = block_mx l%:M 0 0 (drsubmx M) /\ drsubmx M \is symmetricmx.
Proof.
move=> /symmetricmxP MT Me.
have MB := submxK M.
move: Me; rewrite -{1}MB mul_block_col !mulmx1 !mulmx0 !addr0 scale_col_mx.
move=> /eq_col_mx [Mul Mdl].
have Mur : ursubmx M = 0.
  have := MT; rewrite -{1 2}MB tr_block_mx => /eq_block_mx [_ H _ _].
  by rewrite -H Mdl scaler0 trmx0.
have Mdr : (drsubmx M)^T = drsubmx M.
  by have := MT; rewrite -{1 2}MB tr_block_mx => /eq_block_mx [_ _ _ H].
split; last exact/symmetricmxP.
rewrite -{1}MB Mur Mdl scaler0; congr block_mx.
by rewrite Mul -mul_mx_scalar mul1mx.
Qed.

Theorem symmetric_spectral n (A : 'M[R]_n) : A \is symmetricmx ->
  exists2 P : 'M[R]_n, P \is orthogonalmx &
    exists d : 'rV[R]_n, A = P^T *m diag_mx d *m P.
Proof.
elim: n A => [|k IH] A Asym.
  exists 1%:M; first exact: orthogonalmx1.
  by exists 0; apply/matrixP => i; case: i.
have [v v1 Av] := symmetric_eigenvector Asym; set l := mxdot v (A *m v) in Av.
pose e : 'cV[R]_(1 + k) := col_mx 1%:M 0.
have e1 : mxdot e e = 1.
  by rewrite mxdot_colE /e tr_col_mx mul_row_col trmx1 mulmx1 trmx0 mul0mx addr0 mxE.
pose H : 'M[R]_(1 + k) := householder (v - e).
have Hv : H *m v = e by apply: householder_swap; rewrite v1 e1.
have He : H *m e = v.
  by rewrite /H -householderN opprB; apply: householder_swap; rewrite v1 e1.
have HT : H^T = H by exact: householder_tr.
have HH : H *m H = 1%:M by exact: householderK.
pose M : 'M[R]_(1 + k) := H *m A *m H.
have Msym : M \is symmetricmx by rewrite /M -{2}HT symmetricmx_conj.
have Me : M *m e = l *: e by rewrite /M -!mulmxA He Av -scalemxAr Hv.
have [MB Mdr] := symmetric_block_of_eigen Msym Me.
have [P' P'o [d' A'd]] := IH _ Mdr.
pose P : 'M[R]_(1 + k) := block_mx 1%:M 0 0 P'.
exists (P *m H).
  apply: mul_orthogonalmx; last exact: householder_orthogonal.
  exact: (orthogonal_block_mx (orthogonalmx1 _ 1) P'o).
exists (row_mx l%:M d').
have PdP : P^T *m diag_mx (row_mx l%:M d') *m P = M.
  rewrite diag_mx_row /P tr_block_mx !trmx0 trmx1.
  rewrite !mulmx_block !mulmx0 !mul0mx !mulmx1 !mul1mx !addr0 !add0r mul0mx.
  have -> : diag_mx (l%:M : 'rV[R]_1) = l%:M.
    by apply/matrixP => i j; rewrite !ord1 !mxE.
  by rewrite -A'd {2}MB.
rewrite trmx_mul HT.
have -> : H *m P^T *m diag_mx (row_mx l%:M d') *m (P *m H) =
    H *m (P^T *m diag_mx (row_mx l%:M d') *m P) *m H by rewrite !mulmxA.
by rewrite PdP /M !mulmxA HH mul1mx -mulmxA HH mulmx1.
Qed.

End spectral.

Section spectral_consequences.
Variable R : realType.
Implicit Types n : nat.

Lemma spectral_eigenvector n (A P : 'M[R]_n) (d : 'rV[R]_n) i :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  A *m (row i P)^T = d 0 i *: (row i P)^T.
Proof.
move=> /orthogonalmxP PP ->.
have Pu : P *m (row i P)^T = delta_mx i 0 by rewrite tr_row colE mulmxA PP mul1mx.
have De : diag_mx d *m (delta_mx i 0 : 'cV[R]_n) = d 0 i *: delta_mx i 0.
  apply/matrixP => j k; rewrite mul_diag_mx !mxE.
  by have [->|] := eqVneq j i; rewrite ?mulr1 ?mulr0.
by rewrite -mulmxA Pu -mulmxA De -scalemxAr -colE tr_row.
Qed.

Lemma orthogonalmx_row_unit n (P : 'M[R]_n) i :
  P \is orthogonalmx -> mxdot (row i P)^T (row i P)^T = 1.
Proof.
move=> /orthogonalmxP PP.
have := congr1 (fun M : 'M[R]_n => M i i) PP; rewrite !mxE eqxx mulr1n => <-.
by rewrite mxdot_trmx /mxdot big_ord1; apply: eq_bigr => k _; rewrite !mxE.
Qed.

Lemma spectral_trace n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P -> \tr A = \sum_i d 0 i.
Proof.
move=> /orthogonalmxP PP ->.
by rewrite mxtrace_mulC mulmxA PP mul1mx mxtrace_diag.
Qed.

Lemma spectral_mxdot n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P -> mxdot A A = \sum_i d 0 i ^+ 2.
Proof.
move=> Po ->; rewrite mxdot_orthogonalmxr // mxdot_orthogonalmxl ?trmx_orthogonal //.
by rewrite mxdot_diag; apply: eq_bigr => i _; rewrite expr2.
Qed.

Lemma spectral_form n (A P : 'M[R]_n) (d : 'rV[R]_n) (x : 'cV[R]_n) :
  A = P^T *m diag_mx d *m P -> mxdot x (A *m x) = \sum_i d 0 i * (P *m x) i 0 ^+ 2.
Proof.
move=> ->; rewrite -!mulmxA mxdotC mxdot_mulmxl trmxK /mxdot.
by apply: eq_bigr => i _; rewrite big_ord1 mul_diag_mx mxE expr2 mulrA.
Qed.

Lemma spectral_form_le n (A P : 'M[R]_n) (d : 'rV[R]_n) (b : R) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  (forall x : 'cV[R]_n, mxdot x (A *m x) <= b * mxdot x x) <-> (forall i, d 0 i <= b).
Proof.
move=> Po AE; split => [Hb i|Hd x].
  have := Hb (row i P)^T; rewrite (spectral_eigenvector _ Po AE) mxdotZr.
  by rewrite orthogonalmx_row_unit // !mulr1.
rewrite (spectral_form _ AE) -(mxdot_orthogonalmxl _ _ Po) /mxdot mulr_sumr.
by apply: ler_sum => i _; rewrite big_ord1 -expr2 ler_wpM2r ?sqr_ge0.
Qed.

Lemma spectral_form_ge n (A P : 'M[R]_n) (d : 'rV[R]_n) (b : R) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  (forall x : 'cV[R]_n, b * mxdot x x <= mxdot x (A *m x)) <-> (forall i, b <= d 0 i).
Proof.
move=> Po AE; split => [Hb i|Hd x].
  have := Hb (row i P)^T; rewrite (spectral_eigenvector _ Po AE) mxdotZr.
  by rewrite orthogonalmx_row_unit // !mulr1.
rewrite (spectral_form _ AE) -(mxdot_orthogonalmxl _ _ Po) /mxdot mulr_sumr.
by apply: ler_sum => i _; rewrite big_ord1 -expr2 ler_wpM2r ?sqr_ge0.
Qed.

Lemma spectral_psd n (A P : 'M[R]_n) (d : 'rV[R]_n) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  (forall x : 'cV[R]_n, 0 <= mxdot x (A *m x)) <-> (forall i, 0 <= d 0 i).
Proof.
move=> Po AE; rewrite -(spectral_form_ge 0 Po AE).
by split=> H x; have := H x; rewrite mul0r.
Qed.

Lemma spectral_form_abs n (A P : 'M[R]_n) (d : 'rV[R]_n) (b : R) :
  P \is orthogonalmx -> A = P^T *m diag_mx d *m P ->
  (forall x : 'cV[R]_n, `|mxdot x (A *m x)| <= b * mxdot x x) <->
  (forall i, `|d 0 i| <= b).
Proof.
move=> Po AE; have le := spectral_form_le b Po AE.
have ge := spectral_form_ge (- b) Po AE.
split=> [H i|H].
  rewrite ler_norml; apply/andP; split.
    apply: (proj1 ge) i => x; rewrite mulNr lerNl.
    by apply: le_trans (H x); rewrite -normrN ler_norm.
  by apply: (proj1 le) i => x; exact: le_trans (ler_norm _) (H x).
move=> x; rewrite ler_norml; apply/andP; split.
  by rewrite -mulNr; apply: (proj2 ge) => i; rewrite lerNl; have /ler_normlP[] := H i.
by apply: (proj2 le) => i; have /ler_normlP[] := H i.
Qed.

(* A chosen orthogonal diagonalization. *)

Lemma ex_sym_spectral n (A : 'M[R]_n) : exists Pd : 'M[R]_n * 'rV[R]_n,
  (Pd.1 \is orthogonalmx) &&
  ((A \is symmetricmx) ==> (A == Pd.1^T *m diag_mx Pd.2 *m Pd.1)).
Proof.
have [Asym|] := boolP (A \is symmetricmx); last by exists (1%:M, 0); rewrite orthogonalmx1.
by have [P Po [d AE]] := symmetric_spectral Asym; exists (P, d); rewrite Po AE eqxx.
Qed.

Definition sym_spectralmx n (A : 'M[R]_n) : 'M[R]_n := (xchoose (ex_sym_spectral A)).1.
Definition sym_spectral_diag n (A : 'M[R]_n) : 'rV[R]_n :=
  (xchoose (ex_sym_spectral A)).2.

Lemma sym_spectralmx_orthogonal n (A : 'M[R]_n) : sym_spectralmx A \is orthogonalmx.
Proof. by have /andP[] := xchooseP (ex_sym_spectral A). Qed.

Lemma sym_spectralE n (A : 'M[R]_n) : A \is symmetricmx ->
  A = (sym_spectralmx A)^T *m diag_mx (sym_spectral_diag A) *m sym_spectralmx A.
Proof. by move=> Asym; have /andP[_ /implyP/(_ Asym)/eqP] := xchooseP (ex_sym_spectral A). Qed.

End spectral_consequences.
