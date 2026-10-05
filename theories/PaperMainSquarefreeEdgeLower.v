(* The lower spectral edge of the square-free block, deterministic part:
   the non-backtracking (NB) recursion and the Chebyshev step. No
   probability and no counting estimate.
   1. Chebyshev step. Let B, T m, Rm m be n x n real matrices with T 0 = 1,
      B T 0 = T 1 - s T 0 and B T (m+1) = T (m+2) + T m + Rm (m+1). Then
      B^K = sum_(m <= K) gam K m T m + rem K (pmlo_cheb), with
      sum_m |gam K m| <= 2^K when 0 <= s <= 1 (pmlo_gam_abs). For symmetric
      B and K = 2^(k+1), bounds |v^T T m v| <= tau |v|^2 and operator
      bounds on Rm m and B give -theta I <= B <= theta I as soon as
      2^K tau + rho_K <= theta^K (pmlo_cheb_box), by opnorm_le_form_exp of
      GaussianAnalysis.matrix.opnorm. The operator bounds pmlo_opb are
      those of opnorm (pmlo_opbP).
   2. NB recursion. For X : 'I_N -> C -> R over a finite column type C and
      kap, let P_c = kap offdiag(X_c X_c^T), T^c 0 = 0, T 0 = 1,
      T^c (L+1) = P_c (T L - T^c L) and T (L+1) = sum_c T^c (L+1). Then
      T (L+1) = T 1 T L - sum_(k<L) (-1)^k S_(k+2) T (L-1-k) with
      S_j = sum_c P_c^j (pmlo_rec_S). With E_k = S_(k+2) - s^(k+1) T 1 - s^k I
      and Psi L = sum_(k<L) (-1)^k E_k T (L-1-k), exactly
      (T 1 - s) T (L+1) = T (L+2) + T L + Psi (L+1) + s Psi L (pmlo_knh). *)
From Stdlib Require Import Reals Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic sesquilinear.
From GaussianAnalysis.matrix Require Import euclidean real_spectral opnorm.
From EllipsoidFitting Require Import PaperMainDefinitions PaperMainGeometryPsd PaperMainGeometryHomogeneous
  PaperMainGeometrySeparation PaperMainGeometryHeadCoefficients PaperMainGeometryHeadFeature
  PaperMainGeometryHeadCorrection PaperMainConeConditionOperator PaperMainDiagonalBlockTrace
  PaperMainSymmetricDiagonalization.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

(* 1. The Chebyshev step. The coefficients are defined over any ring, so
   that their operations are the ring operations. *)
Fixpoint pmlo_gam {F : pzRingType} (s : F) (K m : nat) {struct K} : F :=
  if K is K'.+1 then
    (if m is m'.+1 then pmlo_gam s K' m' else 0) + pmlo_gam s K' m.+1 -
    (if m == 0%N then s * pmlo_gam s K' 0 else 0)
  else (m == 0%N)%:R.

Lemma pmlo_gam_out (F : pzRingType) (s : F) K m : (K < m)%N -> pmlo_gam s K m = 0.
Proof.
elim: K m => [|K IH] [|m] //= Hm.
have H1 : (K < m)%N by [].
have H2 : (K < m.+2)%N by apply: (ltn_trans H1); rewrite ltnS leqnSn.
by rewrite (IH m H1) (IH m.+2 H2) subr0 addr0.
Qed.

Section Chebyshev.
Variable n : nat.
Implicit Types (M : 'M[R]_n) (v : 'cV[R]_n).

Fixpoint pmlo_rem (B : 'M[R]_n) (s : R) (Rm : nat -> 'M[R]_n) (K : nat) : 'M[R]_n :=
  if K is K'.+1 then
    B *m pmlo_rem B s Rm K' + \sum_(m < K') pmlo_gam s K' m.+1 *: Rm m.+1
  else 0.

(* One step of the coefficient recursion, against any sequence f. *)
Lemma pmlo_gam_sumS (s : R) (f : nat -> 'M[R]_n) K :
  \sum_(m < K.+2) pmlo_gam s K.+1 m *: f m =
  \sum_(m < K.+1) pmlo_gam s K m *: f m.+1 + \sum_(m < K) pmlo_gam s K m.+1 *: f m -
  (s * pmlo_gam s K 0) *: f 0%N.
Proof.
rewrite big_ord_recl /=.
rewrite (eq_bigr (fun i : 'I_K.+1 => pmlo_gam s K i *: f i.+1 + pmlo_gam s K i.+2 *: f i.+1));
  first by move=> i _; rewrite /bump leq0n add0n add1n subr0 scalerDl.
rewrite big_split /=.
have E3 : \sum_(m < K) pmlo_gam s K m.+1 *: f m =
    pmlo_gam s K 1 *: f 0%N + \sum_(i < K.+1) pmlo_gam s K i.+2 *: f i.+1.
  have -> : \sum_(m < K) pmlo_gam s K m.+1 *: f m = \sum_(m < K.+2) pmlo_gam s K m.+1 *: f m.
    rewrite big_ord_recr big_ord_recr /= !pmlo_gam_out ?ltnSn ?(ltn_trans (ltnSn K)) //.
    by rewrite !scale0r !addr0.
  by rewrite big_ord_recl.
rewrite E3 add0r scalerBl.
set a := pmlo_gam s K 1 *: f 0%N.
set b := (s * pmlo_gam s K 0) *: f 0%N.
set c := \sum_(i < K.+1) pmlo_gam s K i *: f i.+1.
set e := \sum_(i < K.+1) pmlo_gam s K i.+2 *: f i.+1.
by rewrite addrAC [c + (a + e)]addrCA.
Qed.

Lemma pmlo_cheb (B : 'M[R]_n) (s : R) (T Rm : nat -> 'M[R]_n) K :
  T 0%N = 1%:M -> B *m T 0%N = T 1%N - s *: T 0%N ->
  (forall m, B *m T m.+1 = T m.+2 + T m + Rm m.+1) ->
  B ^+ K = \sum_(m < K.+1) pmlo_gam s K m *: T m + pmlo_rem B s Rm K.
Proof.
move=> HT0 HB0 HBS.
elim: K => [|K IH]; first by rewrite expr0 big_ord1 /= scale1r addr0 HT0.
rewrite exprS -mulmxE IH mulmxDr mulmx_sumr /= pmlo_gam_sumS.
rewrite (eq_bigr (fun i : 'I_K.+1 => pmlo_gam s K i *: (B *m T i)));
  first by move=> i _; rewrite scalemxAr.
rewrite big_ord_recl /= HB0.
rewrite (eq_bigr (fun i : 'I_K =>
    pmlo_gam s K i.+1 *: T i.+2 + pmlo_gam s K i.+1 *: T i + pmlo_gam s K i.+1 *: Rm i.+1));
  first by move=> i _; rewrite /bump leq0n add1n HBS !scalerDr.
rewrite !big_split /= [\sum_(m < K.+1) _]big_ord_recl /=.
rewrite [in RHS](eq_bigr (fun i : 'I_K => pmlo_gam s K i.+1 *: T i.+2));
  first by move=> i _; rewrite /bump leq0n add1n.
rewrite scalerBr scalerA [pmlo_gam s K 0 * s]mulrC.
set a := pmlo_gam s K 0 *: T 1%N.
set b := (s * pmlo_gam s K 0) *: T 0%N.
set c := \sum_(i < K) pmlo_gam s K i.+1 *: T i.+2.
set e := \sum_(i < K) pmlo_gam s K i.+1 *: T i.
set g := \sum_(i < K) pmlo_gam s K i.+1 *: Rm i.+1.
set h := B *m pmlo_rem B s Rm K.
rewrite -!addrA; congr (_ + _); rewrite addrCA; congr (_ + _).
by rewrite addrCA; congr (_ + _); rewrite [h + g]addrC addrA.
Qed.

Lemma pmlo_gam_abs (s : R) K : 0 <= s <= 1 -> \sum_(m < K.+1) `|pmlo_gam s K m| <= 2 ^+ K.
Proof.
case/andP=> Hs0 Hs1.
elim: K => [|K IH]; first by rewrite big_ord1 /= normr1 expr0.
rewrite big_ord_recl /=.
set S := \sum_(m < K.+1) `|pmlo_gam s K m|.
have Hext : S = `|pmlo_gam s K 0| + `|pmlo_gam s K 1| +
    \sum_(i < K.+1) `|pmlo_gam s K i.+2|.
  have -> : S = \sum_(m < K.+3) `|pmlo_gam s K m|.
    rewrite big_ord_recr big_ord_recr /= !pmlo_gam_out ?ltnSn ?(ltn_trans (ltnSn K)) //.
    by rewrite normr0 !addr0.
  by rewrite big_ord_recl big_ord_recl addrA.
have H1 : \sum_(i < K.+1) `|pmlo_gam s K (0 + i) + pmlo_gam s K (bump 0 i).+1 - 0| <=
    S + \sum_(i < K.+1) `|pmlo_gam s K i.+2|.
  rewrite -big_split /=; apply: ler_sum => i _.
  by rewrite add0n /bump leq0n add1n subr0 ler_normD.
have H0 : `|0 + pmlo_gam s K 1 - s * pmlo_gam s K 0| <=
    `|pmlo_gam s K 1| + s * `|pmlo_gam s K 0|.
  by rewrite add0r (le_trans (ler_normB _ _)) // normrM ger0_norm.
have Hs : s * `|pmlo_gam s K 0| <= `|pmlo_gam s K 0|.
  by rewrite -[X in _ <= X]mul1r ler_wpM2r.
apply: (le_trans (lerD H0 H1)).
rewrite exprS.
move: Hext Hs IH; rewrite -/S.
set g0 := `|pmlo_gam s K 0|.
set g1 := `|pmlo_gam s K 1|.
set Sg := \sum_(i < K.+1) `|pmlo_gam s K i.+2|.
set sg := s * g0.
move=> Hext Hs IH.
lra.
Qed.

(* Operator bounds |M v|^2 <= c^2 |v|^2, in squared form. *)
Definition pmlo_opb M (c : R) : Prop :=
  0 <= c /\ forall v, ((M *m v)^T *m (M *m v)) 0 0 <= c ^+ 2 * (v^T *m v) 0 0.
Arguments pmlo_opb : clear scopes.

Lemma pmlo_opbP M c : pmlo_opb M c <-> 0 <= c /\ opnorm M <= c.
Proof.
split=> [[c0 Mc]|[c0 Mc]].
  split => //; apply/opnorm_leP => // v.
  rewrite -ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 // exprMn !frobenius_sqr.
  by rewrite !mxdot_colE; exact: Mc.
split => // v; rewrite -!mxdot_colE -!frobenius_sqr -exprMn.
rewrite ler_sqr ?nnegrE ?mulr_ge0 ?frobenius_ge0 //.
exact: (proj2 (opnorm_leP M c0) Mc).
Qed.

Lemma pmlo_opb_mul M1 M2 c1 c2 : pmlo_opb M1 c1 -> pmlo_opb M2 c2 ->
  pmlo_opb (M1 *m M2) (c1 * c2).
Proof.
move=> /pmlo_opbP[c10 H1] /pmlo_opbP[c20 H2]; apply/pmlo_opbP.
split; first exact: mulr_ge0.
exact: le_trans (opnorm_mulmx _ _) (ler_pM (opnorm_ge0 _) (opnorm_ge0 _) H1 H2).
Qed.

Lemma pmlo_opb_add M1 M2 c1 c2 : pmlo_opb M1 c1 -> pmlo_opb M2 c2 ->
  pmlo_opb (M1 + M2) (c1 + c2).
Proof.
move=> /pmlo_opbP[c10 H1] /pmlo_opbP[c20 H2]; apply/pmlo_opbP.
by split; [exact: addr_ge0 | exact: le_trans (opnormD _ _) (lerD H1 H2)].
Qed.

Lemma pmlo_opb_scale M c (a : R) : pmlo_opb M c -> pmlo_opb (a *: M) (`|a| * c).
Proof.
move=> /pmlo_opbP[c0 H]; apply/pmlo_opbP; split; first by rewrite mulr_ge0.
by rewrite opnormZ ler_wpM2l.
Qed.

Lemma pmlo_opb_le M c c' : pmlo_opb M c -> c <= c' -> pmlo_opb M c'.
Proof.
move=> /pmlo_opbP[c0 H] cc; apply/pmlo_opbP.
by split; [exact: le_trans c0 cc | exact: le_trans H cc].
Qed.

Lemma pmlo_opb0 : pmlo_opb 0 0.
Proof. by apply/pmlo_opbP; rewrite opnorm0. Qed.

Lemma pmlo_opb_sum (I : finType) (F : I -> 'M[R]_n) (c : I -> R) :
  (forall i, pmlo_opb (F i) (c i)) -> pmlo_opb (\sum_i F i) (\sum_i c i).
Proof.
move=> H; elim/big_rec2: _ => [|i M c' _ IH]; first exact: pmlo_opb0.
exact: pmlo_opb_add.
Qed.

Lemma pmlo_opb_form M c v : pmlo_opb M c -> `|(v^T *m M *m v) 0 0| <= c * (v^T *m v) 0 0.
Proof.
move=> /pmlo_opbP[c0 H]; rewrite -mulmxA -!mxdot_colE.
apply: le_trans (mxdot_opnorm _ _ _) _.
by rewrite -mulrA -expr2 frobenius_sqr ler_wpM2r ?mxdot_ge0.
Qed.

(* Powers of a symmetric matrix are symmetric. *)
Lemma pmlo_trmx_exp M m : M^T = M -> (M ^+ m)^T = M ^+ m.
Proof.
move=> HM; elim: m => [|m IH]; first by rewrite !expr0 trmx1.
rewrite exprS -mulmxE trmx_mul IH HM.
by rewrite mulmxE -exprSr exprS.
Qed.

(* The remainder rem K has operator bound rho_K. *)
Fixpoint pmlo_rho {F : pzRingType} (beta rho : F) (K : nat) : F :=
  if K is K'.+1 then beta * pmlo_rho beta rho K' + 2 ^+ K' * rho else 0.

Lemma pmlo_rem_opb (B : 'M[R]_n) (s beta rho : R) (Rm : nat -> 'M[R]_n) K :
  0 <= s <= 1 -> pmlo_opb B beta -> 0 <= rho ->
  (forall m, (0 < m < K)%N -> pmlo_opb (Rm m) rho) ->
  pmlo_opb (pmlo_rem B s Rm K) (pmlo_rho beta rho K).
Proof.
move=> Hs HB Hr HR.
elim: K HR => [|K IH] HR /=; first exact: pmlo_opb0.
have HR' : forall m, (0 < m < K)%N -> pmlo_opb (Rm m) rho.
  move=> m /andP [H0 H1]; apply: HR; rewrite H0 /=; exact: ltn_trans H1 (ltnSn K).
have H1 := pmlo_opb_mul _ _ _ _ HB (IH HR').
have H2 : pmlo_opb (\sum_(m < K) pmlo_gam s K m.+1 *: Rm m.+1)
    (\sum_(m < K) `|pmlo_gam s K m.+1| * rho).
  apply: pmlo_opb_sum => m; apply: pmlo_opb_scale; apply: HR.
  by rewrite /= ltnS (ltn_ord m).
apply: pmlo_opb_le (pmlo_opb_add _ _ _ _ H1 H2) _.
apply: lerD => //.
rewrite -mulr_suml; apply: ler_wpM2r => //.
apply: le_trans (pmlo_gam_abs s K Hs).
by rewrite big_ord_recl lerDr.
Qed.

Lemma pmlo_form_sum (I : finType) (F : I -> 'M[R]_n) (a : I -> R) v :
  paper_main_quadratic_form (\sum_i a i *: F i) v =
  \sum_i a i * paper_main_quadratic_form (F i) v.
Proof.
elim/big_rec2: _ => [|i y1 y2 _ IH].
  by rewrite paper_main_quadratic_formE mulmx0 mul0mx mxE.
by rewrite pms_formD paper_main_form_scale IH.
Qed.

(* The Chebyshev box: from bounds on the T m and the remainders, Loewner
   bounds on B. *)
Theorem pmlo_cheb_box (B : 'M[R]_n) (s tau beta rho theta : R) (T Rm : nat -> 'M[R]_n) k :
  B^T = B -> 0 <= s <= 1 -> T 0%N = 1%:M -> B *m T 0%N = T 1%N - s *: T 0%N ->
  (forall m, B *m T m.+1 = T m.+2 + T m + Rm m.+1) ->
  0 <= tau -> (forall m v, (m <= 2 ^ k.+1)%N ->
    `|(v^T *m T m *m v) 0 0| <= tau * (v^T *m v) 0 0) ->
  pmlo_opb B beta -> 0 <= rho -> (forall m, (0 < m < 2 ^ k.+1)%N -> pmlo_opb (Rm m) rho) ->
  0 <= theta -> 2 ^+ (2 ^ k.+1) * tau + pmlo_rho beta rho (2 ^ k.+1) <= theta ^+ (2 ^ k.+1) ->
  paper_main_loewner_le ((- theta) *: 1%:M) B /\ paper_main_loewner_le B (theta *: 1%:M).
Proof.
move=> HBs Hs HT0 HB0 HBS Htau HT HB Hr HR Hth Hbound.
set K := (2 ^ k.+1)%N in HT HR Hbound *.
have Hrem := pmlo_rem_opb B s beta rho Rm K Hs HB Hr HR.
(* The quadratic form of B^K, by the expansion. *)
have HBK : forall v, (v^T *m B ^+ K *m v) 0 0 <= theta ^+ K * (v^T *m v) 0 0.
  move=> v.
  set w := (v^T *m v) 0 0.
  have Hw : 0 <= w by exact: pmh_vec_sqr_ge0.
  rewrite (pmlo_cheb B s T Rm K HT0 HB0 HBS).
  rewrite -paper_main_quadratic_formE pms_formD pmlo_form_sum.
  have H1 : \sum_(m < K.+1) pmlo_gam s K m * paper_main_quadratic_form (T m) v <=
      2 ^+ K * tau * w.
    apply: le_trans (ler_norm _) _; apply: le_trans (ler_norm_sum _ _ _) _.
    apply: le_trans (_ : \sum_(m < K.+1) `|pmlo_gam s K m| * (tau * w) <= _).
      apply: ler_sum => m _; rewrite normrM; apply: ler_wpM2l => //.
      by rewrite paper_main_quadratic_formE; apply: HT; rewrite -ltnS ltn_ord.
    rewrite -mulr_suml -mulrA; apply: ler_wpM2r; first exact: mulr_ge0.
    exact: pmlo_gam_abs.
  have H2 : paper_main_quadratic_form (pmlo_rem B s Rm K) v <= pmlo_rho beta rho K * w.
    apply: le_trans (ler_norm _) _; rewrite paper_main_quadratic_formE.
    exact: pmlo_opb_form.
  apply: le_trans (lerD H1 H2) _.
  by rewrite -mulrDl; apply: ler_wpM2r.
(* The operator bound from the even power K. *)
have HBsym : B \is symmetricmx by exact/symmetricmxP.
apply/paper_main_loewner_boxP; split => //.
apply/(opnorm_symP HBsym Hth)/(opnorm_le_form_exp HBsym (p := K)) => //.
- by rewrite /K oddX.
- by rewrite /K expn_gt0.
by move=> v; rewrite !mxdot_colE mulmxA; exact: HBK.
Qed.

End Chebyshev.

(* 2. The non-backtracking recursion. *)
Section Recursion.
Variables (N : nat) (C : finType) (X : 'I_N -> C -> R) (kap : R).

Definition pmlo_P (c : C) : 'M[R]_N :=
  \matrix_(i, j) if i == j then 0 else kap * (X i c * X j c).

Fixpoint pmlo_TT (L : nat) : 'M[R]_N * (C -> 'M[R]_N) :=
  if L is L'.+1 then
    let p := pmlo_TT L' in
    (\sum_c pmlo_P c *m (p.1 - p.2 c), fun c => pmlo_P c *m (p.1 - p.2 c))
  else (1%:M, fun _ => 0).

Definition pmlo_T (L : nat) : 'M[R]_N := (pmlo_TT L).1.
Definition pmlo_Tc (L : nat) (c : C) : 'M[R]_N := (pmlo_TT L).2 c.

Lemma pmlo_T0 : pmlo_T 0 = 1%:M.
Proof. by []. Qed.

Lemma pmlo_Tc0 c : pmlo_Tc 0 c = 0.
Proof. by []. Qed.

Lemma pmlo_TcS L c : pmlo_Tc L.+1 c = pmlo_P c *m (pmlo_T L - pmlo_Tc L c).
Proof. by []. Qed.

Lemma pmlo_TS L : pmlo_T L.+1 = \sum_c pmlo_Tc L.+1 c.
Proof. by []. Qed.

Lemma pmlo_T1 : pmlo_T 1 = \sum_c pmlo_P c.
Proof.
rewrite pmlo_TS; apply: eq_bigr => c _.
by rewrite pmlo_TcS pmlo_T0 pmlo_Tc0 subr0 mulmx1.
Qed.

Lemma pmlo_rec L : pmlo_T L.+1 = pmlo_T 1 *m pmlo_T L - \sum_c pmlo_P c *m pmlo_Tc L c.
Proof.
rewrite pmlo_TS pmlo_T1 mulmx_suml -sumrB; apply: eq_bigr => c _.
by rewrite pmlo_TcS mulmxBr.
Qed.

Lemma pmlo_Tc_unroll L c :
  pmlo_Tc L c = \sum_(k < L) (-1) ^+ k *: (pmlo_P c ^+ k.+1 *m pmlo_T (L - k.+1)).
Proof.
elim: L => [|L IH]; first by rewrite pmlo_Tc0 big_ord0.
rewrite pmlo_TcS IH mulmxBr mulmx_sumr big_ord_recl /= expr0 scale1r expr1 subn1 /=.
rewrite -sumrN; congr (_ + _); apply: eq_bigr => i _.
rewrite /bump leq0n add1n subSS [(-1) ^+ i.+1]exprS mulN1r scaleNr; congr (- _).
by rewrite -scalemxAr mulmxA mulmxE -exprS.
Qed.

Definition pmlo_S (j : nat) : 'M[R]_N := \sum_c pmlo_P c ^+ j.

Lemma pmlo_rec_S L : pmlo_T L.+1 = pmlo_T 1 *m pmlo_T L -
  \sum_(k < L) (-1) ^+ k *: (pmlo_S k.+2 *m pmlo_T (L - k.+1)).
Proof.
rewrite pmlo_rec; congr (_ - _).
rewrite (eq_bigr (fun c => \sum_(k < L) (-1) ^+ k *: (pmlo_P c ^+ k.+2 *m pmlo_T (L - k.+1)))).
  move=> c _; rewrite pmlo_Tc_unroll mulmx_sumr; apply: eq_bigr => k _.
  by rewrite -scalemxAr mulmxA mulmxE -exprS.
rewrite exchange_big /=; apply: eq_bigr => k _.
by rewrite -scaler_sumr /pmlo_S mulmx_suml.
Qed.

Variable s : R.

Definition pmlo_E (k : nat) : 'M[R]_N :=
  pmlo_S k.+2 - s ^+ k.+1 *: pmlo_T 1 - s ^+ k *: 1%:M.

Definition pmlo_Psi (L : nat) : 'M[R]_N :=
  \sum_(k < L) (-1) ^+ k *: (pmlo_E k *m pmlo_T (L - k.+1)).

Definition pmlo_Phi (L : nat) : 'M[R]_N :=
  \sum_(k < L) ((-1) ^+ k * s ^+ k) *: pmlo_T (L - k.+1).

Lemma pmlo_PhiS L : pmlo_Phi L.+1 = pmlo_T L - s *: pmlo_Phi L.
Proof.
rewrite /pmlo_Phi big_ord_recl /= expr0 !mul1r scale1r subn1 /=; congr (_ + _).
rewrite scaler_sumr -sumrN; apply: eq_bigr => i _.
rewrite /bump leq0n add1n subSS !exprS scalerA -scaleNr; congr (_ *: _).
ring.
Qed.

Lemma pmlo_rec_Phi L : pmlo_T L.+1 =
  pmlo_T 1 *m pmlo_T L - (s *: pmlo_T 1 + 1%:M) *m pmlo_Phi L - pmlo_Psi L.
Proof.
rewrite pmlo_rec_S -addrA -opprD; congr (_ - _).
rewrite /pmlo_Psi /pmlo_Phi mulmx_sumr -big_split /=; apply: eq_bigr => k _.
have HS : pmlo_S k.+2 = pmlo_E k + s ^+ k.+1 *: pmlo_T 1 + s ^+ k *: 1%:M.
  by rewrite /pmlo_E -addrA [_ *: pmlo_T 1 + _]addrC addrA !subrK.
rewrite HS -scalemxAr !mulmxDl -!scalemxAl mul1mx !scalerDr !scalerA.
set T1 := pmlo_T 1 *m pmlo_T (L - k.+1).
set Tk := pmlo_T (L - k.+1).
by rewrite [s ^+ k.+1]exprSr mulrA [RHS]addrC !addrA.
Qed.

(* The exact form of KNH Lemma 5.1 on the row side. *)
Theorem pmlo_knh L : (pmlo_T 1 - s *: 1%:M) *m pmlo_T L.+1 =
  pmlo_T L.+2 + pmlo_T L + (pmlo_Psi L.+1 + s *: pmlo_Psi L).
Proof.
rewrite mulmxBl -scalemxAl mul1mx.
rewrite [in X in _ - s *: X](pmlo_rec_Phi L).
rewrite (pmlo_rec_Phi L.+1) pmlo_PhiS.
rewrite !mulmxDl !mulmxBr -!scalemxAl !mul1mx -!scalemxAr.
set a := pmlo_T 1 *m pmlo_T L.+1.
set b := pmlo_T 1 *m pmlo_T L.
set c := pmlo_T 1 *m pmlo_Phi L.
set P := pmlo_Phi L.
set Tl := pmlo_T L.
set Q1 := pmlo_Psi L.+1.
set Q := pmlo_Psi L.
by apply/matrixP => i j; rewrite !mxE; ring.
Qed.

End Recursion.
