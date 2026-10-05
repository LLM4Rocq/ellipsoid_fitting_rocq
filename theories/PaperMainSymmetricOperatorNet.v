(* Deterministic discretization of the bilinear operator bound by contained
   sphere nets, on the public matrices of dimension N = n + 1, for the
   Gaussian operator tail.

   paper_main_gordon_finite_net (PaperMainGordonNets) is a contained eps-net
   of a set of list-coordinate vectors in squared Gordon distance. For the
   unit sphere of R^N in list coordinates, every public unit column x has
   coordinates pmon_coords x with paper_main_symmetric_column n
   (pmon_coords x) = x. So the net covers public unit columns, and its
   points are public unit columns (pmon_net_cover, pmon_net_unit).

   For Z : 'M[R]_N, let M be the supremum of |u^T Z w| over unit u, w
   (paper_main_symmetric_operator_sup). It is finite because
   |x^T Z y| <= |Z|_F |x| |y|, and |x^T Z y| <= M |x| |y| for all x, y,
   zero included (pmon_homogeneous). Let v be a contained eps-net indexed by
   t < s, with 0 <= eps and 2 eps < 1, and let u_t be the column of v t. If
   |u_t^T Z u_t'| <= b for all t, t' < s, then |u^T Z w| <= b + 2 eps M for
   unit u, w, so M (1 - 2 eps) <= b. With beta (1 - 2 eps) = b this gives
   paper_main_cone_opnorm_le Z beta, that is
   (x^T Z y)^2 <= beta^2 |x|^2 |y|^2 for all x, y
   (paper_main_symmetric_operator_net_bound). The contrapositive gives a net
   pair with b < |u_t^T Z u_t'| (paper_main_symmetric_operator_net_witness).
   Nets exist independently of Z: for s the length of the entropy grid of
   PaperMainGordonEntropy, 0 < s and ln s <= (4 + 4/eps) ln 2 N
   (paper_main_symmetric_operator_net_exists). At eps = 1/4, beta = 2 b and
   the constant is 20 ln 2 (paper_main_symmetric_operator_net_quarter,
   paper_main_symmetric_operator_entropy_quarter).
   paper_main_symmetric_operator_net_quarter_stdlib restates the eps = 1/4
   package with Stdlib operators (Nat.lt, Rle, Rmult, Rabs), in the form of
   the hypotheses of the Stdlib Gaussian net tail. No probability, no
   spectral theorem. Nothing from the paper is assumed. *)
From Stdlib Require Import Reals List Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix interval.
From mathcomp Require Import boolp classical_sets functions reals Rstruct.
From mathcomp Require Import topology normedtype derive Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import SoftDefinitions GaussianCovarianceSums PaperMainDefinitions
  PaperMainGeometryPsd PaperMainGeometryGram PaperMainGeometryHomogeneous
  PaperMainGeometrySeparation PaperMainGordonProcessCovariance PaperMainGordonNets
  PaperMainGordonEntropy PaperMainGeometryHeadFrobenius
  PaperMainGeometryHeadCoefficients PaperMainConeConditionOperator
  PaperMainSymmetricBilinear.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OperatorNet.
Variable n : nat.
Local Notation N := (S n).
Implicit Types (Z : 'M[R]_N) (u w x y : 'cV[R]_N).

(* List coordinates of a public column. *)
Definition pmon_coords x : nat -> R := fun i => x (inord i) 0.

Lemma pmon_column_coords x : paper_main_symmetric_column n (pmon_coords x) = x.
Proof. by apply/matrixP => i j; rewrite mxE /pmon_coords inord_val [j]ord1. Qed.

Lemma pmon_coords_dot x :
  paper_main_gordon_dot N (pmon_coords x) (pmon_coords x) = (x^T *m x) 0 0.
Proof. by rewrite -paper_main_symmetric_column_norm pmon_column_coords. Qed.

Lemma pmon_column_sub (f g : nat -> R) :
  paper_main_symmetric_column n (fun i => Rminus (f i) (g i)) =
  paper_main_symmetric_column n f - paper_main_symmetric_column n g.
Proof. by apply/matrixP => i j; rewrite !mxE RminusE. Qed.

(* The first basis vector, a public unit column. *)
Definition pmon_e0 : 'cV[R]_N := delta_mx 0 0.

Lemma pmon_e0_unit : (pmon_e0^T *m pmon_e0) 0 0 = 1.
Proof. by rewrite /pmon_e0 trmx_delta mul_delta_mx mxE !eqxx. Qed.

(* The net covers public unit columns; its points are public unit columns. *)
Lemma pmon_net_cover (v : nat -> nat -> R) (s : nat) (eps : R) x :
  paper_main_gordon_finite_net N (fun f => paper_main_gordon_dot N f f = 1)
    v (List.seq 0 s) eps ->
  (x^T *m x) 0 0 = 1 ->
  exists t, (t < s)%N /\
    ((x - paper_main_symmetric_column n (v t))^T *m
     (x - paper_main_symmetric_column n (v t))) 0 0 <= eps ^+ 2.
Proof.
move=> [_ Hcov] Hx.
have [t [Ht Hd]] := Hcov (pmon_coords x) (etrans (pmon_coords_dot x) Hx).
exists t; split; first by apply/ssrnat.ltP; apply List.in_seq in Ht; lia.
rewrite -(pmon_column_coords x) -pmon_column_sub paper_main_symmetric_column_norm.
by apply/RleP; rewrite -RpowE.
Qed.

Lemma pmon_net_unit (v : nat -> nat -> R) (s : nat) (eps : R) t :
  paper_main_gordon_finite_net N (fun f => paper_main_gordon_dot N f f = 1)
    v (List.seq 0 s) eps ->
  (t < s)%N ->
  ((paper_main_symmetric_column n (v t))^T *m paper_main_symmetric_column n (v t)) 0 0 = 1.
Proof.
move=> [Hin _] Ht; rewrite paper_main_symmetric_column_norm.
by apply: Hin; apply/List.in_seq; split; [lia | move/ssrnat.ltP: Ht; lia].
Qed.

(* The bilinear form is bounded by the Frobenius norm. *)
Lemma pmon_bilinear_frobenius Z x y :
  `|(x^T *m Z *m y) 0 0| <=
  paper_main_frobenius Z * Num.sqrt ((x^T *m x) 0 0) * Num.sqrt ((y^T *m y) 0 0).
Proof.
rewrite -pmsb_pairing_outer -mulrA.
apply: le_trans (pmh_pairing_frobenius_bound _ _ _) _.
rewrite /paper_main_frobenius pmsb_pairing_outer_outer.
by rewrite (sqrtrM _ (pmh_vec_sqr_ge0 _ x)).
Qed.

(* The operator supremum over unit columns. *)
Definition pmon_values Z : set R :=
  [set r | exists u w, (u^T *m u) 0 0 = 1 /\ (w^T *m w) 0 0 = 1 /\
     r = `|(u^T *m Z *m w) 0 0|].

Definition paper_main_symmetric_operator_sup Z : R := sup (pmon_values Z).

Lemma pmon_values_nonempty Z : pmon_values Z !=set0.
Proof.
exists `|(pmon_e0^T *m Z *m pmon_e0) 0 0|.
by exists pmon_e0, pmon_e0; split; [exact: pmon_e0_unit | split; [exact: pmon_e0_unit | done]].
Qed.

Lemma pmon_values_ubound Z : ubound (pmon_values Z) (paper_main_frobenius Z).
Proof.
move=> _ [u [w [Hu [Hw ->]]]].
by have := pmon_bilinear_frobenius Z u w; rewrite Hu Hw sqrtr1 !mulr1.
Qed.

Lemma pmon_sup_ge Z u w :
  (u^T *m u) 0 0 = 1 -> (w^T *m w) 0 0 = 1 ->
  `|(u^T *m Z *m w) 0 0| <= paper_main_symmetric_operator_sup Z.
Proof.
move=> Hu Hw; apply: (ub_le_sup (ex_intro _ _ (pmon_values_ubound Z))).
by exists u, w; split; [done | split].
Qed.

Lemma pmon_sup_ge0 Z : 0 <= paper_main_symmetric_operator_sup Z.
Proof. exact: le_trans (normr_ge0 _) (pmon_sup_ge Z _ _ pmon_e0_unit pmon_e0_unit). Qed.

Lemma pmon_bilinear_scale Z (a c : R) x y :
  ((a *: x)^T *m Z *m (c *: y)) 0 0 = a * c * (x^T *m Z *m y) 0 0.
Proof. by rewrite [(_ *: _)^T]linearZ /= -!scalemxAl -scalemxAr scalerA mxE. Qed.

(* Homogeneity: |x^T Z y| <= M |x| |y| for all x, y, zero included. *)
Theorem pmon_homogeneous Z x y :
  `|(x^T *m Z *m y) 0 0| <=
  paper_main_symmetric_operator_sup Z * Num.sqrt ((x^T *m x) 0 0) *
  Num.sqrt ((y^T *m y) 0 0).
Proof.
have HM := pmon_sup_ge0 Z.
have Hr : 0 <= paper_main_symmetric_operator_sup Z * Num.sqrt ((x^T *m x) 0 0) *
    Num.sqrt ((y^T *m y) 0 0).
  by apply: mulr_ge0; [apply: mulr_ge0 |]; rewrite ?sqrtr_ge0.
have [Hx0|Hx] := eqVneq x 0.
  by move: Hr; rewrite Hx0 trmx0 !mul0mx mxE normr0.
have [Hy0|Hy] := eqVneq y 0.
  by move: Hr; rewrite Hy0 !mulmx0 [X in `|X|]mxE normr0.
have Hxp := pms_sqnorm_gt0 _ _ Hx.
have Hyp := pms_sqnorm_gt0 _ _ Hy.
set a := Num.sqrt ((x^T *m x) 0 0).
set c := Num.sqrt ((y^T *m y) 0 0).
have Ha : 0 < a by rewrite /a sqrtr_gt0.
have Hc : 0 < c by rewrite /c sqrtr_gt0.
have Ha0 : a != 0 by exact: lt0r_neq0.
have Hc0 : c != 0 by exact: lt0r_neq0.
have Ha2 : a ^+ 2 = (x^T *m x) 0 0 by rewrite /a (sqr_sqrtr (ltW Hxp)).
have Hc2 : c ^+ 2 = (y^T *m y) 0 0 by rewrite /c (sqr_sqrtr (ltW Hyp)).
have Hux : ((a^-1 *: x)^T *m (a^-1 *: x)) 0 0 = 1.
  rewrite [(_ *: _)^T]linearZ /= -scalemxAl -scalemxAr scalerA mxE -Ha2.
  by rewrite -expr2 -exprMn (mulVf Ha0) expr1n.
have Huy : ((c^-1 *: y)^T *m (c^-1 *: y)) 0 0 = 1.
  rewrite [(_ *: _)^T]linearZ /= -scalemxAl -scalemxAr scalerA mxE -Hc2.
  by rewrite -expr2 -exprMn (mulVf Hc0) expr1n.
have H := pmon_sup_ge Z _ _ Hux Huy.
have Hac0 : 0 <= a^-1 * c^-1 by apply: mulr_ge0; rewrite invr_ge0 ltW.
rewrite pmon_bilinear_scale normrM (ger0_norm Hac0) in H.
rewrite -mulrA -(ler_pdivrMr _ _ (mulr_gt0 Ha Hc)) invfM mulrC.
exact: H.
Qed.

Lemma pmon_bilinear_sub_l Z x x' y :
  ((x - x')^T *m Z *m y) 0 0 = (x^T *m Z *m y) 0 0 - (x'^T *m Z *m y) 0 0.
Proof. by rewrite -!pmsb_pairing_outer mulmxBl pmh_pairingBr. Qed.

Lemma pmon_bilinear_sub_r Z x y y' :
  (x^T *m Z *m (y - y')) 0 0 = (x^T *m Z *m y) 0 0 - (x^T *m Z *m y') 0 0.
Proof.
by rewrite -!pmsb_pairing_outer [(y - y')^T]linearB /= mulmxBr pmh_pairingBr.
Qed.

(* The discretization: net pairs bounded by b give the operator bound beta
   with beta (1 - 2 eps) = b. *)
Theorem paper_main_symmetric_operator_net_bound Z (v : nat -> nat -> R) (s : nat)
    (eps b beta : R) :
  0 <= eps -> 2 * eps < 1 -> beta * (1 - 2 * eps) = b ->
  paper_main_gordon_finite_net N (fun f => paper_main_gordon_dot N f f = 1)
    v (List.seq 0 s) eps ->
  (forall t t', (t < s)%N -> (t' < s)%N ->
     `|((paper_main_symmetric_column n (v t))^T *m Z *m
        paper_main_symmetric_column n (v t')) 0 0| <= b) ->
  paper_main_cone_opnorm_le Z beta.
Proof.
move=> He0 He1 Hbeta Hnet Hb.
have HM0 := pmon_sup_ge0 Z.
have Hall : forall u w, (u^T *m u) 0 0 = 1 -> (w^T *m w) 0 0 = 1 ->
    `|(u^T *m Z *m w) 0 0| <= b + 2 * eps * paper_main_symmetric_operator_sup Z.
  move=> u w Hu Hw.
  have [t [Ht Hdt]] := pmon_net_cover _ _ _ _ Hnet Hu.
  have [t' [Ht' Hdt']] := pmon_net_cover _ _ _ _ Hnet Hw.
  have Hut := pmon_net_unit _ _ _ _ Hnet Ht.
  have H1 := Hb t t' Ht Ht'.
  move: (paper_main_symmetric_column n (v t)) (paper_main_symmetric_column n (v t'))
    Hdt Hdt' Hut H1 => ut wt Hdt Hdt' Hut H1.
  have E : (u^T *m Z *m w) 0 0 =
      (ut^T *m Z *m wt) 0 0 + ((u - ut)^T *m Z *m w) 0 0 + (ut^T *m Z *m (w - wt)) 0 0.
    by rewrite pmon_bilinear_sub_l pmon_bilinear_sub_r; ring.
  have H2 := pmon_homogeneous Z (u - ut) w.
  have H3 := pmon_homogeneous Z ut (w - wt).
  rewrite Hw sqrtr1 mulr1 in H2.
  rewrite Hut sqrtr1 mulr1 in H3.
  have Hs1 : Num.sqrt (((u - ut)^T *m (u - ut)) 0 0) <= eps.
    by rewrite -(ger0_norm He0) -sqrtr_sqr; exact: ler_wsqrtr.
  have Hs2 : Num.sqrt (((w - wt)^T *m (w - wt)) 0 0) <= eps.
    by rewrite -(ger0_norm He0) -sqrtr_sqr; exact: ler_wsqrtr.
  have H2' := ler_wpM2l HM0 Hs1.
  have H3' := ler_wpM2l HM0 Hs2.
  rewrite E; apply: le_trans (ler_normD _ _) _.
  apply: le_trans (lerD (ler_normD _ _) (lexx _)) _.
  lra.
have HMle : paper_main_symmetric_operator_sup Z <=
    b + 2 * eps * paper_main_symmetric_operator_sup Z.
  apply: ge_sup; first exact: pmon_values_nonempty.
  by move=> _ [u [w [Hu [Hw ->]]]]; exact: Hall.
have Hpos : 0 < 1 - 2 * eps by rewrite subr_gt0.
have HMb : paper_main_symmetric_operator_sup Z <= beta.
  have H : paper_main_symmetric_operator_sup Z * (1 - 2 * eps) <= beta * (1 - 2 * eps).
    by rewrite Hbeta; lra.
  by rewrite (ler_pM2r Hpos) in H.
have Hbeta0 : 0 <= beta by exact: le_trans HM0 HMb.
move=> x y.
have H := pmon_homogeneous Z x y.
have Hx := pmh_vec_sqr_ge0 _ x.
have Hy := pmh_vec_sqr_ge0 _ y.
have Ha := sqrtr_ge0 ((x^T *m x) 0 0).
have Hc := sqrtr_ge0 ((y^T *m y) 0 0).
have Ha2 := sqr_sqrtr Hx.
have Hc2 := sqr_sqrtr Hy.
have Hq : `|(x^T *m Z *m y) 0 0| <=
    beta * Num.sqrt ((x^T *m x) 0 0) * Num.sqrt ((y^T *m y) 0 0).
  have Hac := mulr_ge0 Ha Hc.
  apply: le_trans H _; rewrite -!mulrA; exact: (ler_wpM2r Hac HMb).
rewrite -(real_normK (num_real ((x^T *m Z *m y) 0 0))) -Ha2 -Hc2.
have Hn := normr_ge0 ((x^T *m Z *m y) 0 0).
move: Hq Hn Ha Hc Hbeta0.
move: `|(x^T *m Z *m y) 0 0| (Num.sqrt ((x^T *m x) 0 0)) (Num.sqrt ((y^T *m y) 0 0)) => p q r.
move=> Hq Hn Hq0 Hr0 Hbeta0.
nra.
Qed.

(* The finite-pair witness when the operator bound fails. *)
Theorem paper_main_symmetric_operator_net_witness Z (v : nat -> nat -> R) (s : nat)
    (eps b beta : R) :
  0 <= eps -> 2 * eps < 1 -> beta * (1 - 2 * eps) = b ->
  paper_main_gordon_finite_net N (fun f => paper_main_gordon_dot N f f = 1)
    v (List.seq 0 s) eps ->
  ~ paper_main_cone_opnorm_le Z beta ->
  exists t t', [/\ (t < s)%N, (t' < s)%N &
    b < `|((paper_main_symmetric_column n (v t))^T *m Z *m
           paper_main_symmetric_column n (v t')) 0 0|].
Proof.
move=> He0 He1 Hbeta Hnet Hnot.
apply: contrapT => Hno; apply: Hnot.
apply: (paper_main_symmetric_operator_net_bound Z v s eps b beta He0 He1 Hbeta Hnet).
move=> t t' Ht Ht'; rewrite leNgt; apply/negP => Hlt; apply: Hno.
by exists t, t'; split.
Qed.

(* Fixed contained nets, independent of Z, with the entropy bound. *)
Theorem paper_main_symmetric_operator_net_exists (eps : R) :
  0 < eps ->
  let s := List.length (paper_main_gordon_entropy_grid N eps) in
  (0 < s)%N /\ exists v : nat -> nat -> R,
    paper_main_gordon_finite_net N (fun f => paper_main_gordon_dot N f f = 1)
      v (List.seq 0 s) eps /\
    ln (INR s) <= paper_main_gordon_entropy_constant eps * INR N.
Proof.
move=> He s.
have Hne : exists f, paper_main_gordon_dot N f f = 1.
  by exists (pmon_coords pmon_e0); rewrite pmon_coords_dot; exact: pmon_e0_unit.
have He' : Rlt 0 eps by apply/RltP.
have [Hs [v [Hnet Hln]]] := paper_main_gordon_entropy_net_fixed N
  (fun f => paper_main_gordon_dot N f f = 1) eps He' Hne (fun f Hf => Hf).
split; first by apply/ssrnat.ltP.
by exists v; split => //; apply/RleP; rewrite -RmultE.
Qed.

(* The entropy constant at eps = 1/4: (4 + 16) ln 2 = 20 ln 2. *)
Lemma paper_main_symmetric_operator_entropy_quarter (eps : R) :
  eps * 4%:R = 1 ->
  paper_main_gordon_entropy_constant eps = 20%:R * ln 2%:R.
Proof.
move=> He.
have H4 : (4%:R : R) != 0 by rewrite pnatr_eq0.
have Hinv : eps^-1 = 4%:R by rewrite -[eps](mulfK H4) He mul1r invrK.
have I4 : IZR 4 = 4%:R :> R by rewrite -INRE INR_IZR_INZ.
have I2 : IZR 2 = 2%:R :> R by rewrite -INRE INR_IZR_INZ.
rewrite /paper_main_gordon_entropy_constant RmultE RplusE RdivE I4 I2 Hinv.
by rewrite -natrM -natrD.
Qed.

(* The eps = 1/4 package: one fixed net, independent of Z, with
   ln s <= 20 ln 2 N; net pairs bounded by b give the operator bound
   beta = 2 b, and a failure of that bound gives a net pair above b. *)
Corollary paper_main_symmetric_operator_net_quarter (eps : R) :
  eps * 4%:R = 1 ->
  let s := List.length (paper_main_gordon_entropy_grid N eps) in
  (0 < s)%N /\ exists v : nat -> nat -> R,
    [/\ forall t, (t < s)%N -> paper_main_gordon_dot N (v t) (v t) = 1,
      ln (INR s) <= 20%:R * ln 2%:R * INR N,
      forall Z (b beta : R), beta = 2%:R * b ->
        (forall t t', (t < s)%N -> (t' < s)%N ->
           `|((paper_main_symmetric_column n (v t))^T *m Z *m
              paper_main_symmetric_column n (v t')) 0 0| <= b) ->
        paper_main_cone_opnorm_le Z beta &
      forall Z (b beta : R), beta = 2%:R * b ->
        ~ paper_main_cone_opnorm_le Z beta ->
        exists t t', [/\ (t < s)%N, (t' < s)%N &
          b < `|((paper_main_symmetric_column n (v t))^T *m Z *m
                 paper_main_symmetric_column n (v t')) 0 0|]].
Proof.
move=> He s.
have He0 : 0 < eps by lra.
have He1 : 2 * eps < 1 by lra.
have Hbb : forall b beta : R, beta = 2%:R * b -> beta * (1 - 2 * eps) = b.
  move=> b beta ->.
  transitivity (2%:R * b - b * (eps * 4%:R)); first by ring.
  by rewrite He; ring.
have [Hs [v [Hnet Hln]]] := paper_main_symmetric_operator_net_exists eps He0.
split => //; exists v; split.
- move=> t Ht; have := pmon_net_unit _ _ _ _ Hnet Ht.
  by rewrite paper_main_symmetric_column_norm.
- by rewrite -(paper_main_symmetric_operator_entropy_quarter eps He).
- move=> Z b beta Hbeta.
  exact: (paper_main_symmetric_operator_net_bound Z v s eps b beta (ltW He0) He1 (Hbb _ _ Hbeta) Hnet).
- move=> Z b beta Hbeta.
  exact: (paper_main_symmetric_operator_net_witness Z v s eps b beta (ltW He0) He1 (Hbb _ _ Hbeta) Hnet).
Qed.

(* The same package with Stdlib operators, in the form of the hypotheses of
   the Stdlib Gaussian net tail: Nat.lt indices, the Stdlib unit condition,
   Rle (ln s) (20 ln 2 N), and the witness b <= |u_i^T Z u_j|. *)
Corollary paper_main_symmetric_operator_net_quarter_stdlib :
  exists (s : nat) (v : nat -> nat -> R),
    [/\ Nat.lt 0 s,
      forall i, Nat.lt i s -> paper_main_gordon_dot N (v i) (v i) = IZR 1,
      Rle (ln (INR s)) (Rmult (Rmult 20 (ln 2)) (INR N)) &
      forall Z (b beta : R), beta = Rmult 2 b ->
        ~ paper_main_cone_opnorm_le Z beta ->
        exists i j, [/\ Nat.lt i s, Nat.lt j s &
          Rle b (Rabs (((paper_main_symmetric_column n (v i))^T *m Z *m
            paper_main_symmetric_column n (v j)) ord0 ord0))]].
Proof.
have He : (4%:R : R)^-1 * 4%:R = 1 by rewrite mulVf // pnatr_eq0.
have [Hs [v [Hunit Hln Hbd Hwit]]] := paper_main_symmetric_operator_net_quarter _ He.
exists (List.length (paper_main_gordon_entropy_grid N (4%:R)^-1)), v; split.
- exact/ssrnat.ltP.
- by move=> i Hi; apply: Hunit; apply/ssrnat.ltP.
- have I20 : IZR 20 = 20%:R :> R by rewrite -INRE INR_IZR_INZ.
  have I2 : IZR 2 = 2%:R :> R by rewrite -INRE INR_IZR_INZ.
  by apply/RleP; rewrite !RmultE I20 I2.
- move=> Z b beta Hbeta Hnot.
  have I2 : IZR 2 = 2%:R :> R by rewrite -INRE INR_IZR_INZ.
  have Hbeta' : beta = 2%:R * b by rewrite Hbeta RmultE I2.
  have [i [j [Hi Hj Hij]]] := Hwit Z b beta Hbeta' Hnot.
  exists i, j; split; [exact/ssrnat.ltP | exact/ssrnat.ltP |].
  by apply/RleP; rewrite RabsE; exact: ltW.
Qed.

End OperatorNet.
