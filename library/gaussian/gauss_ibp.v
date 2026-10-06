From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat fingroup perm ssralg ssrnum matrix.
From mathcomp Require Import archimedean arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions cardinality reals ereal.
From mathcomp Require Import interval interval_inference topology normedtype.
From mathcomp Require Import sequences derive realfun exp numfun measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure.
From mathcomp Require Import measurable_realfun lebesgue_integral ftc probability.
From GaussianAnalysis Require Import measurable_matrix normal_integral gauss.

(**md**************************************************************************)
(* # Gaussian integration by parts                                            *)
(*                                                                            *)
(* Stein's identity for the standard normal law, E[X f(X)] = E[f'(X)]         *)
(* (normal_ibp), and its version in several dimensions for gauss n,           *)
(* E[x_i F(x)] = E[d_i F(x)] (gauss_ibp), for functions of class C^1 of       *)
(* polynomial growth. gauss_ibp_line asks less: F and d_i F measurable, and   *)
(* d_i F continuous along the lines parallel to the i-th axis. A partial      *)
(* derivative of a continuous function is measurable (measurable_derive_rV),  *)
(* so the identity of order two, E[(x_i^2 - 1) F(x)] = E[d_i d_i F(x)]        *)
(* (gauss_ibp2), holds for F and d_i d_i F continuous, without the            *)
(* continuity of d_i F.                                                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section integral_nondecreasing_set.
Context {d : measure_display} {T : measurableType d} {R : realType}.
Variables (mu : {measure set T -> \bar R}) (F : (set T)^nat) (g : T -> \bar R).
Hypotheses (ndF : nondecreasing_seq F) (mF : forall i, measurable (F i)).
Hypothesis gi : mu.-integrable (\bigcup_i F i) g.

Lemma integrable_nondecreasing_set_cvg_integral :
  (\int[mu]_(x in F i) g x @[i --> \oo] --> \int[mu]_(x in \bigcup_i F i) g x)%E.
Proof.
have mU : measurable (\bigcup_i F i) by exact: bigcupT_measurable.
have mg := measurable_int _ gi.
have mgi i : measurable_fun (F i) g.
  by apply: measurable_funS mg => //; exact: bigcup_sup.
have cp := @ge0_nondecreasing_set_cvg_integral _ _ _ F (g^\+)%E mu ndF mF
  (fun i => measurable_funepos (mgi i)) (fun i x _ => funepos_ge0 g x).
have cn := @ge0_nondecreasing_set_cvg_integral _ _ _ F (g^\-)%E mu ndF mF
  (fun i => measurable_funeneg (mgi i)) (fun i x _ => funeneg_ge0 g x).
have gpfin : (\int[mu]_(x in \bigcup_i F i) g^\+ x)%E \is a fin_num.
  by apply: integrable_fin_num => //; exact: integrable_funepos.
have gnfin : (\int[mu]_(x in \bigcup_i F i) g^\- x)%E \is a fin_num.
  by apply: integrable_fin_num => //; exact: integrable_funeneg.
have def : (\int[mu]_(x in \bigcup_i F i) g^\+ x +?
    - (\int[mu]_(x in \bigcup_i F i) g^\- x))%E.
  by rewrite fin_num_adde_defl// fin_numN.
have := cvgeB _ cp cn; rewrite -integralE => /(_ _ def) h.
apply: cvg_trans h; apply: near_eq_cvg; apply: nearW => i.
by rewrite /= [RHS]integralE.
Qed.

End integral_nondecreasing_set.

(* A finite sum of continuous functions is continuous. *)
Section continuous_sum.
Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.

Lemma continuous_sum (I : Type) (s : seq I) (f : I -> T -> V) :
  (forall i, continuous (f i)) -> continuous (fun x => \sum_(i <- s) f i x).
Proof.
move=> cf x; elim: s => [|i s IH].
  by under eq_fun do rewrite big_nil; exact: cvg_cst.
by under eq_fun do rewrite big_cons; exact: (continuousD (cf i x) IH).
Qed.

End continuous_sum.

Section normal_ibp.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Notation mu := (@lebesgue_measure R).
Local Notation phi := (normal_pdf (0 : R) 1).

Lemma is_derive_normal_pdf01 (x : R) : is_derive x 1 phi (- x * phi x).
Proof.
rewrite normal_pdfE ?oner_neq0//=.
have dg : is_derive x 1 (fun z : R => - (z - 0) ^+ 2 / (1 ^+ 2 *+ 2)) (- x).
  have hsq : is_derive x 1 (@GRing.exp R ^~ 2) (2%:R *: x ^+ 1 *: 1).
    by apply: DeriveDef; [exact: exprn_derivable|exact: exp_derive].
  have -> : (fun z : R => - (z - 0) ^+ 2 / (1 ^+ 2 *+ 2)) =
      (- 2^-1) \*: (@GRing.exp R ^~ 2).
    by apply/funext => z; rewrite /= subr0 expr1n /GRing.scale /=; lra.
  apply: (is_derive_eq (is_deriveZ (- 2^-1) hsq)).
  by rewrite expr1 /GRing.scale /=; lra.
have he := is_derive1_comp (is_derive_expR _) dg.
apply: (is_derive_eq (is_deriveZ (normal_peak (1 : R)) he)).
by rewrite /normal_fun /GRing.scale /=; lra.
Qed.

Lemma normal_pdf01E (x : R) : phi x = normal_peak 1 * expR (- x ^+ 2 / 2).
Proof.
by rewrite normal_pdfE ?oner_neq0//= /normal_fun subr0 expr1n.
Qed.

Lemma normal_pdf01N (x : R) : phi (- x) = phi x.
Proof. by rewrite !normal_pdf01E sqrrN. Qed.

Lemma cvgn_poly_normal_pdf01 (C : R) k : 0 <= C ->
  C * (1 + n%:R ^+ k) * phi n%:R @[n --> \oo] --> 0.
Proof.
move=> C0.
pose K := C * normal_peak (1 : R) * (1 + (k`! * 4 ^ k)%:R).
have K0 : 0 <= K by rewrite /K !mulr_ge0// ?normal_peak_ge0//; lra.
apply: (@squeeze_cvgr _ _ _ _ (cst 0) (fun n => K * expR (- n%:R))); last 2 first.
- exact: cvg_cst.
- rewrite -[X in _ --> X](mulr0 K).
  by apply: cvgM; [exact: cvg_cst|exact: cvgn_expR].
near=> n.
have n4 : (4 <= n)%N by near: n; exists 4%N.
set y := n%:R.
have y4 : 4 <= y :> R by rewrite /y (ler_nat R 4 n).
have y0 : 0 <= y by lra.
have pk : 0 < normal_peak (1 : R) by rewrite normal_peak_gt0 ?oner_neq0.
have c1 : 0 <= (k`! * 4 ^ k)%:R :> R by [].
have e1 : y ^+ k <= (k`! * 4 ^ k)%:R * expR (y ^+ 2 / 4).
  by have := exprn_le_expR y k; rewrite ger0_norm.
have e2 : 1 <= expR (y ^+ 2 / 4) by rewrite -expR0 ler_expR divr_ge0// sqr_ge0.
have e3 : expR (y ^+ 2 / 4) * expR (- y ^+ 2 / 2) = expR (- y ^+ 2 / 4).
  by rewrite -expRD; congr expR; lra.
have e4 : expR (- y ^+ 2 / 4) <= expR (- y) by rewrite ler_expR; nra.
have E2 := expR_gt0 (- y ^+ 2 / 2); have E4 := expR_gt0 (y ^+ 2 / 4).
have yk := exprn_ge0 k y0.
have h : (1 + y ^+ k) * expR (- y ^+ 2 / 2) <=
    (1 + (k`! * 4 ^ k)%:R) * expR (- y) by nra.
apply/andP; split.
  by rewrite /cst mulr_ge0 ?normal_pdf_ge0// mulr_ge0//; lra.
by rewrite normal_pdf01E /K -!mulrA ler_wpM2l// mulrCA ler_wpM2l// ?ltW.
Unshelve. all: by end_near.
Qed.

Lemma normal_ibp (f f' : R -> R) (C : R) (k : nat) :
  (forall x : R, is_derive x 1 f (f' x)) -> continuous f' ->
  (forall x, `|f x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|f' x| <= C * (1 + `|x| ^+ k)) ->
  (\int[N]_x (x * f x)%:E = \int[N]_x (f' x)%:E)%E.
Proof.
move=> df cf' fC f'C.
have C0 : 0 <= C.
  have := fC 0; rewrite normr0 expr0n => h; have := normr_ge0 (f 0).
  by case: (k == 0%N) h => /= h; nra.
have cf : continuous f.
  move=> x; apply: differentiable_continuous; apply/derivable1_diffP.
  by have [] := df x.
have mf : measurable_fun [set: R] f by exact: continuous_measurable_fun.
have mf' : measurable_fun [set: R] f' by exact: continuous_measurable_fun.
have xfC x : `|x * f x| <= (2 * C) * (1 + `|x| ^+ k.+1).
  rewrite normrM exprS; have hb := fC x; have a0 := normr_ge0 x.
  have p0 := exprn_ge0 k a0; have b0 := normr_ge0 (f x).
  have h1 : `|x| * `|f x| <= C * (`|x| + `|x| * `|x| ^+ k).
    by have := ler_wpM2l a0 hb; nra.
  have h2 : `|x| <= 1 + `|x| * `|x| ^+ k.
    case: (leP `|x| 1) => x1; first by nra.
    have : 1 <= `|x| ^+ k by rewrite exprn_ege1// ltW.
    nra.
  nra.
have mxf : measurable_fun [set: R] (fun x => x * f x) by apply: measurable_funM.
have Ixf := integrable_normal_poly mxf xfC.
have If' := integrable_normal_poly mf' f'C.
rewrite !integral_normal_prob//.
have mphi : measurable_fun [set: R] (fun x => (phi x)%:E).
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
have Lxf : mu.-integrable [set: R] (fun x => ((x * f x) * phi x)%:E).
  under eq_fun do rewrite EFinM.
  by apply/(integrable_normal_prob _ _ _).1 => //; exact/measurable_EFinP.
have Lf' : mu.-integrable [set: R] (fun x => (f' x * phi x)%:E).
  under eq_fun do rewrite EFinM.
  by apply/(integrable_normal_prob _ _ _).1 => //; exact/measurable_EFinP.
under eq_integral do rewrite -EFinM.
under [RHS]eq_integral do rewrite -EFinM.
suff g0 : (\int[mu]_x ((f' x - x * f x) * phi x)%:E = 0)%E.
  have fa := integrable_fin_num measurableT Lf'.
  have fb := integrable_fin_num measurableT Lxf.
  have : (\int[mu]_x (f' x * phi x)%:E - \int[mu]_x (x * f x * phi x)%:E = 0)%E.
    rewrite -integralB//; rewrite -[RHS]g0; apply: eq_integral => x _.
    by rewrite -EFinB mulrBl.
  move: fa fb; set a := (\int[mu]_x _)%E; set b := (\int[mu]_x _)%E.
  clearbody a b; case: a => // a; case: b => // b _ _ /= /eqP.
  by rewrite -EFinB eqe subr_eq0 => /eqP ->.
(* g = (f phi)' is integrable on the line, and the integral of g over
   [-(n+1), n+1] is G (n+1) - G (-(n+1)), which tends to 0. *)
pose g x := (f' x - x * f x) * phi x.
pose G x := f x * phi x.
have Lg : mu.-integrable [set: R] (fun x => (g x)%:E).
  refine (eq_integrable measurableT _ _ _ (integrableB measurableT Lf' Lxf)).
  by move=> x _; rewrite /g /= -EFinB mulrBl.
have dG (x : R) : is_derive x 1 G (g x).
  apply: (is_derive_eq (is_deriveM (df x) (is_derive_normal_pdf01 x))).
  by rewrite /g /GRing.scale /=; lra.
have cg : continuous g.
  move=> x; apply: cvgM; last exact: continuous_normal_pdf (oner_neq0 _) x.
  by apply: cvgB; [exact: cf'|apply: cvgM; [exact: cvg_id|exact: cf]].
have cG : continuous G.
  move=> x; apply: differentiable_continuous; apply/derivable1_diffP.
  exact: (@ex_derive _ _ _ _ _ _ _ (dG x)).
pose I (n : nat) : set R := `[- n.+1%:R, n.+1%:R]%classic.
have FTC (n : nat) : (\int[mu]_(x in I n) (g x)%:E =
    (G n.+1%:R)%:E - (G (- n.+1%:R))%:E)%E.
  apply: continuous_FTC2.
  - by rewrite gtrN ?ltr0n.
  - by apply: continuous_subspaceT => x; exact: cg.
  - split.
    + by move=> y _; exact: (@ex_derive _ _ _ _ _ _ _ (dG y)).
    + by apply: cvg_at_right_filter; exact: cG.
    + by apply: cvg_at_left_filter; exact: cG.
  - move=> y _; rewrite derive1E.
    exact: (@derive_val _ _ _ _ _ _ _ (dG y)).
have mI n : measurable (I n) by exact: measurable_itv.
have ndI : nondecreasing_seq I.
  move=> m n mn; apply/subsetPset => x; rewrite /I /= !in_itv /= => /andP[h1 h2].
  have : (m.+1%:R <= n.+1%:R :> R) by rewrite ler_nat.
  by move=> h; apply/andP; split; lra.
have UI : \bigcup_n I n = [set: R].
  apply/seteqP; split => // x _.
  exists (Num.truncn `|x|) => //; rewrite /I /= in_itv /=.
  have h1 := truncnS_gt `|x|; have h2 := ler_norm x.
  have := ler_norm (- x); rewrite normrN => h3.
  rewrite -[1 *- _]/(- ((Num.truncn `|x|).+1%:R)).
  by apply/andP; split; lra.
have Lg' : mu.-integrable (\bigcup_n I n) (fun x => (g x)%:E) by rewrite UI.
have hcvg := @integrable_nondecreasing_set_cvg_integral _ (measurableTypeR R) R mu
  I (fun x => (g x)%:E) ndI mI Lg'.
rewrite UI in hcvg.
have uS : C * (1 + n.+1%:R ^+ k) * phi n.+1%:R @[n --> \oo] --> (0 : R).
  have := cvgn_poly_normal_pdf01 k C0.
  by rewrite -(cvg_shiftS (fun n => C * (1 + n%:R ^+ k) * phi n%:R)).
have Gb (y : R) : 0 <= y ->
    `|G y| <= C * (1 + y ^+ k) * phi y /\ `|G (- y)| <= C * (1 + y ^+ k) * phi y.
  move=> y0; rewrite /G !normrM normal_pdf01N (ger0_norm (normal_pdf_ge0 _ _ _)).
  split; apply: ler_wpM2r; rewrite ?normal_pdf_ge0//.
    by have := fC y; rewrite (ger0_norm y0).
  by have := fC (- y); rewrite normrN (ger0_norm y0).
have uSN : - (C * (1 + n.+1%:R ^+ k) * phi n.+1%:R) @[n --> \oo] --> (0 : R).
  by apply: (cvg_trans (cvgN uS)); rewrite oppr0; exact: cvg_id.
have Gp : G n.+1%:R @[n --> \oo] --> 0.
  apply: (squeeze_cvgr _ uSN uS).
  by apply: nearW => n; have [+ _] := Gb n.+1%:R (ler0n _ _); rewrite ler_norml.
have Gm : G (- n.+1%:R) @[n --> \oo] --> 0.
  apply: (squeeze_cvgr _ uSN uS).
  by apply: nearW => n; have [_ +] := Gb n.+1%:R (ler0n _ _); rewrite ler_norml.
have E0 : ((G n.+1%:R)%:E - (G (- n.+1%:R))%:E)%E @[n --> \oo] --> (0 : \bar R).
  apply/fine_cvgP; split; first by apply: nearW => n; rewrite -EFinB.
  by rewrite -(subr0 0); exact: (cvgB Gp Gm).
have E1 : ((G n.+1%:R)%:E - (G (- n.+1%:R))%:E)%E @[n --> \oo] -->
    (\int[mu]_x (g x)%:E)%E.
  apply: cvg_trans hcvg; apply: near_eq_cvg; apply: nearW => n /=.
  by rewrite FTC.
exact: (cvg_unique _ E1 E0).
Qed.

End normal_ibp.

Section is_derive_transfer.
Context {R : realType} {V V' W : normedModType R}.

(* Two functions with the same difference quotients have the same
   directional derivative. *)
Lemma is_derive_transfer (F : V -> W) (G : V' -> W) a v b w (d : W) :
  (forall h : R, F (h *: v + a) = G (h *: w + b)) ->
  is_derive b w G d -> is_derive a v F d.
Proof.
move=> FG [dG DG].
have Fa : F a = G b by have := FG 0; rewrite !scale0r !add0r.
have Q : (fun h : R => h^-1 *: ((F \o shift a) (h *: v) - F a)) =
    (fun h : R => h^-1 *: ((G \o shift b) (h *: w) - G b)).
  by apply/funext => h; rewrite /= FG Fa.
apply: DeriveDef; first by rewrite /derivable Q.
by rewrite -DG /derive Q.
Qed.

End is_derive_transfer.

Section gauss_ibp.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

Lemma rV_consD m (t h : R) (v : 'rV[R]_m) :
  rV_cons (h * 1 + t, v) = h *: delta_mx 0 0 + rV_cons (t, v).
Proof.
apply/rowP => j.
have -> : (h *: delta_mx 0 0 + rV_cons (t, v)) 0 j =
    h * (j == 0)%:R + rV_cons (t, v) 0 j.
  rewrite mxE; congr (_ + _); rewrite mxE mxE eqxx /=.
  by rewrite (_ : (j == 0) = (j == ord0)).
case: (unliftP ord0 j) => [j' ->|->]; last by rewrite !rV_cons0 eqxx mulr1.
by rewrite !rV_consS (_ : (lift ord0 j' == 0) = false) ?mulr0 ?add0r//
  eq_sym (negbTE (neq_lift _ _)).
Qed.

Lemma mx_norm_entry_le m n (x : 'M[R]_(m, n)) i j : `|x i j| <= `|x|.
Proof.
have -> : `|x| = \big[maxr/0]_ij `|x ij.1 ij.2| by rewrite -mx_normrE.
exact: (le_bigmax _ _ (i, j)).
Qed.

(* The constant of a polynomial bound is nonnegative. *)
Lemma poly_bound_ge0 m (G : 'rV[R]_m -> R) (C : R) (k : nat) :
  (forall x, `|G x| <= C * (1 + `|x| ^+ k)) -> 0 <= C.
Proof.
move=> GC; have := GC 0; rewrite normr0 expr0n => h; have := normr_ge0 (G 0).
by case: (k == 0%N) h => /= h; nra.
Qed.

(* Multiplying by a coordinate raises the degree of a polynomial bound by
   one. *)
Lemma entry_mul_bound m (i : 'I_m) (G : 'rV[R]_m -> R) (C : R) (k : nat) :
  (forall x, `|G x| <= C * (1 + `|x| ^+ k)) ->
  forall x : 'rV[R]_m, `|x 0 i * G x| <= (2 * C) * (1 + `|x| ^+ k.+1).
Proof.
move=> GC x; have C0 := poly_bound_ge0 GC.
rewrite normrM exprS; have hb := GC x; have a0 := normr_ge0 x.
have ae := mx_norm_entry_le x 0 i; have e0 := normr_ge0 (x 0 i).
have p0 := exprn_ge0 k a0; have b0 := normr_ge0 (G x).
have h1 : `|x 0 i| * `|G x| <= C * (`|x| + `|x| * `|x| ^+ k).
  by have := ler_wpM2r b0 ae; have := ler_wpM2l a0 hb; nra.
have h2 : `|x| <= 1 + `|x| * `|x| ^+ k.
  case: (leP `|x| 1) => x1; first by nra.
  have : 1 <= `|x| ^+ k by rewrite exprn_ege1// ltW.
  nra.
nra.
Qed.

Lemma exprn1S_le (a : R) k : 0 <= a -> 1 + a ^+ k <= 2 * (1 + a ^+ k.+1).
Proof.
move=> a0; have e0 := exprn_ge0 k.+1 a0.
have [h|h] : 1 + a ^+ k <= 2 \/ 1 + a ^+ k <= 1 + a ^+ k.+1.
- case: (lerP a 1) => a1; [left|right].
    by rewrite -[2]/(1 + 1) lerD2l exprn_ile1.
  by rewrite lerD2l ler_eXn2l.
- by apply: (le_trans h); rewrite -[X in X <= _]mulr1 ler_pM2l // lerDl.
- by apply: (le_trans h); rewrite ler_peMl ?addr_ge0 // ler1n.
Qed.

Lemma rV_cons_norm_exprn_le m (t : R) (v : 'rV[R]_m) k :
  `|rV_cons (t, v)| ^+ k <= `|t| ^+ k + `|v| ^+ k.
Proof.
have hn : `|rV_cons (t, v)| <= Num.max `|t| `|v|.
  have -> : `|rV_cons (t, v)| = \big[maxr/0]_ij `|rV_cons (t, v) ij.1 ij.2|.
    by rewrite -mx_normrE.
  apply: bigmax_le => [|[i j] _]; first by rewrite le_max normr_ge0.
  rewrite /= (ord1 i); case: (unliftP ord0 j) => [j' ->|->].
    by rewrite rV_consS le_max (mx_norm_entry_le v 0 j') orbT.
  by rewrite rV_cons0 le_max lexx.
have a0 := normr_ge0 t; have b0 := normr_ge0 v.
have hk : `|rV_cons (t, v)| ^+ k <= (Num.max `|t| `|v|) ^+ k.
  by rewrite lerXn2r// ?nnegrE// le_max a0.
apply: (le_trans hk); have ak := exprn_ge0 k a0; have bk := exprn_ge0 k b0.
by rewrite /Num.max; case: ifPn => _; lra.
Qed.

Lemma integral_gauss_cons21 m (f : 'rV[R]_m.+1 -> \bar R) :
  (gauss m.+1).-integrable [set: 'rV[R]_m.+1] f ->
  (\int[gauss m.+1]_x f x = \int[gauss m]_v \int[N]_t f (rV_cons (t, v)))%E.
Proof.
move=> fi; have mf := measurable_int _ fi.
have fci := (integrable_gauss_cons mf).1 fi.
rewrite [LHS](@integral_distribution _ _ _ _ _ (N \x gauss m)%E (@rV_cons R m))//.
by rewrite -(integral21_prod_meas1 fci).
Qed.

Lemma gauss_ibp0 m (F dF : 'rV[R]_m.+1 -> R) (C : R) (k : nat) :
  (forall x, is_derive x (delta_mx 0 0) F (dF x)) ->
  measurable_fun [set: 'rV[R]_m.+1] F -> measurable_fun [set: 'rV[R]_m.+1] dF ->
  (forall x, continuous (fun t : R => dF (t *: delta_mx 0 0 + x))) ->
  (forall x, `|F x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|dF x| <= C * (1 + `|x| ^+ k)) ->
  (\int[gauss m.+1]_x (x 0 0 * F x)%:E = \int[gauss m.+1]_x (dF x)%:E)%E.
Proof.
move=> dF_ mF mdF ldF FC dFC; have C0 := poly_bound_ge0 FC.
have mx0F : measurable_fun [set: 'rV[R]_m.+1] (fun x => x 0 0 * F x).
  by apply: measurable_funM => //; exact: measurable_mxentry.
have I1 := integrable_gauss_poly mx0F (entry_mul_bound 0 FC).
have I2 := integrable_gauss_poly mdF dFC.
rewrite (integral_gauss_cons21 I1) (integral_gauss_cons21 I2).
apply: eq_integral => v _.
have r0 (t : R) : rV_cons (t, v) 0 0 = t by exact: rV_cons0.
transitivity (\int[N]_t (t * F (rV_cons (t, v)))%:E)%E.
  by apply: eq_integral => t _; rewrite /= r0.
have rD (t h : R) : rV_cons (h *: 1 + t, v) = h *: delta_mx 0 0 + rV_cons (t, v).
  exact: rV_consD.
have rvE : (fun t : R => rV_cons (t, v)) =
    (fun t => t *: delta_mx 0 0 + rV_cons (0, v)).
  by apply/funext => t; rewrite -rD addr0 /GRing.scale /= mulr1.
have bnd (G : 'rV[R]_m.+1 -> R) : (forall x, `|G x| <= C * (1 + `|x| ^+ k)) ->
    forall t : R, `|G (rV_cons (t, v))| <= C * (1 + `|v| ^+ k) * (1 + `|t| ^+ k).
  move=> GC t; apply: (le_trans (GC _)).
  have := rV_cons_norm_exprn_le t v k; have := exprn_ge0 k (normr_ge0 t).
  have := exprn_ge0 k (normr_ge0 v) => vk tk hb.
  by have := mulr_ge0 (mulr_ge0 C0 tk) vk; nra.
transitivity (\int[N]_t (dF (rV_cons (t, v)))%:E)%E; last by [].
apply: (@normal_ibp R (fun t => F (rV_cons (t, v))) (fun t => dF (rV_cons (t, v)))
  (C * (1 + `|v| ^+ k)) k).
- move=> t; apply: (is_derive_transfer _ (dF_ (rV_cons (t, v)))).
  by move=> h; rewrite /= rD.
- have -> : (fun t => dF (rV_cons (t, v))) =
      (fun t => dF (t *: delta_mx 0 0 + rV_cons (0, v))).
    by apply/funext => t; rewrite (congr1 (fun f => f t) rvE).
  exact: ldF.
- exact: bnd.
- exact: bnd.
Qed.

Lemma mx_norm_col_perm_le m (s : 'S_m) (x : 'rV[R]_m) : `|col_perm s x| <= `|x|.
Proof.
have -> : `|col_perm s x| = \big[maxr/0]_ij `|col_perm s x ij.1 ij.2|.
  by rewrite -mx_normrE.
apply: bigmax_le => [|ij _]; first exact: normr_ge0.
by rewrite mxE; exact: mx_norm_entry_le.
Qed.

(* Integration by parts along the coordinate i, for F and its partial
   derivative dF measurable, dF continuous along the lines parallel to the
   i-th axis, both of polynomial growth. *)
Lemma gauss_ibp_line n (i : 'I_n) (F dF : 'rV[R]_n -> R) (C : R) (k : nat) :
  (forall x, is_derive x (delta_mx 0 i) F (dF x)) ->
  measurable_fun [set: 'rV[R]_n] F -> measurable_fun [set: 'rV[R]_n] dF ->
  (forall x, continuous (fun t : R => dF (t *: delta_mx 0 i + x))) ->
  (forall x, `|F x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|dF x| <= C * (1 + `|x| ^+ k)) ->
  (\int[gauss n]_x (x 0 i * F x)%:E = \int[gauss n]_x (dF x)%:E)%E.
Proof.
case: n i F dF => [[] //|m] i F dF dF_ mF mdF ldF FC dFC.
have C0 := poly_bound_ge0 FC.
(* Move the coordinate i first with the transposition s of 0 and i. *)
pose s := tperm (0 : 'I_m.+1) i.
have Pe (x : 'rV[R]_m.+1) j : col_perm s x 0 j = x 0 (s j) by rewrite mxE.
have PD (h : R) (x : 'rV[R]_m.+1) :
    col_perm s (h *: delta_mx 0 0 + x) = h *: delta_mx 0 i + col_perm s x.
  apply/rowP => j; rewrite !mxE /s eqxx /=; congr (h * _%:R + _).
  by rewrite -[X in _ == X](tpermR (0 : 'I_m.+1) i) (inj_eq (@perm_inj _ _)).
have mP : measurable_fun [set: 'rV[R]_m.+1] (col_perm s) := measurable_col_perm s.
have mxiF : measurable_fun [set: 'rV[R]_m.+1] (fun x => x 0 i * F x).
  by apply: measurable_funM => //; exact: measurable_mxentry.
have I1 := integrable_gauss_poly mxiF (entry_mul_bound i FC).
have I2 := integrable_gauss_poly mdF dFC.
rewrite -(integral_gauss_col_perm s I1) -(integral_gauss_col_perm s I2).
transitivity (\int[gauss m.+1]_x (x 0 0 * (F \o col_perm s) x)%:E)%E.
  by apply: eq_integral => x _; rewrite /= Pe /s tpermR.
transitivity (\int[gauss m.+1]_x ((dF \o col_perm s) x)%:E)%E; last by [].
have bP (G : 'rV[R]_m.+1 -> R) : (forall x, `|G x| <= C * (1 + `|x| ^+ k)) ->
    forall x, `|(G \o col_perm s) x| <= C * (1 + `|x| ^+ k).
  move=> GC x; apply: (le_trans (GC _)); rewrite ler_wpM2l// lerD2l.
  by rewrite lerXn2r// ?nnegrE// mx_norm_col_perm_le.
apply: (@gauss_ibp0 m (F \o col_perm s) (dF \o col_perm s) C k).
- move=> x; apply: (is_derive_transfer _ (dF_ (col_perm s x))) => h.
  by rewrite /= PD.
- exact: measurableT_comp mF mP.
- exact: measurableT_comp mdF mP.
- move=> x; have -> : (fun t => (dF \o col_perm s) (t *: delta_mx 0 0 + x)) =
      (fun t => dF (t *: delta_mx 0 i + col_perm s x)).
    by apply/funext => t; rewrite /= PD.
  exact: ldF.
- exact: bP.
- exact: bP.
Qed.

Lemma gauss_ibp n (i : 'I_n) (F dF : 'rV[R]_n -> R) (C : R) (k : nat) :
  (forall x, is_derive x (delta_mx 0 i) F (dF x)) ->
  continuous F -> continuous dF ->
  (forall x, `|F x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|dF x| <= C * (1 + `|x| ^+ k)) ->
  (\int[gauss n]_x (x 0 i * F x)%:E = \int[gauss n]_x (dF x)%:E)%E.
Proof.
move=> dF_ cF cdF; apply: gauss_ibp_line => //.
- exact: continuous_measurable_mx.
- exact: continuous_measurable_mx.
move=> x t; apply: continuous_comp; last exact: cdF.
apply: cvgD; last exact: cvg_cst.
by apply: cvgZ; [exact: cvg_id|exact: cvg_cst].
Qed.

(* A partial derivative of a continuous function is measurable: it is the
   limit of the difference quotients along the sequence 1 / (m + 1). *)
Lemma measurable_derive_rV n (F dF : 'rV[R]_n -> R) (v : 'rV[R]_n) :
  continuous F -> (forall x, is_derive x v F (dF x)) ->
  measurable_fun [set: 'rV[R]_n] dF.
Proof.
move=> cF dF_; have mF := continuous_measurable_mx cF.
apply: (@measurable_fun_cvg _ _ _ _
  (fun m x => (harmonic m)^-1 *: (F (harmonic m *: v + x) - F x))).
  move=> m.
  have mT : measurable_fun [set: 'rV[R]_n] (fun x => harmonic m *: v + x).
    apply/measurable_fun_mxP => i j; under eq_fun do rewrite mxE.
    by apply: measurable_funD => //; exact: measurable_mxentry.
  apply: measurable_funM => //; apply: measurable_funB => //.
  exact: measurableT_comp mF mT.
move=> x _; have [dv dval] := dF_ x.
have qc : (fun h : R => h^-1 *: ((F \o shift x) (h *: v) - F x)) @ 0^' --> dF x.
  by rewrite -dval; exact: dv.
apply: ((cvgr_dnbhsP _ 0 (dF x)).1 qc harmonic); split; last exact: cvg_harmonic.
by move=> k; rewrite /= invr_eq0 pnatr_eq0.
Qed.

(* Second-order integration by parts along the coordinate i:
   E[(x_i^2 - 1) F(x)] = E[d_i d_i F(x)], for F continuous with partial
   derivatives dF and d2F along the i-th axis, d2F continuous, all three of
   polynomial growth. dF need not be continuous. *)
Theorem gauss_ibp2 n (i : 'I_n) (F dF d2F : 'rV[R]_n -> R) (C : R) (k : nat) :
  (forall x, is_derive x (delta_mx 0 i) F (dF x)) ->
  (forall x, is_derive x (delta_mx 0 i) dF (d2F x)) ->
  continuous F -> continuous d2F ->
  (forall x, `|F x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|dF x| <= C * (1 + `|x| ^+ k)) ->
  (forall x, `|d2F x| <= C * (1 + `|x| ^+ k)) ->
  (\int[gauss n]_x ((x 0 i ^+ 2 - 1) * F x)%:E = \int[gauss n]_x (d2F x)%:E)%E.
Proof.
move=> dF_ d2F_ cF cd2F FC dFC d2FC; have C0 := poly_bound_ge0 FC.
set e : 'rV[R]_n := delta_mx 0 i.
have mF := continuous_measurable_mx cF.
have md2F := continuous_measurable_mx cd2F.
have mdF := measurable_derive_rV cF dF_.
have mxi : measurable_fun [set: 'rV[R]_n] (fun x => x 0 i) := measurable_mxentry 0 i.
have line (x : 'rV[R]_n) : continuous (fun t : R => t *: e + x).
  move=> t; apply: cvgD; last exact: cvg_cst.
  by apply: cvgZ; [exact: cvg_id|exact: cvg_cst].
(* dF is continuous along the lines parallel to e: its derivative there is
   d2F. *)
have ldF (x : 'rV[R]_n) : continuous (fun t : R => dF (t *: e + x)).
  move=> t; apply: differentiable_continuous; apply/derivable1_diffP.
  have : is_derive t 1 (fun t : R => dF (t *: e + x)) (d2F (t *: e + x)).
    apply: (is_derive_transfer (G := dF) (b := t *: e + x) (w := e)).
    by move=> h; rewrite scalerDl addrA [h%:A]mulr1.
  by case.
(* E[x_i dF(x)] = E[d2F(x)]. *)
have E1 := gauss_ibp_line d2F_ mdF md2F
  (fun x t => continuous_comp (line x t) (cd2F _)) dFC d2FC.
(* E[x_i (x_i F(x))] = E[F(x) + x_i dF(x)]. *)
have hi (x : 'rV[R]_n) : is_derive x e (fun y : 'rV[R]_n => y 0 i) 1.
  apply: (is_derive_transfer (G := id) (b := x 0 i) (w := 1)) => h.
  by rewrite /e !mxE !eqxx /= mulr1 [h%:A]mulr1.
have G_ (x : 'rV[R]_n) : is_derive x e (fun y => y 0 i * F y) (F x + x 0 i * dF x).
  have := is_deriveM (hi x) (dF_ x).
  by rewrite [(F x)%:A]mulr1 addrC.
have xdFC := entry_mul_bound i dFC.
have G'C (x : 'rV[R]_n) : `|F x + x 0 i * dF x| <= (4 * C) * (1 + `|x| ^+ k.+1).
  apply: (le_trans (ler_normD _ _)); have := FC x; have := xdFC x.
  have := exprn1S_le k (normr_ge0 x); have := exprn_ge0 k.+1 (normr_ge0 x).
  nra.
have GC (x : 'rV[R]_n) : `|x 0 i * F x| <= (4 * C) * (1 + `|x| ^+ k.+1).
  apply: (le_trans (entry_mul_bound i FC x)).
  have := exprn_ge0 k.+1 (normr_ge0 x); nra.
have mG : measurable_fun [set: 'rV[R]_n] (fun y => y 0 i * F y).
  exact: measurable_funM mxi mF.
have mxdF : measurable_fun [set: 'rV[R]_n] (fun y => y 0 i * dF y).
  exact: measurable_funM mxi mdF.
have lG' (x : 'rV[R]_n) :
    continuous (fun t : R => F (t *: e + x) + (t *: e + x) 0 i * dF (t *: e + x)).
  move=> t; apply: cvgD; first exact: (continuous_comp (line x t) (cF _)).
  apply: cvgM; last exact: ldF.
  exact: (continuous_comp (line x t) (@coord_continuous R 1 n 0 i _)).
have E2 := gauss_ibp_line G_ mG (measurable_funD mF mxdF) lG' GC G'C.
(* (x_i^2 - 1) F = x_i (x_i F) - F, and the terms in E[F] cancel. *)
have IF := integrable_gauss_poly mF FC.
have IxdF := integrable_gauss_poly mxdF xdFC.
have IxG := integrable_gauss_poly (measurable_funM mxi mG) (entry_mul_bound i GC).
transitivity (\int[gauss n]_x ((x 0 i * (x 0 i * F x))%:E - (F x)%:E))%E.
  by apply: eq_integral => x _; rewrite -EFinB mulrBl expr2 mulrA mul1r.
rewrite integralB_EFin // E2.
have -> : (\int[gauss n]_x (F x + x 0 i * dF x)%:E =
    \int[gauss n]_x (F x)%:E + \int[gauss n]_x (x 0 i * dF x)%:E)%E.
  by rewrite -(integralD_EFin _ IF IxdF).
by rewrite E1 addeAC subee ?add0e //; exact: integrable_fin_num IF.
Qed.

End gauss_ibp.
