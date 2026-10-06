From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import exp measure lebesgue_stieltjes_measure.
From mathcomp Require Import lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From GaussianAnalysis.gaussian Require Import measurable_matrix normal_integral gauss.
From GaussianAnalysis.comparison Require Import normal_linear.

(**md**************************************************************************)
(* # Rotation invariance of Gaussian measures                                 *)
(*                                                                            *)
(* Lebesgue measure on the plane is invariant under the shears (x, y) |-> (x  *)
(* + a y, y) and (x, y) |-> (x, y + b x), by Fubini and the invariance of     *)
(* Lebesgue measure on the line under translations. A rotation of angle       *)
(* different from pi is a product of three shears, so Lebesgue measure on the *)
(* plane is rotation invariant (ge0_integral_rotation2). The standard         *)
(* Gaussian measure on the plane, normal_prob 0 1 \x normal_prob 0 1, has a   *)
(* rotation invariant density, so it is rotation invariant                    *)
(* (normal2_rotation).                                                        *)
(*                                                                            *)
(* For c^2 + s^2 = 1 and independent x and y of law gauss n, the pair (c x -  *)
(* s y, s x + c y) has the law of (x, y) (ge0_integral_gauss2_rotation,       *)
(* gauss2_rotation): rotating pairwise the coordinates of two independent     *)
(* standard Gaussian vectors preserves their joint law. In particular c x + s *)
(* y has law gauss n (ge0_integral_gauss_lincomb).                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lebesgue2_shear.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma ge0_integral_shear1 (h : R * R -> \bar R) (a : R) :
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[mu \x mu]_p h (p.1 + a * p.2, p.2)%R = \int[mu \x mu]_p h p.
Proof.
move=> mh h0.
have mhs : measurable_fun [set: R * R] (fun p : R * R => h (p.1 + a * p.2, p.2)%R).
  apply: measurableT_comp => //; apply/measurable_fun_pairP; split => //=.
    by apply: measurable_funD => //; apply: measurable_funM.
  exact: measurable_snd.
rewrite (@fubini_tonelli2 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mhs).
  by move=> p; exact: h0.
rewrite (@fubini_tonelli2 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mh)//.
apply: eq_integral => y _; rewrite /fubini_G /=.
have := @ge0_integral_lebesgue_affine R 1 (a * y) (fun x => h (x, y)) (oner_neq0 R).
rewrite normr1 invr1 mul1e.
have mhy : measurable_fun [set: R] (fun x : R => h (x, y)).
  exact: (measurableT_comp mh (pair2_measurable y)).
move=> /(_ mhy (fun x => h0 (x, y))) <-.
by apply: eq_integral => x _; rewrite mul1r.
Qed.

Lemma ge0_integral_shear2 (h : R * R -> \bar R) (b : R) :
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[mu \x mu]_p h (p.1, p.2 + b * p.1)%R = \int[mu \x mu]_p h p.
Proof.
move=> mh h0.
have mhs : measurable_fun [set: R * R] (fun p : R * R => h (p.1, p.2 + b * p.1)%R).
  apply: measurableT_comp => //; apply/measurable_fun_pairP; split => //=.
    exact: measurable_fst.
  by apply: measurable_funD => //; apply: measurable_funM.
rewrite (@fubini_tonelli1 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mhs).
  by move=> p; exact: h0.
rewrite (@fubini_tonelli1 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mh)//.
apply: eq_integral => x _; rewrite /fubini_F /=.
have := @ge0_integral_lebesgue_affine R 1 (b * x) (fun y => h (x, y)) (oner_neq0 R).
rewrite normr1 invr1 mul1e.
have mhx : measurable_fun [set: R] (fun y : R => h (x, y)).
  exact: (measurableT_comp mh (pair1_measurable x)).
move=> /(_ mhx (fun y => h0 (x, y))) <-.
by apply: eq_integral => y _; rewrite mul1r.
Qed.

Lemma ge0_integral_oppr2 (h : R * R -> \bar R) :
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[mu \x mu]_p h (- p.1, - p.2)%R = \int[mu \x mu]_p h p.
Proof.
move=> mh h0; have N10 : (-1 != 0 :> R)%R by rewrite oppr_eq0 oner_eq0.
have mhs : measurable_fun [set: R * R] (fun p : R * R => h (- p.1, - p.2)%R).
  apply: measurableT_comp => //; apply/measurable_fun_pairP; split => //=.
    exact: measurableT_comp measurable_fst.
  exact: measurableT_comp measurable_snd.
rewrite (@fubini_tonelli2 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mhs).
  by move=> p; exact: h0.
rewrite (@fubini_tonelli2 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _ mh)//.
rewrite /fubini_G /=.
have mhy y : measurable_fun [set: R] (fun x : R => h (x, y)).
  exact: (measurableT_comp mh (pair2_measurable y)).
transitivity (\int[mu]_y \int[mu]_x h (x, - y)%R).
  apply: eq_integral => y _.
  have := @ge0_integral_lebesgue_affine R (-1) 0 (fun x => h (x, - y)%R).
  rewrite normrN normr1 invr1 mul1e.
  move=> /(_ N10 (mhy (- y)%R) (fun x => h0 (x, - y)%R)) <-.
  by apply: eq_integral => x _; rewrite mulN1r addr0.
pose G y := \int[mu]_x h (x, y).
have mG : measurable_fun [set: R] G.
  exact: (@measurable_fun_fubini_tonelli_G _ _ (measurableTypeR R)
    (measurableTypeR R) R mu h mh h0).
have G0 y : 0 <= G y by apply: integral_ge0 => x _; exact: h0.
have := @ge0_integral_lebesgue_affine R (-1) 0 G.
rewrite normrN normr1 invr1 mul1e => /(_ N10 mG G0) <-.
by apply: eq_integral => y _; rewrite mulN1r addr0.
Qed.

Lemma ge0_integral_rotation2 (h : R * R -> \bar R) (c s : R) :
    (c ^+ 2 + s ^+ 2 = 1)%R ->
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[mu \x mu]_p h (c * p.1 - s * p.2, s * p.1 + c * p.2)%R =
  \int[mu \x mu]_p h p.
Proof.
move=> cs mh h0; have [c1|c1] := eqVneq c (-1)%R.
  have s0 : (s = 0)%R.
    move: cs; rewrite c1 sqrrN expr1n => /(congr1 (fun x => x - 1)%R).
    by rewrite addrAC subrr add0r => /eqP; rewrite sqrf_eq0 => /eqP.
  rewrite -[RHS](ge0_integral_oppr2 mh h0); apply: eq_integral => p _.
  by rewrite c1 s0 !mul0r subr0 add0r !mulN1r.
have c10 : (1 + c != 0)%R by apply: contra c1; rewrite addrC addr_eq0 => /eqP ->.
pose t := (s / (1 + c))%R.
pose A (p : R * R) := (p.1 - t * p.2, p.2)%R.
pose B (p : R * R) := (p.1, p.2 + s * p.1)%R.
have mA : measurable_fun [set: R * R] A.
  apply/measurable_fun_pairP; split => //=; last exact: measurable_snd.
  by apply: measurable_funB => //; apply: measurable_funM.
have mB : measurable_fun [set: R * R] B.
  apply/measurable_fun_pairP; split => //=; first exact: measurable_fst.
  by apply: measurable_funD => //; apply: measurable_funM.
have s2 : (s ^+ 2 = 1 - c ^+ 2)%R by rewrite -cs addrAC subrr add0r.
have RE p : (c * p.1 - s * p.2, s * p.1 + c * p.2)%R = A (B (A p)).
  by rewrite /A /B /t /=; congr pair; field: s2.
transitivity (\int[mu \x mu]_p ((h \o A) \o B) (A p)).
  by apply: eq_integral => p _; rewrite RE.
have ShA (g : R * R -> \bar R) : measurable_fun [set: R * R] g ->
    (forall p, 0 <= g p) -> \int[mu \x mu]_p g (A p) = \int[mu \x mu]_p g p.
  move=> mg g0; rewrite -(ge0_integral_shear1 (- t)%R mg g0).
  by apply: eq_integral => p _; rewrite /A mulNr.
rewrite ShA.
- by apply: measurableT_comp => //; exact: measurableT_comp.
- by move=> p; exact: h0.
rewrite (ge0_integral_shear2 s _ (fun p => h0 (A p))).
  exact: measurableT_comp.
by rewrite ShA.
Qed.

End lebesgue2_shear.

Section normal2.
Context {R : realType}.
Local Notation mu := (@lebesgue_measure R).
Local Notation N := (@normal_prob R 0 1).
Local Notation phi := (@normal_pdf R 0 1).
Local Open Scope ereal_scope.

Lemma ge0_integral_normal2 (h : R * R -> \bar R) :
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[N \x N]_p h p = \int[mu \x mu]_p (h p * (phi p.1 * phi p.2)%:E).
Proof.
move=> mh h0.
rewrite (@fubini_tonelli1 _ _ (measurableTypeR R) (measurableTypeR R) R N N h mh h0).
have mhphi : measurable_fun [set: R * R]
    (fun p : R * R => h p * (phi p.1 * phi p.2)%:E).
  apply: emeasurable_funM => //; apply/measurable_EFinP; apply: measurable_funM.
    exact: measurableT_comp (measurable_normal_pdf 0 1) measurable_fst.
  exact: measurableT_comp (measurable_normal_pdf 0 1) measurable_snd.
have hphi0 p : 0 <= h p * (phi p.1 * phi p.2)%:E.
  by rewrite mule_ge0// lee_fin mulr_ge0// normal_pdf_ge0.
rewrite (@fubini_tonelli1 _ _ (measurableTypeR R) (measurableTypeR R) R mu mu _
  mhphi hphi0).
rewrite ge0_integral_normal_prob.
- by move=> x; apply: integral_ge0 => y _; exact: h0.
- exact: (@measurable_fun_fubini_tonelli_F _ _ (measurableTypeR R)
    (measurableTypeR R) R N h mh h0).
apply: eq_integral => x _; rewrite /fubini_F /=.
rewrite ge0_integral_normal_prob.
- by move=> y; exact: h0.
- exact: (measurableT_comp mh (pair1_measurable x)).
rewrite -ge0_integralZr//.
- apply: emeasurable_funM; first exact: (measurableT_comp mh (pair1_measurable x)).
  by apply/measurable_EFinP; exact: measurable_normal_pdf.
- by move=> y _; rewrite mule_ge0// lee_fin normal_pdf_ge0.
- by rewrite lee_fin normal_pdf_ge0.
by apply: eq_integral => y _ /=; rewrite -muleA -EFinM mulrC.
Qed.

Lemma normal_pdf01_rotation (c s x y : R) : (c ^+ 2 + s ^+ 2 = 1)%R ->
  (phi (c * x - s * y) * phi (s * x + c * y) = phi x * phi y)%R.
Proof.
move=> cs; rewrite !normal_pdfE ?oner_neq0// /normal_fun !subr0.
rewrite mulrACA [RHS]mulrACA -!expRD; congr (_ * expR _)%R.
have s2 : (s ^+ 2 = 1 - c ^+ 2)%R by rewrite -cs addrAC subrr add0r.
by field: s2.
Qed.

Theorem ge0_integral_normal2_rotation (h : R * R -> \bar R) (c s : R) :
    (c ^+ 2 + s ^+ 2 = 1)%R ->
    measurable_fun [set: R * R] h -> (forall p, 0 <= h p) ->
  \int[N \x N]_p h (c * p.1 - s * p.2, s * p.1 + c * p.2)%R =
  \int[N \x N]_p h p.
Proof.
move=> cs mh h0.
pose Rot (p : R * R) := (c * p.1 - s * p.2, s * p.1 + c * p.2)%R.
have mRot : measurable_fun [set: R * R] Rot.
  apply/measurable_fun_pairP; split => /=.
    by apply: measurable_funB => //; apply: measurable_funM.
  by apply: measurable_funD => //; apply: measurable_funM.
have mhR : measurable_fun [set: R * R] (h \o Rot) := measurableT_comp mh mRot.
have mpsi : measurable_fun [set: R * R] (fun p : R * R => (phi p.1 * phi p.2)%R).
  apply: measurable_funM.
    exact: measurableT_comp (measurable_normal_pdf 0 1) measurable_fst.
  exact: measurableT_comp (measurable_normal_pdf 0 1) measurable_snd.
rewrite (ge0_integral_normal2 mhR (fun p => h0 (Rot p))) ge0_integral_normal2//.
transitivity (\int[mu \x mu]_p
    ((fun q : R * R => h q * (phi q.1 * phi q.2)%:E) (Rot p))).
  apply: eq_integral => p _ /=; congr (_ * _%:E).
  by rewrite normal_pdf01_rotation.
rewrite (@ge0_integral_rotation2 R (fun q : R * R => h q * (phi q.1 * phi q.2)%:E) c s cs)//.
- by apply: emeasurable_funM => //; exact/measurable_EFinP.
- by move=> q; rewrite mule_ge0// lee_fin mulr_ge0// normal_pdf_ge0.
Qed.

Theorem normal2_rotation (c s : R) (B : set (R * R)) :
    (c ^+ 2 + s ^+ 2 = 1)%R -> measurable B ->
  (N \x N) ((fun p : R * R => (c * p.1 - s * p.2, s * p.1 + c * p.2)%R) @^-1` B) =
  (N \x N) B.
Proof.
move=> cs mB.
pose Rot (p : R * R) := (c * p.1 - s * p.2, s * p.1 + c * p.2)%R.
have mRot : measurable_fun [set: R * R] Rot.
  apply/measurable_fun_pairP; split => /=.
    by apply: measurable_funB => //; apply: measurable_funM.
  by apply: measurable_funD => //; apply: measurable_funM.
have mRB : measurable (Rot @^-1` B).
  by rewrite -[X in measurable X]setTI; exact: mRot.
have E1 : (N \x N) (Rot @^-1` B) = \int[N \x N]_p (\1_B (Rot p))%:E.
  by rewrite -[in LHS](setIT (Rot @^-1` B)) -integral_indic.
change ((N \x N) (Rot @^-1` B) = (N \x N) B).
rewrite E1 -[in RHS](setIT B) -integral_indic//.
apply: (@ge0_integral_normal2_rotation (fun p => (\1_B p)%:E) c s cs).
- by apply/measurable_EFinP; exact: measurable_indic.
- by move=> p; rewrite lee_fin indicE.
Qed.

End normal2.

Section gauss2_cons.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).
Local Open Scope ereal_scope.

Lemma ge0_integral_gauss2_cons n (F : 'rV[R]_n.+1 * 'rV[R]_n.+1 -> \bar R) :
    measurable_fun [set: 'rV[R]_n.+1 * 'rV[R]_n.+1] F -> (forall p, 0 <= F p) ->
  \int[gauss n.+1 \x gauss n.+1]_p F p =
  \int[N \x N]_q \int[gauss n \x gauss n]_r
    F (rV_cons (q.1, r.1), rV_cons (q.2, r.2)).
Proof.
move=> mF F0.
pose K (a : measurableTypeR R) (u : 'rV[R]_n) (b : measurableTypeR R)
  (v : 'rV[R]_n) := F (rV_cons (a, u), rV_cons (b, v)).
have K0 a u b v : 0 <= K a u b v by exact: F0.
have mFx x : measurable_fun [set: 'rV[R]_n.+1] (fun y => F (x, y)).
  exact: measurableT_comp mF (pair1_measurable x).
have E1 x : \int[gauss n.+1]_y F (x, y) =
    \int[N]_b \int[gauss n]_v F (x, rV_cons (b, v)).
  by rewrite ge0_integral_gauss_cons.
rewrite (@fubini_tonelli1 _ _ _ _ R (gauss n.+1) (gauss n.+1) F mF F0).
rewrite ge0_integral_gauss_cons; first last.
2: by move=> x; apply: integral_ge0 => y _; exact: F0.
2: exact: (@measurable_fun_fubini_tonelli_F _ _ _ _ R (gauss n.+1) F mF F0).
transitivity (\int[N]_a \int[gauss n]_u \int[N]_b \int[gauss n]_v K a u b v).
  by apply: eq_integral => a _; apply: eq_integral => u _; rewrite /fubini_F E1.
have mPhi : measurable_fun
    [set: (measurableTypeR R * measurableTypeR R) * ('rV[R]_n * 'rV[R]_n)]
    (fun w => F (rV_cons (w.1.1, w.2.1), rV_cons (w.1.2, w.2.2))).
  apply: measurableT_comp => //; apply: measurable_fun_pair.
    have h := measurableT_comp (@measurable_rV_cons R n)
      (measurable_fun_pair (measurableT_comp (@measurable_fst _ _ _ _) measurable_fst)
                           (measurableT_comp (@measurable_fst _ _ _ _) measurable_snd)).
    exact: h.
  have h := measurableT_comp (@measurable_rV_cons R n)
    (measurable_fun_pair (measurableT_comp (@measurable_snd _ _ _ _) measurable_fst)
                         (measurableT_comp (@measurable_snd _ _ _ _) measurable_snd)).
  exact: h.
pose PP : probability ('rV[R]_n * 'rV[R]_n)%type R := (@gauss R n \x @gauss R n)%E.
have mPsi := @measurable_fun_fubini_tonelli_F _ _
  (measurableTypeR R * measurableTypeR R)%type ('rV[R]_n * 'rV[R]_n)%type R
  PP _ mPhi (fun w => F0 _).
have Psi0 q : 0 <= \int[gauss n \x gauss n]_r
    F (rV_cons (q.1, r.1), rV_cons (q.2, r.2)).
  by apply: integral_ge0 => r _; exact: F0.
transitivity (\int[N]_a \int[N]_b \int[gauss n]_u \int[gauss n]_v K a u b v);
    last first.
  rewrite (@fubini_tonelli1 _ _ _ _ R N N (fun q => \int[gauss n \x gauss n]_r
    F (rV_cons (q.1, r.1), rV_cons (q.2, r.2))) mPsi Psi0).
  apply: eq_integral => a _; rewrite /fubini_F; apply: eq_integral => b _ /=.
  have mKab : measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
      (fun r : 'rV[R]_n * 'rV[R]_n => F (rV_cons (a, r.1), rV_cons (b, r.2))).
    apply: measurableT_comp => //; apply: measurable_fun_pair.
      have h := measurableT_comp (@measurable_rV_cons R n)
        (measurable_fun_pair
          (@measurable_cst _ _ ('rV[R]_n * 'rV[R]_n)%type _ setT a)
          (@measurable_fst _ _ 'rV[R]_n 'rV[R]_n)).
      exact: h.
    have h := measurableT_comp (@measurable_rV_cons R n)
      (measurable_fun_pair
        (@measurable_cst _ _ ('rV[R]_n * 'rV[R]_n)%type _ setT b)
        (@measurable_snd _ _ 'rV[R]_n 'rV[R]_n)).
    exact: h.
  by rewrite (@fubini_tonelli1 _ _ _ _ R (gauss n) (gauss n) _ mKab (fun r => F0 _)).
apply: eq_integral => a _.
have mKa : measurable_fun [set: ('rV[R]_n * measurableTypeR R) * 'rV[R]_n]
    (fun w : ('rV[R]_n * measurableTypeR R) * 'rV[R]_n => K a w.1.1 w.1.2 w.2).
  apply: measurableT_comp => //; apply: measurable_fun_pair.
    have h := measurableT_comp (@measurable_rV_cons R n)
      (measurable_fun_pair
        (@measurable_cst _ _ (('rV[R]_n * measurableTypeR R) * 'rV[R]_n)%type _ setT a)
        (measurableT_comp (@measurable_fst _ _ _ _) measurable_fst)).
    exact: h.
  have h := measurableT_comp (@measurable_rV_cons R n)
    (measurable_fun_pair (measurableT_comp (@measurable_snd _ _ _ _) measurable_fst)
      (@measurable_snd _ _ _ _)).
  exact: h.
have mPhia := @measurable_fun_fubini_tonelli_F _ _ _ _ R (gauss n) _ mKa
  (fun w => K0 _ _ _ _).
have := @fubini_tonelli _ _ _ _ R (gauss n) N _ mPhia
  (fun w => integral_ge0 _ (fun v _ => K0 a w.1 w.2 v)).
by rewrite /fubini_F /=.
Qed.

Lemma rV_cons_lin n (c s a b : R) (u v : 'rV[R]_n) :
  (c *: rV_cons (a, u) + s *: rV_cons (b, v) =
   rV_cons ((c * a + s * b)%R, c *: u + s *: v))%R.
Proof.
rewrite /rV_cons /=; apply/rowP => j; rewrite !mxE.
by case: splitP => k _; rewrite !mxE.
Qed.

Lemma rV_cons_lincomb n (c s a b : R) (u v : 'rV[R]_n) :
  (c *: rV_cons (a, u) - s *: rV_cons (b, v) =
   rV_cons ((c * a - s * b)%R, c *: u - s *: v))%R.
Proof. by rewrite -scaleNr rV_cons_lin mulNr scaleNr. Qed.

Theorem ge0_integral_gauss2_rotation n (c s : R)
    (f : 'rV[R]_n * 'rV[R]_n -> \bar R) :
    (c ^+ 2 + s ^+ 2 = 1)%R -> measurable_fun [set: 'rV[R]_n * 'rV[R]_n] f ->
    (forall p, 0 <= f p) ->
  \int[gauss n \x gauss n]_p f (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R =
  \int[gauss n \x gauss n]_p f p.
Proof.
move=> cs; elim: n f => [|n IH] f mf f0.
  apply: eq_integral => p _; congr f.
  by case: p => x y; congr pair; apply/matrixP => i [].
have consE (a b : R) (u v : 'rV[R]_n) :
    ((c *: rV_cons (a, u) - s *: rV_cons (b, v))%R,
     (s *: rV_cons (a, u) + c *: rV_cons (b, v))%R) =
    (rV_cons ((c * a - s * b)%R, (c *: u - s *: v)%R),
     rV_cons ((s * a + c * b)%R, (s *: u + c *: v)%R)).
  by rewrite rV_cons_lincomb rV_cons_lin.
have mRot m : measurable_fun [set: 'rV[R]_m * 'rV[R]_m]
    (fun p : 'rV[R]_m * 'rV[R]_m =>
       ((c *: p.1 - s *: p.2)%R, (s *: p.1 + c *: p.2)%R)).
  apply: measurable_fun_pair.
    apply: measurable_addmx.
      by apply: measurable_scalemx => //; exact: measurable_fst.
    by apply: measurable_oppmx; apply: measurable_scalemx => //;
      exact: measurable_snd.
  apply: measurable_addmx.
    by apply: measurable_scalemx => //; exact: measurable_fst.
  by apply: measurable_scalemx => //; exact: measurable_snd.
rewrite (ge0_integral_gauss2_cons (measurableT_comp mf (mRot _)) (fun p => f0 _)).
rewrite (ge0_integral_gauss2_cons mf f0).
pose Psi (q : R * R) := \int[gauss n \x gauss n]_r
  f (rV_cons (q.1, r.1), rV_cons (q.2, r.2)).
have mhq (q : R * R) : measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
    (fun r : 'rV[R]_n * 'rV[R]_n => f (rV_cons (q.1, r.1), rV_cons (q.2, r.2))).
  apply: measurableT_comp => //; apply: measurable_fun_pair.
    have h := measurableT_comp (@measurable_rV_cons R n)
      (measurable_fun_pair
        (@measurable_cst _ _ ('rV[R]_n * 'rV[R]_n)%type _ setT q.1)
        (@measurable_fst _ _ 'rV[R]_n 'rV[R]_n)).
    exact: h.
  have h := measurableT_comp (@measurable_rV_cons R n)
    (measurable_fun_pair
      (@measurable_cst _ _ ('rV[R]_n * 'rV[R]_n)%type _ setT q.2)
      (@measurable_snd _ _ 'rV[R]_n 'rV[R]_n)).
  exact: h.
transitivity (\int[N \x N]_q Psi (c * q.1 - s * q.2, s * q.1 + c * q.2)%R).
  apply: eq_integral => q _; rewrite /Psi.
  rewrite -(IH _ (mhq (c * q.1 - s * q.2, s * q.1 + c * q.2)%R) (fun r => f0 _)).
  by apply: eq_integral => r _ /=; rewrite consE.
have mPhi : measurable_fun
    [set: (measurableTypeR R * measurableTypeR R) * ('rV[R]_n * 'rV[R]_n)]
    (fun w => f (rV_cons (w.1.1, w.2.1), rV_cons (w.1.2, w.2.2))).
  apply: measurableT_comp => //; apply: measurable_fun_pair.
    have h := measurableT_comp (@measurable_rV_cons R n)
      (measurable_fun_pair
        (measurableT_comp (@measurable_fst _ _ _ _) measurable_fst)
        (measurableT_comp (@measurable_fst _ _ _ _) measurable_snd)).
    exact: h.
  have h := measurableT_comp (@measurable_rV_cons R n)
    (measurable_fun_pair
      (measurableT_comp (@measurable_snd _ _ _ _) measurable_fst)
      (measurableT_comp (@measurable_snd _ _ _ _) measurable_snd)).
  exact: h.
pose PP : probability ('rV[R]_n * 'rV[R]_n)%type R := (@gauss R n \x @gauss R n)%E.
have mPsi := @measurable_fun_fubini_tonelli_F _ _
  (measurableTypeR R * measurableTypeR R)%type ('rV[R]_n * 'rV[R]_n)%type R
  PP _ mPhi (fun w => f0 _).
have Psi0 q : 0 <= Psi q by apply: integral_ge0 => r _; exact: f0.
exact: (@ge0_integral_normal2_rotation R Psi c s cs mPsi Psi0).
Qed.

Corollary gauss2_rotation n (c s : R) (E : set ('rV[R]_n * 'rV[R]_n)) :
    (c ^+ 2 + s ^+ 2 = 1)%R -> measurable E ->
  (gauss n \x gauss n)
    ((fun p : 'rV[R]_n * 'rV[R]_n => (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R)
       @^-1` E) = (gauss n \x gauss n) E.
Proof.
move=> cs mE.
have mRot : measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
    (fun p : 'rV[R]_n * 'rV[R]_n => (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R).
  apply: measurable_fun_pair.
    apply: measurable_addmx.
      by apply: measurable_scalemx => //; exact: measurable_fst.
    by apply: measurable_oppmx; apply: measurable_scalemx => //;
      exact: measurable_snd.
  apply: measurable_addmx.
    by apply: measurable_scalemx => //; exact: measurable_fst.
  by apply: measurable_scalemx => //; exact: measurable_snd.
have mRE : measurable ((fun p : 'rV[R]_n * 'rV[R]_n =>
    (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R) @^-1` E).
  by rewrite -[X in measurable X]setTI; exact: mRot.
rewrite -[in LHS](setIT (_ @^-1` E)) -[in RHS](setIT E) -!integral_indic//.
apply: (@ge0_integral_gauss2_rotation n c s (fun p => (\1_E p)%:E) cs).
- by apply/measurable_EFinP; exact: measurable_indic.
- by move=> p; rewrite lee_fin indicE.
Qed.

Corollary ge0_integral_gauss_lincomb n (c s : R) (f : 'rV[R]_n -> \bar R) :
    (c ^+ 2 + s ^+ 2 = 1)%R -> measurable_fun [set: 'rV[R]_n] f ->
    (forall x, 0 <= f x) ->
  \int[gauss n \x gauss n]_p f (c *: p.1 + s *: p.2)%R = \int[gauss n]_x f x.
Proof.
move=> cs mf f0.
have sc : (s ^+ 2 + c ^+ 2 = 1)%R by rewrite addrC.
have mf2 : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => f p.2).
  exact: measurableT_comp mf measurable_snd.
have := @ge0_integral_gauss2_rotation n s c (fun p => f p.2) sc mf2 (fun p => f0 _).
rewrite /= => ->.
rewrite (@fubini_tonelli1 _ _ _ _ R (gauss n) (gauss n) _ mf2 (fun p => f0 _)).
under eq_integral do rewrite /fubini_F /=.
by rewrite integral_cst// [X in (_ * X)%E]probability_setT mule1.
Qed.

Lemma measurable_gauss2_rot n (c s : R) :
  measurable_fun [set: 'rV[R]_n * 'rV[R]_n]
    (fun p : 'rV[R]_n * 'rV[R]_n => (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R).
Proof.
apply: measurable_fun_pair.
  apply: measurable_addmx.
    by apply: measurable_scalemx => //; exact: measurable_fst.
  by apply: measurable_oppmx; apply: measurable_scalemx => //; exact: measurable_snd.
apply: measurable_addmx.
  by apply: measurable_scalemx => //; exact: measurable_fst.
by apply: measurable_scalemx => //; exact: measurable_snd.
Qed.

Corollary integrable_gauss2_rotation n (c s : R) (f : 'rV[R]_n * 'rV[R]_n -> \bar R) :
    (c ^+ 2 + s ^+ 2 = 1)%R ->
    (gauss n \x gauss n).-integrable setT f ->
  (gauss n \x gauss n).-integrable setT
    (fun p => f (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R).
Proof.
move=> cs fi; have mf := measurable_int _ fi.
have maf : measurable_fun [set: 'rV[R]_n * 'rV[R]_n] (fun p => `|f p|).
  exact: measurableT_comp.
apply/integrableP; split; first exact: measurableT_comp mf (measurable_gauss2_rot c s).
have := @ge0_integral_gauss2_rotation n c s (fun p => `|f p|) cs maf (fun p => abse_ge0 _).
move=> /= ->; by case/integrableP: fi.
Qed.

Corollary integral_gauss2_rotation n (c s : R) (f : 'rV[R]_n * 'rV[R]_n -> \bar R) :
    (c ^+ 2 + s ^+ 2 = 1)%R ->
    (gauss n \x gauss n).-integrable setT f ->
  \int[gauss n \x gauss n]_p f (c *: p.1 - s *: p.2, s *: p.1 + c *: p.2)%R =
  \int[gauss n \x gauss n]_p f p.
Proof.
move=> cs fi; have mf := measurable_int _ fi.
rewrite integralE [RHS]integralE; congr (_ - _).
  rewrite -(@ge0_integral_gauss2_rotation n c s (f^\+) cs
    (measurable_funepos mf) (funepos_ge0 f)).
  by apply: eq_integral => p _; rewrite !funeposE.
rewrite -(@ge0_integral_gauss2_rotation n c s (f^\-) cs
  (measurable_funeneg mf) (funeneg_ge0 f)).
by apply: eq_integral => p _; rewrite !funenegE.
Qed.

End gauss2_cons.
