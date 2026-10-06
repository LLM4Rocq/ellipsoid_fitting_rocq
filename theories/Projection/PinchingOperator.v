(* Diffuse bulk control after pinching into an approximating head subspace. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import ring_tactic arithmetic_tactic.
From EllipsoidFitting Require Import PaperMainDefinitions Geometry.Psd
  Geometry.Homogeneous Geometry.HeadFrobenius Geometry.HeadCoefficients
  Cone.ConditionOperator Feature.DiagonalTrace Projection.Frobenius
  Projection.Pinching.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Operator.
Variable d : nat.
Implicit Types (A B P U H : 'M[R]_d) (a b : R).

Theorem paper_main_opnorm_from_frobenius A : paper_main_cone_opnorm_le A (paper_main_frobenius A).
Proof.
move=> u v.
have H1 := pmco_vec_cauchy_schwarz d u (A *m v).
rewrite mulmxA in H1.
have H2 := pmdb_form_frobenius d A v.
rewrite -paper_main_frobenius_trace in H2.
have Hu := pmh_vec_sqr_ge0 d u.
have H3 : (u^T *m u) 0 0*((A *m v)^T *m (A *m v)) 0 0<=
  (u^T *m u) 0 0*(paper_main_frobenius A ^+ 2*(v^T *m v) 0 0).
  by apply: ler_wpM2l.
nra.
Qed.

Lemma paper_main_opnorm_monotone A a b : 0<=a -> a<=b ->
  paper_main_cone_opnorm_le A a -> paper_main_cone_opnorm_le A b.
Proof.
move=> Ha Hab HA u v; apply: le_trans (HA u v) _.
apply: ler_wpM2r; first by apply: mulr_ge0; exact: pmh_vec_sqr_ge0.
nra.
Qed.

Theorem paper_main_opnorm_compression P A a : P^T = P -> P *m P = P ->
  paper_main_cone_opnorm_le A a -> paper_main_cone_opnorm_le (P *m A *m P) a.
Proof.
move=> HP HI HA u v.
have H := HA (P *m u) (P *m v).
have E : (((P *m u)^T *m A *m (P *m v)) 0 0) = (u^T *m (P *m A *m P) *m v) 0 0
  by rewrite trmx_mul HP !mulmxA.
rewrite E in H.
have Hu := paper_main_projection_action d P HP HI u.
have Hv := paper_main_projection_action d P HP HI v.
have Hpu := pmh_vec_sqr_ge0 d (P *m u).
have Hpv := pmh_vec_sqr_ge0 d (P *m v).
have Hnu := pmh_vec_sqr_ge0 d u.
have Hnv := pmh_vec_sqr_ge0 d v.
have HC : ((P *m u)^T *m (P *m u)) 0 0*((P *m v)^T *m (P *m v)) 0 0<=
  (u^T *m u) 0 0*(v^T *m v) 0 0 by exact: ler_pM.
apply: le_trans H _.
apply: ler_wpM2l; [exact: sqr_ge0|exact HC].
Qed.

Theorem paper_main_opnorm_add A B a b : 0<=a -> 0<=b ->
  paper_main_cone_opnorm_le A a -> paper_main_cone_opnorm_le B b ->
  paper_main_cone_opnorm_le (A+B) (a+b).
Proof.
move=> Ha Hb HA HB u v.
have H1 := HA u v; have H2 := HB u v.
have Hnu := pmh_vec_sqr_ge0 d u; have Hnv := pmh_vec_sqr_ge0 d v.
set z := (u^T *m u) 0 0*(v^T *m v) 0 0 in H1 H2 *.
have Hz : 0<=z by exact: mulr_ge0.
set t := Num.sqrt z.
have Ht : 0<=t by exact: sqrtr_ge0.
have Et : t ^+ 2=z by rewrite /t sqr_sqrtr.
have Hat : 0<=a*t by exact: mulr_ge0.
have Hbt : 0<=b*t by exact: mulr_ge0.
have Hx : `|(u^T *m A *m v) 0 0|<=a*t.
  have HH : `|(u^T *m A *m v) 0 0|^+2<=(a*t)^+2.
    by rewrite -normrX ger0_norm ?sqr_ge0 // exprMn Et.
  by move: HH; rewrite ler_sqr ?nnegrE ?normr_ge0.
have Hy : `|(u^T *m B *m v) 0 0|<=b*t.
  have HH : `|(u^T *m B *m v) 0 0|^+2<=(b*t)^+2.
    by rewrite -normrX ger0_norm ?sqr_ge0 // exprMn Et.
  by move: HH; rewrite ler_sqr ?nnegrE ?normr_ge0.
move: Hx; rewrite ler_norml => /andP [Hx1 Hx2].
move: Hy; rewrite ler_norml => /andP [Hy1 Hy2].
rewrite mulmxDr mulmxDl mxE.
have Hlo : -(a+b)*t<=((u^T *m A *m v) 0 0+(u^T *m B *m v) 0 0) by nra.
have Hhi : ((u^T *m A *m v) 0 0+(u^T *m B *m v) 0 0)<=(a+b)*t by nra.
have Hpos : 0<=(a+b)*t by apply: mulr_ge0; [exact: addr_ge0|exact Ht].
have Hbound : `|(u^T *m A *m v) 0 0+(u^T *m B *m v) 0 0|<=(a+b)*t.
  rewrite ler_norml; apply/andP; split; nra.
have Hsq : `|(u^T *m A *m v) 0 0+(u^T *m B *m v) 0 0|^+2<=((a+b)*t)^+2.
  by rewrite ler_sqr ?nnegrE ?normr_ge0.
by rewrite -normrX ger0_norm ?sqr_ge0 // exprMn Et in Hsq.
Qed.

Theorem paper_main_compression_leakage P U H :
  P^T = P -> U^T = U -> U *m U = U -> P *m H *m P = H ->
  paper_main_frobenius ((1%:M-U) *m H *m (1%:M-U))<=
    paper_main_frobenius (U-P) ^+ 2*paper_main_frobenius H.
Proof.
move=> HP HU HI HH.
pose Q := 1%:M-U.
have HQ : Q^T = Q by exact: paper_main_projection_complement_transpose.
have HJ : Q *m Q = Q by exact: paper_main_projection_complement_square.
have HQU : Q *m U = 0 by rewrite /Q mulmxBl mul1mx HI subrr.
have EU : Q *m P = Q *m (P-U) by rewrite mulmxBr HQU subr0.
have Hsmall : paper_main_frobenius (Q *m P)<=paper_main_frobenius (U-P).
  rewrite EU -[paper_main_frobenius (U-P)](pmh_frobeniusB d P U).
  exact: paper_main_projection_frobenius_left.
have Htrans : paper_main_frobenius (P *m Q)=paper_main_frobenius (Q *m P)
  by rewrite -[paper_main_frobenius (P *m Q)]paper_main_frobenius_transpose trmx_mul HP HQ.
have E : Q *m H *m Q=(Q *m P) *m H *m (P *m Q).
  by rewrite -{1}HH !mulmxA.
have H1 := paper_main_frobenius_product d ((Q *m P) *m H) (P *m Q).
have H2 := paper_main_frobenius_product d (Q *m P) H.
rewrite Htrans in H1.
have Hq := pmh_frobenius_ge0 d (Q *m P).
have Hh := pmh_frobenius_ge0 d H.
have Hd := pmh_frobenius_ge0 d (U-P).
have H3 : paper_main_frobenius ((Q *m P) *m H)*paper_main_frobenius (Q *m P)<=
  (paper_main_frobenius (Q *m P)*paper_main_frobenius H)*paper_main_frobenius (Q *m P)
  by apply: ler_wpM2r.
have H4 : paper_main_frobenius (Q *m P)^+2<=paper_main_frobenius (U-P)^+2 by nra.
have H5 : paper_main_frobenius (Q *m P)^+2*paper_main_frobenius H<=
  paper_main_frobenius (U-P)^+2*paper_main_frobenius H by apply: ler_wpM2r.
change (paper_main_frobenius (Q *m H *m Q)<=paper_main_frobenius (U-P)^+2*paper_main_frobenius H).
rewrite E; nra.
Qed.

Theorem paper_main_pinching_bulk_opnorm P U H B eps :
  P^T = P -> U^T = U -> U *m U = U -> P *m H *m P = H -> 0<=eps ->
  paper_main_cone_opnorm_le B eps ->
  paper_main_cone_opnorm_le ((1%:M-U) *m (H+B) *m (1%:M-U))
    (paper_main_frobenius (U-P)^+2*paper_main_frobenius H+eps).
Proof.
move=> HP HU HI HH Heps HB.
have HQ := paper_main_projection_complement_transpose d U HU.
have HJ := paper_main_projection_complement_square d U HI.
have HL := paper_main_compression_leakage P U H HP HU HI HH.
have Hh := pmh_frobenius_ge0 d H.
have HD : 0<=paper_main_frobenius (U-P)^+2*paper_main_frobenius H
  by apply: mulr_ge0; [exact: sqr_ge0|exact Hh].
have E : (1%:M-U) *m (H+B) *m (1%:M-U) =
  (1%:M-U) *m H *m (1%:M-U)+(1%:M-U) *m B *m (1%:M-U)
  by rewrite (mulmxDr (1%:M-U) H B) mulmxDl.
rewrite E.
apply: paper_main_opnorm_add HD Heps _ _.
- apply: (paper_main_opnorm_monotone ((1%:M-U) *m H *m (1%:M-U))
    (paper_main_frobenius ((1%:M-U) *m H *m (1%:M-U)))
    (paper_main_frobenius (U-P)^+2*paper_main_frobenius H)).
  + exact: pmh_frobenius_ge0.
  + exact HL.
  + exact: paper_main_opnorm_from_frobenius.
- exact: paper_main_opnorm_compression HQ HJ HB.
Qed.
End Operator.
