From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From GaussianAnalysis.matrix Require Import euclidean.
From GaussianAnalysis.gaussian Require Import measurable_matrix.
From GaussianAnalysis.convex Require Import moreau.

(**md**************************************************************************)
(* # The maximizer of a trace-penalized quadratic on a closed convex set      *)
(*                                                                            *)
(* For c > -1 and real n x n matrices H and S, let                            *)
(* trace_quad c H S = 2 <H, S> - |S|_F^2 - (c / n) (tr S)^2, with the         *)
(* Frobenius product <., .> and norm |.|_F of matrix/euclidean.v. Since       *)
(* (tr S)^2 <= n |S|_F^2, the quadratic part is coercive:                     *)
(* |S|_F^2 + (c / n) (tr S)^2 >= min(1, 1 + c) |S|_F^2. So trace_quad c H is  *)
(* strictly concave, and it has a unique maximizer on every nonempty closed   *)
(* convex set K of matrices: the nearest point of K to H for the scalar       *)
(* product <S, T> + (c / n) tr S tr T. The maximizer is computed by the       *)
(* projection of convex/moreau.v after the map                                *)
(* trace_scale (sqrt (1 + c) - 1), which multiplies the component of a matrix *)
(* along the identity by sqrt (1 + c), fixes the matrices of trace 0, and     *)
(* turns the quadratic part into a squared Frobenius norm.                    *)
(*                                                                            *)
(* - trace_scaleK:                                                            *)
(*   trace_scale a (trace_scale b S) = trace_scale ((1 + a) (1 + b) - 1) S,   *)
(*   so trace_scale a is invertible when a != -1; trace_scale_adj, it is      *)
(*   self-adjoint for the Frobenius product; mxtrace_scale,                   *)
(*   tr (trace_scale a S) = (1 + a) tr S.                                     *)
(* - mxtrace_sqr_le: (tr S)^2 / n <= |S|_F^2; trace_pen_ge, the coercivity    *)
(*   above, for every real c.                                                 *)
(* - trace_quad_expand: the exact expansion of trace_quad c H at any X:       *)
(*   trace_quad c H S - trace_quad c H X equals                               *)
(*   2 <H - X - (c / n) tr(X) I, S - X> minus                                 *)
(*   |S - X|_F^2 + (c / n) (tr (S - X))^2.                                    *)
(*                                                                            *)
(* In what follows, K is a set of n x n matrices that is closed in the        *)
(* coordinates of mxvec, convex and nonempty, c > -1 and X =                  *)
(* trace_argmax K c H.                                                        *)
(* - trace_argmaxP: X is in K and satisfies the variational inequality        *)
(*   <H - X - (c / n) tr(X) I, S - X> <= 0 for every S in K; trace_argmax_eq, *)
(*   X is the only point of K that does.                                      *)
(* - trace_argmax_ge: trace_quad c H S + min(1, 1 + c) |S - X|_F^2 <=         *)
(*   trace_quad c H X for every S in K; trace_argmax_unique, X is the only    *)
(*   maximizer of trace_quad c H on K.                                        *)
(* - trace_argmax_lipschitz: |X(H) - X(H')|_F <= |H - H'|_F / min(1, 1 + c).  *)
(* - trace_argmax0 and trace_argmax_norm: if 0 is in K, then X(0) = 0 and     *)
(*   |X(H)|_F <= |H|_F / min(1, 1 + c). trace_argmax_cone: if K is a cone,    *)
(*   then <H, X> = |X|_F^2 + (c / n) (tr X)^2 = trace_quad c H X.             *)
(* - trace_argmax_conj: if K is invariant under the conjugations              *)
(*   S |-> Q S Q^T by the orthogonal matrices Q, then                         *)
(*   X(Q H Q^T) = Q X(H) Q^T.                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*    trace_scale a S == S + a (tr S / n) I                                   *)
(*   trace_quad c H S == 2 <H, S> - |S|_F^2 - (c / n) (tr S)^2                *)
(* trace_argmax K c H == the maximizer of trace_quad c H on K                 *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section trace_facts.
Context {R : realType}.

Lemma mxdot1l n (A : 'M[R]_n) : mxdot 1%:M A = \tr A.
Proof. by rewrite mxdot_trace mul1mx mxtrace_tr. Qed.

Lemma mxtrace_divK n (A : 'M[R]_n) : \tr A / n%:R * n%:R = \tr A.
Proof.
case: n A => [|n] A; first by rewrite /mxtrace big_ord0 !mul0r.
by rewrite divfK // pnatr_eq0.
Qed.

(* Cauchy-Schwarz for the Frobenius product with the identity. *)
Lemma mxtrace_sqr_le n (A : 'M[R]_n) : \tr A ^+ 2 / n%:R <= mxdot A A.
Proof.
case: n A => [|n] A; first by rewrite mulr0n invr0 mulr0 mxdot_ge0.
rewrite ler_pdivrMr ?ltr0n //.
by have := mxdot_cauchy_schwarz A 1%:M; rewrite (mxdotC A) !mxdot1l mxtrace1.
Qed.

(* The coercivity of the quadratic part, for every real c. *)
Lemma trace_pen_ge n (c : R) (A : 'M[R]_n) :
  Num.min 1 (1 + c) * mxdot A A <= mxdot A A + c / n%:R * \tr A ^+ 2.
Proof.
have -> : c / n%:R * \tr A ^+ 2 = c * (\tr A ^+ 2 / n%:R) by ring.
have qm := mxtrace_sqr_le A.
have m0 := mxdot_ge0 A.
have q0 : 0 <= \tr A ^+ 2 / n%:R by rewrite divr_ge0 ?sqr_ge0 ?ler0n.
have a1 : Num.min 1 (1 + c) <= 1 by rewrite ge_min lexx.
have a2 : Num.min 1 (1 + c) <= 1 + c by rewrite ge_min lexx orbT.
move: (\tr A ^+ 2 / n%:R) (mxdot A A) (Num.min 1 (1 + c)) qm m0 q0 a1 a2.
move=> q m a qm m0 q0 a1 a2.
by have [c0|c0] := leP 0 c; nra.
Qed.

Lemma mxtraceB n (A B : 'M[R]_n) : \tr (A - B) = \tr A - \tr B.
Proof. exact: raddfB. Qed.

Lemma mxdot_conjmx n (Q A B : 'M[R]_n) : Q \is orthogonalmx ->
  mxdot (Q *m A *m Q^T) (Q *m B *m Q^T) = mxdot A B.
Proof.
move=> Qo; rewrite -!mulmxA mxdot_orthogonalmxl //.
by rewrite mxdot_orthogonalmxr // trmx_orthogonal.
Qed.

Lemma mxtrace_conj n (Q A : 'M[R]_n) : Q \is orthogonalmx ->
  \tr (Q *m A *m Q^T) = \tr A.
Proof. by move=> Qo; rewrite mxtrace_mulC mulmxA orthogonalmxT // mul1mx. Qed.

End trace_facts.

Section trace_scale.
Context {R : realType} {n : nat}.
Implicit Types (a b c k : R) (H S T X : 'M[R]_n).

(* Multiplies the component of S along the identity by 1 + a. *)
Definition trace_scale a S : 'M[R]_n := S + (a * (\tr S / n%:R)) *: 1%:M.

Definition trace_quad c H S : R :=
  2 * mxdot H S - mxdot S S - c / n%:R * \tr S ^+ 2.

Definition trace_argmax (K : set 'M[R]_n) c H : 'M[R]_n :=
  trace_scale ((Num.sqrt (1 + c))^-1 - 1) (vec_mx (proj
    [set v | K (trace_scale ((Num.sqrt (1 + c))^-1 - 1) (vec_mx v))]
    (mxvec (trace_scale ((Num.sqrt (1 + c))^-1 - 1) H)))).

Lemma trace_scaleD a S T :
  trace_scale a (S + T) = trace_scale a S + trace_scale a T.
Proof. by rewrite /trace_scale mxtraceD mulrDl mulrDr scalerDl addrACA. Qed.

Lemma trace_scaleZ a k S : trace_scale a (k *: S) = k *: trace_scale a S.
Proof.
rewrite /trace_scale mxtraceZ scalerDr scalerA.
by congr (_ + _ *: _); ring.
Qed.

Lemma trace_scaleN a S : trace_scale a (- S) = - trace_scale a S.
Proof. by rewrite -scaleN1r trace_scaleZ scaleN1r. Qed.

Lemma trace_scaleB a S T :
  trace_scale a (S - T) = trace_scale a S - trace_scale a T.
Proof. by rewrite trace_scaleD trace_scaleN. Qed.

Lemma trace_scale0 a : trace_scale a 0 = 0.
Proof. by rewrite /trace_scale mxtrace0 mul0r mulr0 scale0r addr0. Qed.

Lemma trace_scale_id S : trace_scale 0 S = S.
Proof. by rewrite /trace_scale mul0r scale0r addr0. Qed.

Lemma mxtrace_scale a S : \tr (trace_scale a S) = (1 + a) * \tr S.
Proof.
rewrite /trace_scale mxtraceD mxtraceZ mxtrace1 -mulrA mxtrace_divK.
by rewrite mulrDl mul1r.
Qed.

Lemma trace_scaleK a b S :
  trace_scale a (trace_scale b S) = trace_scale ((1 + a) * (1 + b) - 1) S.
Proof.
rewrite {1}/trace_scale mxtrace_scale /trace_scale -addrA -scalerDl.
by congr (_ + _ *: _); ring.
Qed.

Lemma mxdot_trace_scalel a S T :
  mxdot (trace_scale a S) T = mxdot S T + a / n%:R * (\tr S * \tr T).
Proof. by rewrite /trace_scale mxdotDl mxdotZl mxdot1l; ring. Qed.

Lemma trace_scale_adj a S T :
  mxdot (trace_scale a S) T = mxdot S (trace_scale a T).
Proof.
rewrite mxdot_trace_scalel [RHS]mxdotC mxdot_trace_scalel (mxdotC T S).
by ring.
Qed.

Lemma trace_scale_conj a Q S : Q \is orthogonalmx ->
  trace_scale a (Q *m S *m Q^T) = Q *m trace_scale a S *m Q^T.
Proof.
move=> Qo; rewrite /trace_scale mxtrace_conj // mulmxDr mulmxDl.
by rewrite -scalemxAr mulmx1 -scalemxAl (orthogonalmxP _ Qo).
Qed.

(* The second-order expansion of trace_quad c H at X. *)
Lemma trace_quad_expand c H S X :
  trace_quad c H S = trace_quad c H X +
    2 * mxdot (H - trace_scale c X) (S - X) -
    (mxdot (S - X) (S - X) + c / n%:R * \tr (S - X) ^+ 2).
Proof.
rewrite /trace_quad mxdotBl mxdot_trace_scalel !mxdotBr !mxdotBl !mxtraceB.
by rewrite (mxdotC X S); ring.
Qed.

End trace_scale.

Section trace_argmax.
Context {R : realType} {n : nat}.
Variable K : set 'M[R]_n.
Hypothesis Kc : closed [set v : 'rV[R]_(n * n) | K (vec_mx v)].
Hypothesis Kn : K !=set0.
Hypothesis Kcvx : forall (S T : 'M[R]_n) (t : R), K S -> K T -> 0 <= t <= 1 ->
  K (S + t *: (T - S)).
Variable c : R.
Hypothesis c1 : -1 < c.
Implicit Types (H S T X Y : 'M[R]_n).

Local Notation sc := (Num.sqrt (1 + c)).
Local Notation Uc := (trace_scale (sc - 1)).
Local Notation Vc := (trace_scale (sc^-1 - 1)).
Local Notation KU := [set v : 'rV[R]_(n * n) | K (Vc (vec_mx v))].
Local Notation Mv := (1%:M + ((sc^-1 - 1) / n%:R) *:
  ((mxvec (1%:M : 'M[R]_n))^T *m mxvec (1%:M : 'M[R]_n))).

Let sc_gt0 : 0 < sc.
Proof. by rewrite sqrtr_gt0; have := c1; lra. Qed.

Let UV S : Uc (Vc S) = S.
Proof.
rewrite trace_scaleK.
have -> : (1 + (sc - 1)) * (1 + (sc^-1 - 1)) - 1 = 0.
  by have s1 : sc != 0 := lt0r_neq0 sc_gt0; field.
exact: trace_scale_id.
Qed.

Let VU S : Vc (Uc S) = S.
Proof.
rewrite trace_scaleK.
have -> : (1 + (sc^-1 - 1)) * (1 + (sc - 1)) - 1 = 0.
  by have s1 : sc != 0 := lt0r_neq0 sc_gt0; field.
exact: trace_scale_id.
Qed.

Let UU S : Uc (Uc S) = trace_scale c S.
Proof.
rewrite trace_scaleK; congr trace_scale.
have h : sc ^+ 2 = 1 + c by rewrite sqr_sqrtr //; have := c1; lra.
by transitivity (sc ^+ 2 - 1); [ring | rewrite h; ring].
Qed.

Let mxdot_vecE (A B : 'M[R]_n) : mxdot (mxvec A) (mxvec B) = mxdot A B.
Proof.
rewrite /mxdot big_ord1 [in RHS]pair_bigA /=.
rewrite [in LHS](reindex (uncurry (@mxvec_index n n))) /=.
  exact: curry_mxvec_bij.
by apply: eq_bigr => -[i j] _; rewrite /= !mxvecE.
Qed.

Let mxtrace_vec_mx (v : 'rV[R]_(n * n)) :
  \tr (vec_mx v) = mxdot v (mxvec 1%:M).
Proof. by rewrite -mxdot1l -mxdot_vecE vec_mxK mxdotC. Qed.

(* In the coordinates of mxvec, Vc is the right multiplication by Mv. *)
Let Vvec (v : 'rV[R]_(n * n)) : mxvec (Vc (vec_mx v)) = v *m Mv.
Proof.
rewrite mulmxDr mulmx1 -scalemxAr mulmxA [v *m _^T]mx11_scalar.
rewrite mul_scalar_mx scalerA /trace_scale linearD linearZ /= vec_mxK.
by congr (_ + _ *: _); rewrite -mxdot_rowE mxtrace_vec_mx; ring.
Qed.

Let KU_closed : closed KU.
Proof.
have -> : KU = (fun v => v *m Mv) @^-1` [set v | K (vec_mx v)].
  by apply/seteqP; split => v; rewrite /= -Vvec mxvecK.
exact: (continuous_closedP _).1 (@continuous_mulmxr _ _ _ _ Mv) _ Kc.
Qed.

Let KU_n0 : KU !=set0.
Proof. by have [S KS] := Kn; exists (mxvec (Uc S)); rewrite /= mxvecK VU. Qed.

Let KU_convex (x y : 'rV[R]_(n * n)) (t : R) : KU x -> KU y -> 0 <= t <= 1 ->
  KU (x + t *: (y - x)).
Proof.
rewrite /= linearD linearZ linearB /= trace_scaleD trace_scaleZ trace_scaleB.
exact: Kcvx.
Qed.

(* The variational inequality of the projection, read on matrices. *)
Let vi_transfer H X S :
  mxdot (mxvec (Vc H) - mxvec (Uc X)) (mxvec (Uc S) - mxvec (Uc X)) =
  mxdot (H - trace_scale c X) (S - X).
Proof.
have e1 : mxvec (Vc H) - mxvec (Uc X) = mxvec (Vc H - Uc X).
  by rewrite linearB.
have e2 : mxvec (Uc S) - mxvec (Uc X) = mxvec (Uc (S - X)).
  by rewrite trace_scaleB linearB.
by rewrite e1 e2 mxdot_vecE -trace_scale_adj trace_scaleB UV UU.
Qed.

(* The maximizer is in K and satisfies the variational inequality
   <H - X - (c / n) tr(X) I, S - X> <= 0 for every S in K. *)
Theorem trace_argmaxP H : K (trace_argmax K c H) /\
  forall S, K S ->
    mxdot (H - trace_scale c (trace_argmax K c H)) (S - trace_argmax K c H)
      <= 0.
Proof.
have [Kp hp] := projP KU_closed KU_n0 KU_convex (mxvec (Vc H)).
rewrite /trace_argmax; move: (proj KU (mxvec (Vc H))) Kp hp => p Kp hp.
split => // S KS.
have pE : p = mxvec (Uc (Vc (vec_mx p))) by rewrite UV vec_mxK.
rewrite -vi_transfer -pE; apply: hp => /=.
by rewrite mxvecK VU.
Qed.

(* The variational inequality characterizes the maximizer. *)
Lemma trace_argmax_eq H Y : K Y ->
  (forall S, K S -> mxdot (H - trace_scale c Y) (S - Y) <= 0) ->
  trace_argmax K c H = Y.
Proof.
move=> KY hY.
have KUY : KU (mxvec (Uc Y)) by rewrite /= mxvecK VU.
have hvi y : KU y ->
    mxdot (mxvec (Vc H) - mxvec (Uc Y)) (y - mxvec (Uc Y)) <= 0.
  move=> /= Ky.
  have yE : y = mxvec (Uc (Vc (vec_mx y))) by rewrite UV vec_mxK.
  by rewrite [in Z in mxdot _ Z]yE vi_transfer; exact: hY.
have e := @proj_eq _ _ KU KU_closed KU_n0 KU_convex (mxvec (Vc H)) _ KUY hvi.
by rewrite /trace_argmax e mxvecK VU.
Qed.

(* The maximizer beats every point of K by min(1, 1 + c) |S - X|_F^2. *)
Lemma trace_argmax_ge H S : K S ->
  trace_quad c H S + Num.min 1 (1 + c) *
    mxdot (S - trace_argmax K c H) (S - trace_argmax K c H) <=
  trace_quad c H (trace_argmax K c H).
Proof.
move=> KS; have [KX hX] := trace_argmaxP H.
move: (trace_argmax K c H) KX hX => X KX hX.
rewrite (trace_quad_expand c H S X).
have := hX S KS; have := trace_pen_ge c (S - X).
lra.
Qed.

Lemma trace_argmax_unique H Y : K Y ->
  (forall S, K S -> trace_quad c H S <= trace_quad c H Y) ->
  trace_argmax K c H = Y.
Proof.
move=> KY hY; have [KX _] := trace_argmaxP H.
have h1 := trace_argmax_ge H KY; have h2 := hY _ KX.
move: (trace_argmax K c H) KX h1 h2 => X KX h1 h2.
have a0 : 0 < Num.min 1 (1 + c) by rewrite lt_min ltr01 /=; have := c1; lra.
have m0 : mxdot (Y - X) (Y - X) <= 0 by nra.
by apply/eqP; rewrite eq_sym -subr_eq0 -mxdot_eq0 eq_le m0 mxdot_ge0.
Qed.

Lemma trace_argmax_lipschitz H H' :
  frobenius (trace_argmax K c H - trace_argmax K c H') <=
  frobenius (H - H') / Num.min 1 (1 + c).
Proof.
have [KX hX] := trace_argmaxP H; have [KX' hX'] := trace_argmaxP H'.
move: (trace_argmax K c H) (trace_argmax K c H') KX hX KX' hX'.
move=> X X' KX hX KX' hX'.
have h1 := hX X' KX'; have h2 := hX' X KX.
have e : mxdot (H - trace_scale c X) (X' - X) +
    mxdot (H' - trace_scale c X') (X - X') =
    mxdot (X - X') (X - X') + c / n%:R * \tr (X - X') ^+ 2 -
    mxdot (H - H') (X - X').
  rewrite !mxdotBl !mxdot_trace_scalel !mxdotBr !mxtraceB (mxdotC X' X).
  by ring.
have key : Num.min 1 (1 + c) * mxdot (X - X') (X - X') <=
    frobenius (H - H') * frobenius (X - X').
  apply: le_trans (trace_pen_ge c (X - X')) _.
  apply: le_trans _ (ler_mxdot (H - H') (X - X')); lra.
have a0 : 0 < Num.min 1 (1 + c) by rewrite lt_min ltr01 /=; have := c1; lra.
have [->|D0] := eqVneq (X - X') 0.
  rewrite frobenius0; apply: divr_ge0; first exact: frobenius_ge0.
  exact: ltW a0.
have f0 : 0 < frobenius (X - X') by rewrite frobenius_gt0.
rewrite ler_pdivlMr // -(ler_pM2r f0).
by have := key; rewrite -frobenius_sqr; lra.
Qed.

Lemma trace_argmax0 : K 0 -> trace_argmax K c 0 = 0.
Proof.
move=> K0; apply: trace_argmax_eq => // S _.
by rewrite trace_scale0 subrr mxdot0l.
Qed.

Lemma trace_argmax_norm H : K 0 ->
  frobenius (trace_argmax K c H) <= frobenius H / Num.min 1 (1 + c).
Proof.
move=> K0; have := trace_argmax_lipschitz H 0.
by rewrite trace_argmax0 // !subr0.
Qed.

(* On a cone, the value of the maximum is <H, X>. *)
Lemma trace_argmax_cone H :
  (forall S (k : R), K S -> 0 <= k -> K (k *: S)) ->
  mxdot H (trace_argmax K c H) =
    mxdot (trace_argmax K c H) (trace_argmax K c H) +
    c / n%:R * \tr (trace_argmax K c H) ^+ 2 /\
  trace_quad c H (trace_argmax K c H) = mxdot H (trace_argmax K c H).
Proof.
move=> Kcone; have [KX hX] := trace_argmaxP H.
move: (trace_argmax K c H) KX hX => X KX hX.
have h0 := hX _ (Kcone X 0 KX (lexx 0)).
have h2 := hX _ (Kcone X 2 KX (ler0n _ 2)).
rewrite scale0r sub0r mxdotNr oppr_le0 in h0.
have e2 : 2 *: X - X = X by rewrite scaler_nat mulr2n addrK.
rewrite e2 in h2.
have e : mxdot (H - trace_scale c X) X =
    mxdot H X - (mxdot X X + c / n%:R * \tr X ^+ 2).
  by rewrite mxdotBl mxdot_trace_scalel; ring.
rewrite e in h0 h2.
have v : mxdot H X = mxdot X X + c / n%:R * \tr X ^+ 2 by lra.
by split => //; rewrite /trace_quad v; ring.
Qed.

(* Equivariance under the orthogonal conjugations, from uniqueness. *)
Lemma trace_argmax_conj H Q :
  (forall P S, P \is orthogonalmx -> K S -> K (P *m S *m P^T)) ->
  Q \is orthogonalmx ->
  trace_argmax K c (Q *m H *m Q^T) = Q *m trace_argmax K c H *m Q^T.
Proof.
move=> Kconj Qo; have [KX hX] := trace_argmaxP H.
move: (trace_argmax K c H) KX hX => X KX hX.
apply: trace_argmax_eq; first exact: Kconj Q X Qo KX.
move=> S KS; rewrite trace_scale_conj // -mulmxBl -mulmxBr.
have Qt : Q^T \is orthogonalmx by rewrite trmx_orthogonal.
have SE : S = Q *m (Q^T *m S *m Q) *m Q^T.
  by rewrite !mulmxA (orthogonalmxP _ Qo) mul1mx -mulmxA
    (orthogonalmxP _ Qo) mulmx1.
rewrite [in Z in mxdot _ Z]SE -mulmxBl -mulmxBr mxdot_conjmx //.
apply: hX; have := Kconj Q^T S Qt KS; by rewrite trmxK.
Qed.

End trace_argmax.
