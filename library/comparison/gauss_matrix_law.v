From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix.
From mathcomp Require Import boolp classical_sets functions reals ereal.
From mathcomp Require Import topology normedtype measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral probability.
From GaussianAnalysis.gaussian Require Import measurable_matrix gauss.
From GaussianAnalysis.probability Require Import lindeberg conditioning.

(**md**************************************************************************)
(* # Gaussian matrices from Gaussian rows                                     *)
(*                                                                            *)
(* A Gaussian matrix of size n x m is vec_mx a for a of law gauss (n * m), as *)
(* in escape.v and cgmt.v. This file identifies two other descriptions of its *)
(* law.                                                                       *)
(*                                                                            *)
(* - gauss_tuple_mx: n independent rows of law gauss m, put in a matrix by    *)
(*   tuple_mx, give the same law: for X measurable,                           *)
(*   tuple_prod (fun=> gauss m) n (tuple_mx @^-1` X) is                       *)
(*   gauss (n * m) [set a | X (vec_mx a)].                                    *)
(* - gauss_trmx: the transpose of a Gaussian matrix of size n x m is a        *)
(*   Gaussian matrix of size m x n.                                           *)
(*                                                                            *)
(* Both follow from gauss_unique: the coordinates are permuted, and the laws  *)
(* agree on boxes by gauss_box and tuple_prod_box.                            *)
(*                                                                            *)
(* ```                                                                        *)
(*   tuple_mx t == the n x m matrix whose rows are the vectors of t           *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section gauss_matrix_law.
Context {R : realType}.
Local Notation N := (@normal_prob R 0 1).

(* The n x m matrix whose rows are the vectors of a tuple. *)
Definition tuple_mx n m (t : n.-tuple 'rV[R]_m) : 'M[R]_(n, m) :=
  \matrix_(i, j) tnth t i 0 j.

Lemma measurable_tuple_mx n m : measurable_fun setT (@tuple_mx n m).
Proof.
apply/measurable_fun_mxP => i j.
have -> : (fun t : n.-tuple 'rV[R]_m => tuple_mx t i j) =
    (fun t => tnth t i 0 j) by apply/funext => t; rewrite mxE.
have m1 : measurable_fun setT (fun v : 'rV[R]_m => v 0 j).
  exact: measurable_mxentry.
have m2 : measurable_fun setT (fun t : n.-tuple 'rV[R]_m => tnth t i).
  exact: measurable_tnth.
exact: measurableT_comp m1 m2.
Qed.

Lemma measurable_vec_mx n m : measurable_fun setT (@vec_mx R n m).
Proof.
apply/measurable_fun_mxP => i j.
have -> : (fun a : 'rV[R]_(n * m) => vec_mx a i j) =
    (fun a => a 0 (mxvec_index i j)) by apply/funext => a; rewrite mxE.
exact: measurable_mxentry.
Qed.

Lemma measurable_mxvec n m : measurable_fun setT (@mxvec R n m).
Proof.
apply/measurable_fun_mxP => i k; case/mxvec_indexP: k => a b.
have -> : (fun A : 'M[R]_(n, m) => mxvec A i (mxvec_index a b)) =
    (fun A => A a b) by apply/funext => A; rewrite ord1 mxvecE.
exact: measurable_mxentry.
Qed.

(* The inverse of mxvec_index. *)
Let unvec_ix n m (k : 'I_(n * m)) : 'I_n * 'I_m :=
  enum_val (cast_ord (esym (mxvec_cast n m)) k).

Let unvec_ixK n m (i : 'I_n) (j : 'I_m) :
  unvec_ix (mxvec_index i j) = (i, j).
Proof. by rewrite /unvec_ix /mxvec_index cast_ordK enum_rankK. Qed.

(* A product over the indices mxvec_index i j is a double product. *)
Lemma prod_mxvec n m (F : 'I_(n * m) -> \bar R) :
  (\prod_(k < n * m) F k = \prod_(i < n) \prod_(j < m) F (mxvec_index i j))%E.
Proof.
rewrite (reindex _ (curry_mxvec_bij n m)) /= [RHS]pair_big /=.
by apply: eq_bigr => -[i j] _.
Qed.

(* n independent Gaussian rows form a Gaussian matrix. *)
Theorem gauss_tuple_mx n m (X : set 'M[R]_(n, m)) : measurable X ->
  tuple_prod (fun=> gauss m) n (@tuple_mx n m @^-1` X) =
  gauss (n * m) [set a | X (vec_mx a)].
Proof.
move=> mX.
have mf : measurable_fun setT (fun t : n.-tuple 'rV[R]_m => mxvec (tuple_mx t)).
  have m1 := @measurable_mxvec n m; have m2 := @measurable_tuple_mx n m.
  exact: measurableT_comp m1 m2.
pose f : {mfun n.-tuple 'rV[R]_m >-> 'rV[R]_(n * m)} :=
  HB.pack (fun t => mxvec (tuple_mx t)) (isMeasurableFun.Build _ _ _ _ _ mf).
have mY : measurable [set a : 'rV[R]_(n * m) | X (vec_mx a)].
  by rewrite -[X in measurable X]setTI; exact: (@measurable_vec_mx n m).
suff hP : forall Y, measurable Y ->
    distribution (tuple_prod (fun=> gauss m) n) f Y = gauss (n * m) Y.
  rewrite -hP // /= /pushforward /=.
  by congr (tuple_prod _ _ _); apply/seteqP; split => t /=; rewrite mxvecK.
apply: gauss_unique => A mA.
change (tuple_prod (fun=> gauss m) n
  (f @^-1` [set x : 'rV[R]_(n * m) | forall k, A k (x 0 k)]) =
  (\prod_(k < n * m) N (A k))%E).
have -> : f @^-1` [set x : 'rV[R]_(n * m) | forall k, A k (x 0 k)] =
    tuple_box (fun i => [set v : 'rV[R]_m |
      forall j, A (mxvec_index i j) (v 0 j)]).
  apply/seteqP; split => t /= h.
    by move=> i j; have := h (mxvec_index i j); rewrite mxvecE mxE.
  by move=> k; case/mxvec_indexP: k => i j; rewrite mxvecE mxE; exact: h.
have mside (i : 'I_n) : measurable [set v : 'rV[R]_m |
    forall j, A (mxvec_index i j) (v 0 j)].
  by apply: (@measurable_rowbox _ R m (fun j => A (mxvec_index i j))) => j.
rewrite (tuple_prod_box _ mside) prod_mxvec; apply: eq_bigr => i _.
by apply: (@gauss_box R m (fun j => A (mxvec_index i j))) => j.
Qed.

(* The transpose of a Gaussian matrix is a Gaussian matrix. *)
Theorem gauss_trmx n m (X : set 'M[R]_(m, n)) : measurable X ->
  gauss (n * m) [set a | X (vec_mx a)^T] = gauss (m * n) [set b | X (vec_mx b)].
Proof.
move=> mX.
have mf : measurable_fun setT
    (fun a : 'rV[R]_(n * m) => mxvec (vec_mx a : 'M[R]_(n, m))^T).
  have m1 : measurable_fun setT
      (fun a : 'rV[R]_(n * m) => (vec_mx a : 'M[R]_(n, m))^T).
    apply/measurable_fun_mxP => i j.
    have -> : (fun a : 'rV[R]_(n * m) => (vec_mx a : 'M[R]_(n, m))^T i j) =
        (fun a => a 0 (mxvec_index j i)) by apply/funext => a; rewrite !mxE.
    exact: measurable_mxentry.
  have m2 := @measurable_mxvec m n.
  exact: measurableT_comp m2 m1.
pose f : {mfun 'rV[R]_(n * m) >-> 'rV[R]_(m * n)} :=
  HB.pack (fun a : 'rV[R]_(n * m) => mxvec (vec_mx a : 'M[R]_(n, m))^T)
    (isMeasurableFun.Build _ _ _ _ _ mf).
have mY : measurable [set b : 'rV[R]_(m * n) | X (vec_mx b)].
  by rewrite -[X in measurable X]setTI; exact: (@measurable_vec_mx m n).
suff hP : forall Y, measurable Y ->
    distribution (gauss (n * m)) f Y = gauss (m * n) Y.
  rewrite -hP // /= /pushforward /=.
  by congr (gauss _ _); apply/seteqP; split => a /=; rewrite mxvecK.
apply: gauss_unique => A mA.
change (gauss (n * m)
  (f @^-1` [set x : 'rV[R]_(m * n) | forall k, A k (x 0 k)]) =
  (\prod_(k < m * n) N (A k))%E).
pose B (k : 'I_(n * m)) := A (mxvec_index (unvec_ix k).2 (unvec_ix k).1).
have -> : f @^-1` [set x : 'rV[R]_(m * n) | forall k, A k (x 0 k)] =
    [set a : 'rV[R]_(n * m) | forall k, B k (a 0 k)].
  apply/seteqP; split => a /= h k.
    case/mxvec_indexP: k => i j; rewrite /B unvec_ixK /=.
    by have := h (mxvec_index j i); rewrite mxvecE !mxE.
  case/mxvec_indexP: k => j i; rewrite mxvecE !mxE.
  by have := h (mxvec_index i j); rewrite /B unvec_ixK.
have mB : forall k, measurable (B k) by move=> k; exact: mA.
rewrite (@gauss_box R (n * m) B mB).
rewrite prod_mxvec [RHS]prod_mxvec exchange_big /=.
by apply: eq_bigr => i _; apply: eq_bigr => j _; rewrite /B unvec_ixK.
Qed.

End gauss_matrix_law.
