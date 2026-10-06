(* Frobenius duality for the public symmetric matrices, in scalar form. *)
From Stdlib Require Import Reals List Lia Lra Psatz.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix normedtype.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From EllipsoidFitting Require Import Soft.Definitions Analysis.FiniteSumAlgebra
  PaperMainDefinitions Geometry.Psd Geometry.Homogeneous Gordon.Bilinear.
Import GRing.Theory Num.Theory.
Open Scope R_scope.

Lemma paper_main_frobenius_nonnegative d (T : 'M[R]_d) :
  0 <= paper_main_frobenius T.
Proof.
apply/RleP; apply sqrtr_ge0.
Qed.

Lemma paper_main_frobenius_squared d (T : 'M[R]_d) :
  (paper_main_frobenius T)^2 = paper_main_pairing T T.
Proof.
have H := sqr_sqrtr (paper_main_pairing_self_ge0 d T).
rewrite expr2 in H.
change (paper_main_frobenius T*paper_main_frobenius T = paper_main_pairing T T) in H.
nra.
Qed.
