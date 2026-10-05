(* Countable unions of measurable sets of samples and rational approximation,
   for the measurability conjuncts of paper_main_results. Internal proof
   module of the MathComp-Analysis port, written on 30 September 2026 by a
   Claude Code session (Fable 5.1). Nothing here is reviewed or accepted.

   Unions over a countable type (countable_bigcupT_measurable of
   MathComp-Analysis with countableP for a countType) and intersections over
   nat (bigcap_measurable); a set defined by a constant proposition and a
   measurable condition; rational approximation of a real (rat_in_itvoo), of
   a real matrix entrywise, and of a symmetric real matrix by a symmetric
   rational matrix, with the choice made by cid of boolp. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum interval matrix rat.
From mathcomp Require Import boolp classical_sets reals Rstruct.
From mathcomp Require Import topology normedtype Rstruct_topology.
From mathcomp Require Import ereal measure lebesgue_measure measurable_realfun lebesgue_integral.
From mathcomp Require Import probability normal_distribution.
From EllipsoidFitting Require Import GaussianProbabilityProductDefinitions PaperMainDefinitions.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section countable_unions.
Variables (n d : nat).
Local Notation T := (paper_main_sample n d).

Lemma pm_bigcup_measurable (U : countType) (F : U -> set T) :
  (forall i, measurable (F i)) -> measurable (\bigcup_i F i).
Proof. by move=> mF; apply: countable_bigcupT_measurable => //; exact: countableP. Qed.

Lemma pm_bigcap_measurable (F : nat -> set T) :
  (forall k, measurable (F k)) -> measurable (\bigcap_k F k).
Proof. by move=> mF; apply: bigcap_measurable => //; exists 0%nat. Qed.

(* A set cut down by a constant proposition. *)
Lemma pm_measurable_guard (P : Prop) (A : set T) :
  measurable A -> measurable [set x | P /\ A x].
Proof.
move=> mA; have [HP|HP] := pselect P.
- by rewrite (_ : [set x | P /\ A x] = A)//; apply/seteqP; split=> x /=; [case|split].
- by rewrite (_ : [set x | P /\ A x] = set0)//; apply/seteqP; split=> x //= [].
Qed.

End countable_unions.

(* Rational approximation. *)
Lemma pm_rat_approx (x eps : R) : 0 < eps -> exists q : rat, `|x - ratr q| < eps.
Proof.
move=> eps0.
have xe : x - eps < x + eps by rewrite ltrBlDr -addrA ltrDl addr_gt0.
have [q] := rat_in_itvoo xe; rewrite in_itv/= => /andP[Hq1 Hq2].
exists q; rewrite ltr_norml; apply/andP; split.
- by rewrite ltrBrDl ltrBlDr.
- by rewrite ltrBlDr addrC -ltrBlDr.
Qed.

Lemma pm_rat_matrix_approx (m : nat) (S : 'M[R]_m) (eps : R) :
  0 < eps -> exists q : 'M[rat]_m, forall i j, `|S i j - ratr (q i j)| < eps.
Proof.
move=> eps0.
exists (\matrix_(i, j) sval (cid (pm_rat_approx (S i j) eps eps0))) => i j.
by rewrite mxE; exact: (svalP (cid (pm_rat_approx (S i j) eps eps0))).
Qed.

(* A symmetric real matrix is approximated by a symmetric rational matrix:
   approximate the entries and mirror the upper triangle. *)
Lemma pm_rat_sym_approx (m : nat) (S : 'M[R]_m) (eps : R) :
  0 < eps -> paper_main_symmetric S ->
  exists q : 'M[rat]_m, (forall i j, q i j = q j i) /\ forall i j, `|S i j - ratr (q i j)| < eps.
Proof.
move=> eps0 Ssym.
have [q Hq] := pm_rat_matrix_approx _ S eps eps0.
exists (\matrix_(i, j) (if (i <= j)%nat then q i j else q j i)); split=> i j; rewrite !mxE.
- case: (leqP i j) => ij; case: (leqP j i) => ji //.
  + by have -> : i = j by apply/val_inj/eqP; rewrite eqn_leq ij ji.
  + by move: (ltn_trans ij ji); rewrite ltnn.
- by case: (leqP i j) => ij; [exact: Hq|rewrite Ssym; exact: Hq].
Qed.
