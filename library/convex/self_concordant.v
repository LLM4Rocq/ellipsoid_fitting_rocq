From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun exp.
From GaussianAnalysis Require Import euclidean.

(**md**************************************************************************)
(* # Self-concordant functions and barriers                                   *)
(*                                                                            *)
(* Self-concordant functions and barriers in the sense of Nesterov and        *)
(* Nemirovskii (Interior-point polynomial algorithms, Definition 2.3.1), on a *)
(* convex set D of 'rV[R]_N that is open in its affine hull z + V, with V a   *)
(* subspace. Derivatives are taken along the directions h of V, with          *)
(* MathComp's directional derivative 'D_h. A self-concordant function is      *)
(* convex, three times differentiable along V, its first and second           *)
(* derivatives are a linear and a quadratic form, it tends to +oo at the      *)
(* relative boundary of D, and                                                *)
(*   (SC)  |D^3 B(z)[h, h, h]| <= 2 (D^2 B(z)[h, h])^(3/2),                   *)
(* written (D^3 B(z)[h, h, h])^2 <= 4 (D^2 B(z)[h, h])^3. A theta-self-       *)
(* concordant barrier satisfies moreover                                      *)
(*   (BP)  (D B(z)[h])^2 <= theta D^2 B(z)[h, h].                             *)
(* These are the notions of Koehler and Sohn, Universality and sharp          *)
(* thresholds for ellipsoid fitting (arXiv 2608.27372), Definition 2.7.       *)
(*                                                                            *)
(* ```                                                                        *)
(*    rel_open_convex V D == D is convex, y - z is in V for y, z in D, and    *)
(*                           around each z of D, D contains the points z + h  *)
(*                           with h in V and `|h| < e for some e > 0: D is    *)
(*                           relatively open in its affine hull z + V         *)
(*      sc_function V D B == B is a self-concordant function on D with        *)
(*                           directions V: three times differentiable along   *)
(*                           V, with a gradient vector and a Hessian matrix,  *)
(*                           convex, (SC), and B (z + t h) tends to +oo when  *)
(*                           t tends to 1 from the left, if z + t h is in D   *)
(*                           for 0 <= t < 1 and z + h is not                  *)
(* sc_barrier V D theta B == B is a theta-self-concordant barrier: a          *)
(*                           self-concordant function with (BP)               *)
(*          sc_norm B z h == the local norm sqrt (D^2 B(z)[h, h])             *)
(*      bregman_div B y z == the Bregman divergence B y - B z - D B(z)[y - z] *)
(*             sc_omega r == r - ln (1 + r)                                   *)
(*        sc_omega_star r == - r - ln (1 - r)                                 *)
(* ```                                                                        *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5), for z in D, h in V and               *)
(* r = sc_norm B z h:                                                         *)
(* - B is convex on D, and continuous on D (within D).                        *)
(* - For t >= 0 with z + t h in D, r^2 / (1 + t r)^2 <= D^2 B(z + t h)[h, h], *)
(*   and D^2 B(z + t h)[h, h] <= r^2 / (1 - t r)^2 when moreover t r < 1      *)
(*   (Koehler-Sohn, proof of Lemma 2.15).                                     *)
(* - The Dikin ellipsoid: if r < 1, then z + h is in D (Nesterov-Nemirovskii  *)
(*   Theorem 2.1.1).                                                          *)
(* - sc_omega r <= bregman_div B (z + h) z when z + h is in D, and            *)
(*   bregman_div B (z + h) z <= sc_omega_star r when r < 1.                   *)
(* - Lemma 2.15 (i): if z + h is in D and bregman_div B (z + h) z is at most  *)
(*   sc_omega (1/2), then r <= 1/2 and r^2 / 3 <= bregman_div B (z + h) z.    *)
(* - Lemma 2.15 (ii): if r <= 1/2, then z + h is in D and                     *)
(*   |B (z + h) - B z - D B(z)[h] - r^2 / 2| <= 2 r^3 / 3.                    *)
(* - Lemma 2.10 (Nesterov Theorem 4.2.4): for a theta-self-concordant         *)
(*   barrier and y, z in D, D B(z)[y - z] <= theta; hence for x0, x in D and  *)
(*   0 < eps < 1, B ((1 - eps) x + eps x0) <= B x0 + theta ln (1 / eps).      *)
(* - The sum of a theta1- and a theta2-self-concordant barrier with the same  *)
(*   directions is a (theta1 + theta2)-self-concordant barrier on the         *)
(*   intersection of the domains, and the restriction of a                    *)
(*   theta-self-concordant barrier to the intersection of D with an affine    *)
(*   subspace z0 + V' of z0 + V is one with directions V'                     *)
(*   (Nesterov-Nemirovskii Proposition 2.3.1).                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section self_concordant_definitions.
Context {R : realType} {N : nat}.
Implicit Types (V : {vspace 'rV[R]_N}) (D : set 'rV[R]_N)
  (B : 'rV[R]_N -> R).

Definition rel_open_convex V D :=
  [/\ forall z y (t : R), D z -> D y -> 0 <= t <= 1 -> D (z + t *: (y - z)),
      forall z y, D z -> D y -> y - z \in V &
      forall z, D z -> exists2 e : R, 0 < e &
        forall h, h \in V -> `|h| < e -> D (z + h)].

Definition sc_function V D B :=
  [/\ forall z h, D z -> h \in V ->
        [/\ derivable B z h, derivable ('D_h B) z h &
            derivable ('D_h ('D_h B)) z h],
      forall z, D z -> exists (g : 'rV[R]_N) (M : 'M[R]_N),
        forall h, h \in V ->
          'D_h B z = mxdot g h /\ 'D_h ('D_h B) z = mxdot h (h *m M),
      forall z h, D z -> h \in V -> 0 <= 'D_h ('D_h B) z,
      forall z h, D z -> h \in V ->
        ('D_h ('D_h ('D_h B)) z) ^+ 2 <= 4%:R * ('D_h ('D_h B) z) ^+ 3 &
      forall z h, D z -> h \in V ->
        (forall t, 0 <= t < 1 -> D (z + t *: h)) -> ~ D (z + h) ->
        B (z + t *: h) @[t --> (1 : R)^'-] --> +oo].

Definition sc_barrier V D (theta : R) B :=
  sc_function V D B /\
  forall z h, D z -> h \in V -> ('D_h B z) ^+ 2 <= theta * 'D_h ('D_h B) z.

Definition sc_norm B (z h : 'rV[R]_N) : R := Num.sqrt ('D_h ('D_h B) z).

Definition bregman_div B (y z : 'rV[R]_N) : R := B y - B z - 'D_(y - z) B z.

Definition sc_omega (r : R) : R := r - ln (1 + r).

Definition sc_omega_star (r : R) : R := - r - ln (1 - r).

End self_concordant_definitions.
