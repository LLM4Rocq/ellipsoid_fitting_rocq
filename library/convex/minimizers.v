From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat ssralg ssrnum matrix vector.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun exp.
From GaussianAnalysis Require Import euclidean self_concordant least_squares.

(**md**************************************************************************)
(* # Minimizers of strongly convex functions with a barrier                   *)
(*                                                                            *)
(* The convex analysis that the Lindeberg argument of Koehler and Sohn        *)
(* (arXiv 2608.27372, Theorem 2.9) needs, for a function                      *)
(*   F (theta, b) = Q (theta, b) + gamma B theta                              *)
(* on D x R, where D is relatively open and convex with directions V          *)
(* (rel_open_convex), B is a self-concordant function on D (sc_function),     *)
(* gamma > 0, and Q is a quadratic function of (theta, b) whose quadratic     *)
(* part is at least c (|theta|^2 + b^2) for some c > 0, such as the ridge     *)
(* regularized least squares objective ls_objective with beta > 0.            *)
(*                                                                            *)
(* Planned results (stage 1 of phase 5):                                      *)
(* - F attains its infimum on D x R at a unique point. The proof shows that   *)
(*   minimizing sequences are Cauchy (strong convexity) and that their limit  *)
(*   lies in D (the barrier tends to +oo at the relative boundary, and B is   *)
(*   continuous on D); D need not be bounded.                                 *)
(* - At the minimizer, the derivative of F along every direction (u, u_b) of  *)
(*   V x R is 0.                                                              *)
(* - Taylor's formula with the Bregman remainder: for the minimizer           *)
(*   xm = (thetam, bm) and u = (u, u_b) in V x R with thetam + u in D,        *)
(*   F (xm + u) - F xm = (1/2) H(u, u) + R(u), where H is the Hessian         *)
(*   quadratic form of F at xm and R(u) = gamma (B (thetam + u) - B thetam    *)
(*   - D B(thetam)[u] - (1/2) D^2 B(thetam)[u, u]) (paper, (2.17)-(2.18)).    *)
(* - The Bregman divergence of F dominates gamma times that of B, and at the  *)
(*   minimizer it is F (xm + u) - F xm.                                       *)
(* - The quadratic response: for a positive definite quadratic form H on      *)
(*   V x R (a matrix in a basis of V), a in V x R and n > 0, the infimum      *)
(*   over u of (1/2) H(u, u) + (r + <a, u>)^2 / (2 n) is r^2 / (2 (n + l))    *)
(*   with l = <a, H^-1 a>, attained at u = - (r / (n + l)) H^-1 a (paper,     *)
(*   (2.19)); l is a quadratic function of a whose matrix is H^-1.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
