(* The three main theorems of the paper: thm:main, thm:conditioned and
   cor:alternative, as stated in MainStatement. The proof is the theorem
   paper_main_results of PaperMainResults; the kernel checks that its type
   is main_statement. check/Assumptions.v prints the axioms it uses. *)
From EllipsoidFitting Require Import MainStatement PaperMainResults.

Theorem ellipsoid_fitting_main : main_statement.
Proof. exact paper_main_results. Qed.
