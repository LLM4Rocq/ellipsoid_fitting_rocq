(* The surrogate maximizer and the deterministic comparison of the two
   Gaussian objectives, at Stdlib's R: items M1 and M2 of phase 11
   (notes/phase11-plan.md, sections 3.1, 3.3 and 5; the math plan
   notes/general-fourth-moment-condition-plan.md, sections 4.2 and 4.3;
   lane A).

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1, a0 = min(1, 1 + c) and
   e = sqrt (1 + c) - 1. For C > 1, K_C = cond_cone C
   (library/matrix/condition_cone.v): the symmetric d x d matrices S with
   t I <= S <= C t I for some t >= 0. T = cone_map kappa (Gaussian/Cones.v)
   multiplies the diagonal by sqrt (1 + c) = sqrt ((kappa - 1) / 2), and
   diag S = diag_part S. For a d x d matrix H,
     Phi_H(S)     = 2 <H, T S> - |S|_F^2 - c |diag S|_F^2,
     Phi-bar_H(S) = 2 <H, S> - |S|_F^2 - (c / d) (tr S)^2.

   Results to prove here.
   - M1. Phi-bar_H has a unique maximizer X(H) on K_C. It satisfies the
     variational inequality
       <H - X - (c / d) tr(X) I, S - X> <= 0 for every S in K_C,
     |X|_F <= |H|_F / a0, and X is positive semidefinite. X is Lipschitz
     in H with constant 1 / a0, measurable, and X(P H P^T) = P X(H) P^T for
     every orthogonal P, by uniqueness: the hypotheses of goe_diag_var_tail
     (library/random_matrix/goe_rotation.v) for F(W) = X(W / sqrt 2).
     Route: U_c S = S + e (tr S / d) I is self-adjoint and invertible, with
     |U_c S|_F^2 = |S|_F^2 + (c / d) (tr S)^2, so X(H) is U_c^-1 of the
     projection (proj of library/convex/moreau.v) of U_c^-1 H onto the
     closed convex cone U_c K_C. U_c rescales the trace direction only; T
     rescales every diagonal entry. The general form, for a closed convex
     cone of matrices and every c > -1, is in a library module of lane A.
   - M2. With D = diag X - (tr X / d) I and E = e diag H - c D,
       Phi_H(S) - Phi_H(X) <= |E|_F^2 / a0 for every S in K_C,
     so 0 <= sup_(S in K_C) Phi_H(S) - Phi_H(X) <= |E|_F^2 / a0, and
       Phi_H(X) - Phi-bar_H(X) = 2 e <diag H, diag X> - c |D|_F^2,
     for every c > -1, both signs and c = 0. The proof expands Phi_H at X
     and uses the variational inequality, T H - H = e diag H and
     |h|_F^2 + c |diag h|_F^2 >= a0 |h|_F^2. *)
