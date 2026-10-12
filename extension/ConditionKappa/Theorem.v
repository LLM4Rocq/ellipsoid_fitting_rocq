(* The threshold and the optimal condition number at fourth moment kappa,
   for finite mixtures of product laws, at Stdlib's R: item A1 of phase 11
   (notes/phase11-plan.md, sections 3.4, 5 and 6; lane C). The model is
   Condition/Theorem.v, which treats kappa = 3.

   Results to prove here.
   - (20) at kappa: for K > 0, kappa > 1, C > 1 and alpha > 0, the
     conditioned fit event is measurable, and its probability tends to 1
     if alpha < alpha(C, kappa) (item D1, Sat) and to 0 if
     alpha(C, kappa) < alpha (item D2, Unsat).
   - (21) at kappa, from (20), as condition_number_of_threshold does at
     kappa = 3: for 0 < alpha < alpha*(kappa) and C_star = C_star(alpha,
     kappa), (20) at C_star + eps / 2 and at a point between 1 and C_star
     puts the optimal condition number (data_condition_number, measurable
     by measurable_data_condition_number of Condition/Theorem.v) within eps
     of C_star outside a measurable set of small probability.

   Interface used: I3, from item S3 (Curve, lane C): the analogue of
   condition_starP of Condition/Curve.v for C_star(alpha, kappa) on
   0 < alpha < alpha*(kappa): 1 < C_star, alpha(C_star, kappa) = alpha,
   alpha(C, kappa) < alpha for 1 < C < C_star, and
   alpha < alpha(C, kappa) for C_star < C. *)
