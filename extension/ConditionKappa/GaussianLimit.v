(* The Gaussian limit at fourth moment kappa, at Stdlib's R: items M3, M4
   and M5 of phase 11 (notes/phase11-plan.md, sections 3.3, 5 and 6; the
   math plan notes/general-fourth-moment-condition-plan.md, sections 4.3
   and 4.4; reviews/phase11-plan-review.md, sections 2.3 and 2.4; lane A).

   Setting as in Geometry: kappa > 1, c = (kappa - 3) / 2, a0 = min(1, 1 + c),
   C > 1, K_C = cond_cone C, T = cone_map kappa. a has law gauss (d * d),
   G = goe_part (vec_mx a) (diagonal variance 1, off-diagonal variance 1/2),
   H = G / sqrt d, and W = goe_mx a = sqrt 2 H, of spectral edge 2. X(H) is
   the maximizer of the surrogate objective Phi-bar_H on K_C (item M1).

   Results to prove here.
   - M3. diag_var X(H) -> 0 in probability (goe_diag_var_tail of
     library/random_matrix/goe_rotation.v with F(W) = X(W / sqrt 2));
     |diag H|_F^2 is bounded in probability, so
     |tr H| / d <= |diag H|_F / sqrt d -> 0; and, with item M2,
     (max_K Phi_H - max_K Phi-bar_H) / d -> 0 in probability.
   - M4. (1/d) max_K Phi-bar_H -> alpha(C, kappa) in probability. The route
     is section 3.3 of the plan: the duality in mu,
       max_K Phi-bar_H = opt_mu (|Pi_K(H - c mu I)|_F^2 + c d mu^2),
     a maximum for c < 0 and a minimum for c > 0, attained at
     mu = tr(X) / d (mu = 0 at c = 0); the windows 0 <= mu <= M = 3 / a0
     and 0 <= t <= B = 3 + |c| M on the event |W|_op <= 3, for the random
     and for the limiting optimizers; the three limits, uniform in mu in
     [0, M]: the trace term 2 c mu tr(H) / d, |H|_F^2 / d -> 1/2
     (goe_sqnorm_half of Condition/GaussianCone.v), and the shifted
     clipping energy (1/d) inf_t sum_i dist(lambda_i(H) - c mu, [t, C t])^2
     (wigner_uniform_inf on [0, B] at the points of a net in mu, and a
     Lipschitz bound in mu); and the identification of the limit by
     interface I2.
   - M5. |Pi_{T K_C} G|_F^2 = d max_K Phi_H, and interface I1 below.

   Interface I2 (from item S2, Curve, lane C; used by M4). With
   c = (kappa - 3) / 2, condition_kappa_dual C kappa mu of Curve is
     1/2 + c (1 + c) mu^2 - inf_(t >= 0) (v(-t - c mu) + v(C t + c mu)),
   the limit of (1/d) (|Pi_K(H - c mu I)|_F^2 + c d mu^2). Item S2 proves,
   for C > 1 and kappa > 1: some mu* with 0 <= mu* <= 1 / (sqrt 2 a0) <= M
   and condition_kappa_dual C kappa mu* = condition_kappa_alpha C kappa;
   if kappa <= 3, condition_kappa_dual C kappa mu <= condition_kappa_alpha
   C kappa for every mu; if 3 <= kappa, condition_kappa_alpha C kappa <=
   condition_kappa_dual C kappa mu for every mu. Until S2 lands, M4 may take
   these three facts as hypotheses.

   Interface I1 (the output of M5; used by item G1, GaussianWitness and
   GaussianGap, lane B). sigma_{C,kappa} is the support function of Cone
   (item B1, lane B),
     sigma_{C,kappa}(A) = sup { <A, T S> : S in K_C, |T S|_F <= 1 },
   with the unit ball after T. M5 proves, for C > 1 and kappa > 1,
     cvg_prob (fun d => gauss (d * d))
       (fun d a => sigma_{C,kappa}(vec_mx a) / d)
       (sqrt (condition_kappa_alpha C kappa)),
   the hypothesis hQ2 of Condition/GaussianWitness.v with sigma_{C,kappa}
   in place of cond_support C and alpha(C, kappa) in place of
   condition_alpha C. Since sigma_{C,kappa}(A) = |Pi_{T K_C}(A)|_F for the
   closed convex cone T K_C, this is M3, M4 and the identity of M5. *)
