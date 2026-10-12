(* The root of the condition-number curve at fourth moment kappa, at
   Stdlib's R: item S1 of phase 11 (notes/phase11-plan.md, section 5; the
   math plan notes/general-fourth-moment-condition-plan.md, section 3, S1;
   lane C). The definitions are those of the definition file of phase 11,
   at the top of extension/.

   Setting. m and v are universality_m and universality_s, the upper
   moments of the semicircle law nu on [-sqrt 2, sqrt 2]. For kappa > 1 and
   C > 1, c = (kappa - 3) / 2 and r = c / (1 + c) = (kappa - 3) / (kappa - 1),
   so r < 1;
     L(u) = (u + r (C - 1)^2 m(u)) / C,    F(u) = m(-L(u)) - C m(u),
   the root u = sup {u in [0, sqrt 2] : F(u) <= 0} and ell = L(u).

   Results to prove here.
   - F is continuous and strictly increasing on [0, sqrt 2]. For u < v,
     with b = m(u) - m(v) > 0: if L(v) >= L(u), then F(v) - F(u) >= C b;
     otherwise the 1-Lipschitz property of m gives
     F(v) - F(u) >= (v - u) / C + (C - r (C - 1)^2 / C) b > 0.
   - F(0) < 0 < F(sqrt 2), in the two cases r >= 0 and r < 0.
   - u is the unique zero of F on [0, sqrt 2], and 0 < u < sqrt 2.
   - -sqrt 2 < ell < u. First m(-ell) = C m(u) > 0. If ell >= u, then,
     since m decreases and m(-ell) = m(ell) + ell,
     C m(u) = m(ell) + ell <= m(u) + ell, so (C - 1) m(u) <= ell and
     C ell - u >= (C - 1) ell >= (C - 1)^2 m(u), against
     C ell - u = r (C - 1)^2 m(u), since r < 1 and m(u) > 0. *)
