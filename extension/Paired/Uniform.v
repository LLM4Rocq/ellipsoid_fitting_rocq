(* The uniform law on [-sqrt 3, sqrt 3], the rescaled Legendre polynomial
   h(x) = P_4(x / sqrt 3), and the laws lam_a = (1 + a h) mu, at Stdlib's R:
   item P1 of phase 6 (notes/paired-law-plan-v2.md, section 4.3; lane B).
   The definitions are those of PairedDefinitions: paired_uniform_spec and
   paired_kernel.

   Results to prove here, for a law mu with paired_uniform_spec mu.
   - mu integrates as uniform_prob of MathComp-Analysis does
     (integral_uniform): int f dmu = int_{-sqrt 3}^{sqrt 3} f / (2 sqrt 3).
   - The moments: int x^a dmu for a <= 4 (0, 1, 0, 9/5), and
     int x^a h dmu = 0 for a <= 3, int x^4 h dmu = 8/35, int h dmu = 0
     (polynomials on an interval, by the fundamental theorem of calculus).
   - The range of h on the support: -3/7 <= h <= 1, from
     h + 3/7 = 5 (7 t^2 - 3)^2 / 56 and 1 - h = 5 (1 - t^2)(1 + 7 t^2) / 8,
     t = x / sqrt 3.
   - For -1 <= a <= 7/3, the law lam_a with density
     (1 + a h(x)) 1_(|x| <= sqrt 3) against mu (the laws given by a density
     of item L1, a new module of library/probability/; this density is
     nonnegative everywhere): a probability, of mean 0, variance 1 and
     fourth moment 9/5 + 8 a / 35, with values in [-sqrt 3, sqrt 3], hence
     a component law with constant 3 (mixture_component_law 3 of
     MixtureDefinitions, since E exp (x^2 / 9) <= exp (1/3) <= 2). *)
