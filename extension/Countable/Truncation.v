(* The truncation of a countable mixture of product laws to a finite one,
   and the coupling of their samples, at Stdlib's R: item K2 of phase 8
   (notes/three-extensions-plan.md, sections 1.3 and 5.2; lane A). The
   definitions are those of CountableMixtureDefinitions and
   MixtureDefinitions; the general facts on countable mixtures of laws and
   on label sums are those of item L1, a new file of library/probability.

   Results to prove here, for a family with countable_mixture_family K w mu.
   - For every d, a cutoff m_d with tail mass
     r_d = sum_(s > m_d) w d s <= (d + 1)^-3 (the series of the weights
     converges).
   - The truncated finite family: N' d = m_d + 2 components, the
     components s <= m_d with their weights and laws, and the component
     m_d + 1 of weight r_d whose coordinate j has the law
     sum_(s > m_d) w d s mu d s j / r_d (any component law of the family
     when r_d = 0). It satisfies mixture_family K N' w' mu', and
     mixture_fourth_moment kappa N' w' mu' when
     countable_fourth_moment kappa w mu holds, since the coordinate
     marginals do not change.
   - The label coupling: for every measurable set E of samples of n
     points,
       |countable_mixture_probability (w d) (mu d) n d E
        - mixture_probability (N' d) (w' d) (mu' d) n d E|
       <= 1 - (1 - r_d)^n <= n r_d. *)
