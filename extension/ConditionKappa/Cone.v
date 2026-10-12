(* The transformed cone of bounded condition number and its support
   function, at Stdlib's R: item B1 of phase 11 (notes/phase11-plan.md,
   sections 5 and 6, interface I1; the math plan
   notes/general-fourth-moment-condition-plan.md, section 4.1; lane B).

   This file holds the single shared definition of the cone T K_C, of its
   base and of its support function. Items M5 (lane A) and G1 (lane B)
   import it.

   Setting. kappa > 1, c = (kappa - 3) / 2 > -1 and a0 = min(1, 1 + c).
   For C > 1, K_C = cond_cone C and cond_slice C, its slice of trace d
   (library/matrix/condition_cone.v). T = cone_map kappa (Gaussian/Cones.v)
   multiplies the diagonal by sqrt (1 + c) = sqrt ((kappa - 1) / 2); it is
   invertible (cone_mapK, cone_mapVK). The condition number of a matrix of
   T K_C is measured on S, before T.

   Results to prove here.
   - T K_C is a closed convex cone of vectors, in the mxvec coordinates of
     cond_cone_vec, and in the transposed form tr_set of
     library/comparison/cgmt.v that library/comparison/cone_escape.v takes.
   - Its base, T of the trace-d slice, is closed, convex, nonempty for
     d > 0 and inside the cone, and every nonzero element of the cone is a
     positive multiple of an element of the base.
   - On the base, sqrt (a0 d) <= |T S|_F <= sqrt (max(1, 1 + c) C d).
   - The support function of interface I1,
       sigma_{C,kappa}(A) = sup { <A, T S> : S in K_C, |T S|_F <= 1 },
     with the unit ball after T: cone_sup of cone_escape.v for this cone.
     Its limit, sigma_{C,kappa} / d -> sqrt alpha(C, kappa) in probability
     under gauss (d * d), is item M5 (lane A).
   These are the analogues for T K_C of cond_K0 to cond_cone_supE of
   Condition/GaussianWitness.v, which treats kappa = 3. *)
