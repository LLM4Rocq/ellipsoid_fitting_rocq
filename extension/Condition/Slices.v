(* The approximate fit on finitely many two-sided slices, at Stdlib's R:
   item Q6 of phase 8 (notes/three-extensions-plan.md, sections 2 and 5.2;
   lane A). It generalizes af_at_d of Sat/ApproximateFit.v, which keeps its
   name and statement, as approximate_fit_law does.

   Results to prove here, for the objective of the section sat_values of
   Sat/ApproximateFit.v on pd_slice2 d m M with fixed 0 < m < 1 < M (the
   square loss with an intercept, the ridge, and the barrier
   logdet_barrier2 with the weight gamma = 1 / (d sqrt d)), its value
   af_value and its Gaussian center af_center (the mean of af_value under
   the Gaussian features).
   - af_at_d from a bound af_center <= w on the Gaussian center, in place
     of an exact Gaussian witness, with constants and dimension thresholds
     explicit in m and M, so that they are uniform over finitely many
     slices.
   - The value at an approximate witness: for mxvec S in pd_slice2 d m M,
     af_value Z <= (1 / (2 n)) sum_i <Z_i, S>^2 + beta Mk M
     + gamma Bar (mxvec S).
   - af_center_le for finitely many slices j < J: if, outside a Gaussian
     event of probability at most 1/4, the value af_value of some slice is
     at most w, and the probabilities of af_conc of the J slices sum to at
     most 1/2, then some slice has af_center <= w + af_err + t (center and
     error of that slice). This gives a deterministic choice of the slice
     at each d.
   - The lower bound of a center: if af_value >= g outside a Gaussian
     event of probability at most 1/2, then af_center >= g / 2 (af_value
     is nonnegative, since the barrier is, sat_B0). *)
