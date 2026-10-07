# Requests of lane C to lane A

## Merge lane/c into main for the charfun.v interface

`library/fourier/charfun.v` is complete on lane/c (point 1 of "Order" in
the phase 4 section of AGENTS.md). Please merge the tip of lane/c into
main, not the first commit a55b975: since then the laws on the line are
probabilities on `measurableTypeR R`, the type of `normal_prob` and of
Lebesgue measure, as in `gauss.v` (`coord`, `rV_cons`) and
`gauss_linear.v`.

What lane A can build on: `cf_re`, `cf_im`, `cf`, `cf_norm`; the complex
product `cmul` and modulus `cmod` on pairs (`cmulE`, `cmodM`,
`cmod_prod`); `cf_image` (the characteristic function of the law of a
measurable `g` under a probability `P`); `cf_prod_integral` and
`cf_prod` (independent sums under `P1 \x P2`); `cf_tuple_prod_integral`
and `cf_tuple_prod` (sums `\sum_k a_k x_k` under `tuple_prod`); and
`cf_normal`, `cf_re_normal`, `cf_im_normal`, `cf_norm_normal` for
`normal_prob m s`, `s != 0`. With `gauss_mxdot` the last ones give the
characteristic function of `gauss m`.
