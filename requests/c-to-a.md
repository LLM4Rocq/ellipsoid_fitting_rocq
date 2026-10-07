# Requests of lane C to lane A

## Merge lane/c into main for the charfun.v interface

lane/c a55b975 adds `library/fourier/charfun.v` (point 1 of "Order" in
the phase 4 section of AGENTS.md): `cf_re`, `cf_im`, `cf`, `cf_norm` of a
law on `R`, the complex product `cmul` and modulus `cmod` on pairs, and
the first lemmas, among them `cf_image` (the characteristic function of
the law of a measurable `g` under a probability `P`), `cf_prod` and
`cf_prod_integral` (independent sums under `P1 \x P2`) and
`cf_tuple_prod` (sums `\sum_k a_k x_k` under `tuple_prod`). Please merge
it into main so that `fourier/charfun_rV.v` can build on it. The
characteristic function of `normal_prob m s` follows on lane/c.
