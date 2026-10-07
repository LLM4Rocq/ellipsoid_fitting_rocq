# Requests of lane C to lane A

## Two corollaries of the vector small-ball estimate, after the Brascamp-Lieb swap

Sections 2 and 3 of `reviews/phase4-small-ball-statement-review.md` list two generalizations that the paper's statement and its proof allow but `fourier/small_ball.v` does not state. Lane C has added what they need to `fourier/gauss_factor.v` (lane/c e4f5427):
- `conc_fun_truncated_level_exists`: the first half of Lemma 3.5 for any truncation level `c`;
- `gauss_factor_center_exists`: Lemma 3.5 under `E[(X - a)^2] <= v`.

**Request.** Once `brascamp_lieb` comes from `comparison/brascamp_lieb_lebesgue.v`, please add the two theorems below to section `small_ball` of `fourier/small_ball.v`, with README rows.

**What was checked.** Both statements and proofs below compile in a scratch file on lane/c 316dcd9 (main 22f2942 merged in). The scratch file has the imports of small_ball.v, and a section with the hypothesis `brascamp_lieb` copied from small_ball.v. `Print Assumptions` lists only propositional extensionality, functional extensionality and constructive indefinite description.

### 1. Any truncation level (paper, line 942)

The paper says the constant `1/2` in its condition (910) may be any `c` in `(0, 1)`. The interval length then has to depend on `c`. For `c < 1/256`, a law with mass close to 1 at `+-1/16`, plus a small mass far away, satisfies the hypotheses and has `Q(mu, 1/8)` close to 1. So the proof takes the length `L = sqrt c / 4`, which satisfies `4 L^2 < c`.

Pitfall: apply `hC` to all of `m n mu w z rho eta`. With `apply: hC => //`, `rho` does not occur in the conclusion, so `//` instantiates it to `1` while proving `0 < rho`.

```
(* The vector small-ball estimate for laws of mean zero and variance one
   with E[x^2 1_{|x| <= M}] >= c, for any level c > 0. *)
Theorem vector_small_ball_moments_level (M c : R) : 0 < M -> 0 < c ->
  exists2 C : R, 0 < C &
  forall m n (mu : nat -> probability (measurableTypeR R) R)
      (w : nat -> 'rV[R]_m) (z : 'rV[R]_m) (rho eta : R),
    (forall k, (k < n)%N -> (\int[mu k]_x x%:E = 0)%E) ->
    (forall k, (k < n)%N -> (\int[mu k]_x ((x ^+ 2)%R)%:E = 1)%E) ->
    (forall k, (k < n)%N -> (c%:E <=
       \int[mu k]_x ((x ^+ 2 * \1_[set y | `|y| <= M] x)%R)%:E)%E) ->
    (forall x : 'rV[R]_m, mxdot x x <= \sum_(k < n) mxdot x (w k) ^+ 2) ->
    0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) ->
    C * rho <= eta ->
    (tuple_prod mu n [set x |
       (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
        eta * Num.sqrt m%:R)%R] <= ((C * eta) ^+ m)%:E)%E.
Proof.
move=> M0 c0.
pose L := Num.sqrt c / 4.
have L0 : 0 < L by rewrite divr_gt0// sqrtr_gt0.
have Lc : 4 * L ^+ 2 < c.
  rewrite /L expr_div_n sqr_sqrtr ?ltW//.
  have -> : 4 * (c / 4 ^+ 2) = c / 4 :> R by field.
  lra.
have [k k0 hk] := conc_fun_truncated_level_exists M0 L0 Lc.
have [C C0 hC] := @vector_small_ball R brascamp_lieb 1 L k ltr01 L0 k0.
exists C => // m n mu w z rho eta h0 h1 h2 hS rho0 wrho hK.
apply: (hC m n mu w z rho eta) => //.
- by move=> k' kn; rewrite (h1 k' kn).
- by move=> k' kn; exact: (hk (mu k') (h0 k' kn) (h1 k' kn) (h2 k' kn)).
Qed.
```

Once the hypothesis is gone, `@vector_small_ball R brascamp_lieb 1 L k` becomes `@vector_small_ball R 1 L k`.

### 2. The variance form

The hypothesis `E[x^2] <= v` becomes `E[(x - a_k)^2] <= v` for arbitrary centers `a_k`. With `a_k` the mean of `mu k`, this is `Var(mu k) <= v`.

The route needs no translation of the laws and no image of `tuple_prod`. The second moment enters the proof only through `E[(X - X')^2] <= 4 v` for the symmetrized law, and `E[(X - X')^2] <= 4 E[(X - a)^2]` for every `a` (`sym_second_moment_center`, esseen.v). So the proof is the proof of `vector_small_ball` with `gauss_factor_center_exists` in place of `gauss_factor_exists`, and the constant is the same.

```
(* The vector small-ball estimate under E[(x - a_k)^2] <= v, for instance
   the variance when a_k is the mean of mu k. *)
Theorem vector_small_ball_variance (v lambda eps : R) :
  0 < v -> 0 < lambda -> 0 < eps ->
  exists2 C : R, 0 < C &
  forall m n (mu : nat -> probability (measurableTypeR R) R) (a : nat -> R)
      (w : nat -> 'rV[R]_m) (z : 'rV[R]_m) (rho eta : R),
    (forall k, (k < n)%N ->
       (\int[mu k]_x (((x - a k) ^+ 2)%R)%:E <= v%:E)%E) ->
    (forall k, (k < n)%N -> conc_fun (mu k) lambda <= 1 - eps) ->
    (forall x : 'rV[R]_m, mxdot x x <= \sum_(k < n) mxdot x (w k) ^+ 2) ->
    0 < rho -> (forall k, (k < n)%N -> frobenius (w k) <= rho) ->
    C * rho <= eta ->
    (tuple_prod mu n [set x |
       (frobenius (\sum_(k < n) tnth x k *: w k - z) <=
        eta * Num.sqrt m%:R)%R] <= ((C * eta) ^+ m)%:E)%E.
Proof.
move=> v0 l0 e0.
have [C C0 hC] := @gauss_factor_center_exists R v lambda eps v0 l0 e0.
exists (maxr 2 (Num.sqrt (8 * expR 1 / pi) * C)).
  by rewrite lt_max ltr0n.
move=> m n mu a w z rho eta hv hl hS rho0 wrho hK.
pose S := \sum_(k < n) (w k)^T *m w k.
have Ssym : S \is symmetricmx.
  apply/symmetricmxP; rewrite /S linear_sum /=; apply: eq_bigr => k _.
  by rewrite trmx_mul trmxK.
have SI (x : 'rV[R]_m) : mxdot x x <= mxdot (x *m S) x.
  have -> : mxdot (x *m S) x = \sum_(k < n) mxdot x (w k) ^+ 2.
    rewrite /S mulmx_sumr mxdot_suml; apply: eq_bigr => k _.
    by rewrite mulmx_outer_rV mxdotZl mxdotC expr2.
  exact: hS.
have [W [hW cW]] := whitening_exists Ssym SI.
apply: (@vector_small_ball_fourier R brascamp_lieb m mu n w W z rho eta C
  hW cW rho0 wrho C0 _ hK).
move=> k r s kn hr hs.
exact: (hC (mu k) (a k) r s (hv k kn) (hl k kn) hr hs).
Qed.
```

As in theorem 1, drop the argument `brascamp_lieb` once the hypothesis is gone. `vector_small_ball` itself could then be stated as the case `a = 0`, but it can also stay as it is.
