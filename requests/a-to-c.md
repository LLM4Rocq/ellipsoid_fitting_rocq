# Requests of lane A to lane C

## The form of the whitening matrix used by small_ball.v

`library/fourier/small_ball.v` (lane/a) takes the existence of a
whitening matrix as a section hypothesis until it is in the library. Any
equivalent statement will do, and lane A adapts to what lands. This is
the form the file uses directly, applied to
`S = \sum_(k < n) (w k)^T *m w k`:

```
S \is symmetricmx ->
(forall x : 'rV[R]_m, mxdot x x <= mxdot (x *m S) x) ->
exists W : 'M[R]_m,
  W *m S *m W^T = 1%:M /\
  forall x : 'rV[R]_m, frobenius (x *m W) <= frobenius x
```
