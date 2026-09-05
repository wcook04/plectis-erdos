# Erdős #243: negative-feedback descent probe

The exact negative-to-negative feedback law is a centered Euclidean division,
but it is not a descent law for the negative magnitude.  The smallest durable
normalized counterexample used here is

```text
(u,v)=(6,11), (a,m)=(3,1), h=1
(u',v')=(7,33), (a',m')=(6,2)
```

Both pairs are primitive, both errors are strictly centered and negative, the
multiplier increases, and the exact transport equations hold.  Nevertheless
`m' >= m` and `m'/u' = 2/7 > 1/6 = m/u`.  Lean checks this witness as
`negativeFeedback_normalizedDescent_counterexample`.

The stronger exact seed

```text
(u,v)=(9,62), (a,m,h)=(8,1,2)
(u',v')=(5,248), (a',m')=(51,2)
```

kills the entire nonnegative homogeneous family at once.  The negative mass
doubles while the primitive scale falls from `9` to `5`.  Hence, for every
real `alpha>=0`,

`m'/(u')^alpha > m/u^alpha`.

This is not a numerical optimization over exponents; the two exact monotonic
inequalities make every exponent fail simultaneously.

`scripts/check_erdos243_negative_feedback_descent.py` replays the exact map on
a bounded primitive census and verifies the analytic identity
`A*m = k*u' + m'` from `negativeFeedback_centeredQuotient` on every retained
step.  Its bound is a regression surface, not evidence for an infinite orbit.
The one-way conclusion comes from the explicit witnesses: any surviving proof
must use multi-step cancellation payments, residue compatibility,
nonhomogeneous source data, or global prefix coherence rather than any
one-step weight `m/u^alpha` with `alpha>=0`.
