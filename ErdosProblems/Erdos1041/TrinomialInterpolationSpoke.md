# Erdős #1041: endpoint-vanishing trinomial interpolation

Status: exact analytic certificate, Lean kernel, and deterministic numerical
replay, 2026-08-25. **This is not the unrestricted solution of Erdős #1041.**
It converts the remaining finite-mode competition into an explicit inequality
that vanishes at both endpoints of every candidate spoke.

## 1. Interpolate the actual polynomial, not its asymptotic model

Write the monic polynomial as

```text
f(z) = z^n + sum_(k=1)^(n-1) b_k z^k + c
```

and let `a != 0` be one of its roots. Choose an exponent `1 <= j < n` and put

```text
A_j a^j = sum_(k=1)^(n-1) b_k a^k = -(a^n+c),
g_j(z) = z^n + A_j z^j + c.
```

Then `g_j(0)=f(0)` and `g_j(a)=f(a)=0`. On the radial segment `z=t a`,
`0<=t<=1`, the root equation gives the exact two-term identity

```text
g_j(t a) = (1-t^j)c - (t^j-t^n)a^n.                    (I1)
```

No perturbative assumption is used. More importantly, subtraction gives

```text
f(t a)-g_j(t a)
  = sum_(k=1)^(n-1) b_k a^k (t^k-t^j).                 (I2)
```

Every discarded mode now vanishes at `t=0` and `t=1`. This is strictly better
for a full spoke than approximating by a homogeneous first nonzero mode, whose
error generally does not vanish at the root endpoint.

For `j=2` after critical-point normalization, this is the Abel-summation
mechanism already recorded in [GeneralSpokeIdentity.md](GeneralSpokeIdentity.md).
The content used here is its arbitrary-interpolation-exponent form and the
explicit slack comparison below; no priority claim is made for the identity.

## 2. The exact slack

If `|a|<1` and `|c|<1`, the triangle inequality in (I1) gives

```text
|g_j(t a)| <= (1-t^j)|c| + (t^j-t^n)|a|^n = 1-S_j(t),
```

where

```text
S_j(t)
 = t^n + (1-t^j)(1-|c|) + (t^j-t^n)(1-|a|^n).          (S)
```

For `1<=j<n` and `0<=t<=1`, all three terms are nonnegative and `S_j(t)>0`:
at `t=0` the second term is positive, while for `t>0` the first term is.
Therefore the following is an exact, finite certificate for an actual safe
spoke:

```text
sum_(k != j) |b_k| |a|^k |t^k-t^j| < S_j(t)
for every 0<=t<=1                                      (C)
```

implies `|f(t a)|<1` for the whole segment. The Lean theorem
`norm_lt_one_of_model_remainder_slack` formalizes the load-bearing final
triangle-inequality step, while the same module checks (I1), (I2), and (S).

## 3. A finite multiscale envelope

The endpoint factors admit the elementary bounds

```text
|t^k-t^j|
 <= |k-j| t^min(k,j) (1-t),       0<=t<=1.              (E)
```

Indeed, after extracting `t^min(k,j)`, the remaining factor is
`1-t^d=(1-t)(1+t+...+t^(d-1))<=d(1-t)`.

Thus (C) is implied by one explicit one-variable inequality involving only
the finite coefficient envelope

```text
B_j(t) = sum_(k != j) |k-j| |b_k| |a|^k t^min(k,j).
```

Namely, `(1-t)B_j(t)<S_j(t)`. Different `j` may dominate on different radial
intervals. Because both the polynomial and every interpolant agree at the
interval endpoints `0` and `a`, those intervals can be glued without a new
endpoint error. This is the correct replacement for a non-uniform “literal
first nonzero mode” argument.

## 4. What is closed and what remains

This checkpoint closes the exact spoke-stability arrow for any exponent whose
finite envelope beats its explicit slack. It also explains why the earlier
quadratic remainder was the wrong quantity near `t=1`: interpolation forces
the actual error to zero there.

What remains is combinatorial-geometric: prove that two roots can be selected,
with exponents allowed to change across finitely many subintervals, so that
their envelope certificates cover the two truncated spokes and the existing
connector. The deterministic checker verifies the identities and bounds and
includes configurations where a fixed exponent fails, so this note does not
silently promote the certificate to a universal one-exponent theorem.
