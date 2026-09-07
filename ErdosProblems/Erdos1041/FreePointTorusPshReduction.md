# Erdős 1041 satellite: the all-degree torus/psh bridge from FP to (S)

Date: 2026-08-30.  Origin: main-loop corpus reread followed by an exact
reconstruction of the root-polydisk maximum argument.  Deterministic replay:
`scripts/check_erdos1041_free_point_torus_psh_reduction.py`.  Scalar Lean
kernel: `FreePointTorusPshReduction.lean`.

This note closes the implication which was deliberately left unclaimed in
`FreePointMeanInequalityFP3.md`:

```text
                    FP_{n-1}  ==>  (S)_n.                 (BRIDGE)
```

Consequently the already proved `FP_3` and `FP_4` establish Conjecture (S)
in degrees four and five.  This is a genuine advance of the auxiliary
frontier, but (S) by itself does **not** prove the parent Erdős 1041 theorem.

## 1. Statements

For `m >= 1`, write `FP_m` for the assertion that every
`c_1,...,c_m` in the closed unit disk satisfies

```text
sum_j (prod_k |1-conj(c_j)c_k|)^(1/m) <= m.
```

For `n >= 2`, write `(S)_n` for the assertion that, for every monic
degree-`n` polynomial `f`, every minimum enclosing disk of its roots with
radius `R`, and the critical points `c_1,...,c_{n-1}` counted with
multiplicity,

```text
sum_j |f(c_j)|^(1/n) <= (n-1) R.
```

**Theorem (all-degree bridge).**  If `FP_{n-1}` holds, then `(S)_n` holds.

**Corollary.**  `(S)_n` is proved for `n=2,3,4,5`.  The new cases are
`n=4` from `FP_3` and `n=5` from `FP_4`.

## 2. The root-polydisk functional is plurisubharmonic

Translate the centre of a minimum enclosing root disk to zero and, when
`R>0`, scale its radius to one.  Thus

```text
f_a(z) = prod_{i=1}^n (z-a_i),        |a_i| <= 1.
```

Define the symmetric critical-value functional

```text
Phi(a_1,...,a_n)
  = sum_{f_a'(c)=0, with multiplicity} |f_a(c)|^(1/n).    (1)
```

On the open set where `f_a'` has simple roots, its critical points admit
local holomorphic branches `c_j(a)`.  The corresponding critical values

```text
v_j(a) = f_a(c_j(a))
```

are holomorphic.  Since `|v_j|^alpha` is plurisubharmonic for every
`alpha>0`, (1) is plurisubharmonic there.

The complement is the analytic multiple-critical locus.  Roots of a monic
polynomial vary continuously as an unordered multiset with its
coefficients; evaluating `f_a` at those roots preserves that continuity.
Hence `Phi` is continuous, in particular locally bounded above, across the
multiple-critical locus.  The removable-singularity theorem for
plurisubharmonic functions therefore extends the same `Phi` across that
locus.  Thus `Phi` is a continuous plurisubharmonic function on a
neighbourhood of the closed root polydisk.

Apply the one-variable subharmonic maximum principle successively to
`a_1,...,a_n`.  It gives the exact distinguished-boundary reduction

```text
max_{|a_i|<=1} Phi(a_1,...,a_n)
  = max_{|a_i|=1} Phi(a_1,...,a_n).                       (2)
```

No selection or labelling of critical points is used at a collision: the
functional is the symmetric multiset sum.

## 3. Exact identity on the distinguished torus

Suppose now all roots `zeta_i` lie on the unit circle and write

```text
f(z)=prod_i(z-zeta_i),        f'(z)=n prod_{k=1}^{n-1}(z-c_k).
```

For every critical point `c_j`, counted with multiplicity,

```text
|f(c_j)| = prod_{k=1}^{n-1} |1-conj(c_j)c_k|.             (3)
```

Here is a direct proof.  First assume `c=c_j` is not a root and `c != 0`.
The conjugate critical equation and `|zeta_i|=1` give

```text
sum_i zeta_i/(1-conj(c)zeta_i)=0,
sum_i 1/(1-conj(c)zeta_i)=n.
```

Therefore the logarithmic derivative at `1/conj(c)` yields

```text
|f'(1/conj(c))| = n |c| |f(1/conj(c))|.
```

Using the two product formulae above, its left side is

```text
n |c|^{-(n-1)} prod_k |1-conj(c)c_k|,
```

whereas its right side is

```text
n |c| * |c|^{-n}|f(c)|.
```

Cancellation proves (3).  If `c=0`, both sides of (3) are one because
`|f(0)|=1`.  If a critical point is also a unit-circle root, it is a
repeated root; both sides vanish because that root also occurs among the
zeros of `f'`.  These cases exhaust the boundary by Gauss--Lucas, and the
identity also follows uniformly by continuity under splitting repeated
roots.

## 4. FP supplies the wrong exponent — concavity fixes it exactly

Put `m=n-1` and, on the torus, define

```text
y_j = |f(c_j)|^(1/m) >= 0.
```

By (3), `FP_m` says

```text
sum_j y_j <= m.                                           (4)
```

The exponent required by (S) is smaller.  Let

```text
q = m/(m+1) = m/n.
```

Concavity of `y^q`, or its tangent at one, gives for every `y>=0`

```text
y^q <= q y + (1-q) = (m y+1)/n.                          (5)
```

Summing (5) and using (4),

```text
sum_j |f(c_j)|^(1/n)
  = sum_j y_j^q
  <= q sum_j y_j + m(1-q)
  <= qm + m(1-q)
  = m.                                                     (6)
```

Equations (2), (3), and (6) prove the normalized theorem.

Finally, for a root disk of centre `tau` and radius `R>0`, set

```text
g(w)=R^{-n} f(tau+Rw).
```

Its critical values are `R^{-n}f(c_j)`, so the normalized estimate for
`g` becomes the asserted bound `(n-1)R` for `f`.  If `R=0`, the polynomial
is `(z-tau)^n` and both sides vanish.  QED

## 5. Equality and claim boundary

The bridge proves only the inequality.  The regular-polygon family
`f(z)=(z-tau)^n-lambda` attains equality after choosing its minimum root
disk: all critical points coincide at `tau`, all normalized `y_j` equal
one, and both (4) and (5) are equalities.  A complete converse equality
classification would additionally require tracing equality through the
plurisubharmonic maximum step; it is not claimed here.

The analytic proof uses the standard removable-singularity theorem for
locally bounded plurisubharmonic functions across analytic sets.  The Lean
companion checks the entire scalar exponent-conversion kernel (5) and its
finite-sum consequence, not the several-complex-variables boundary theorem
or the self-inversive polynomial identity.  The deterministic checker
stress-tests those analytic/algebraic interfaces, including near critical
collisions, but numerical checks are corroboration rather than proof.

No novelty or literature-priority claim is made.  The result is “proved in
this corpus”; it may well be classical.  The next auxiliary burden is
`FP_m` for `m>=5`.  The parent problem still requires one of the metric
selection/cover/allocation routes recorded in `FRONTIER.md`.
