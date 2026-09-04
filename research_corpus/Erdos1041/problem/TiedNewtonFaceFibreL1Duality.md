# Fibre-speed `L1` as an exact Chebyshev interpolation problem

The all-fibre product and moment identities do not by themselves select two
short inverse branches.  This note identifies the realizability structure that
the abstract product countermodel omits: inverse velocities are barycentric
weights of one actual polynomial fibre.  Their `L1` norm is exactly a finite
Chebyshev interpolation constant.

## 1. Full-fibre duality

Let

```text
P(z)=product_{j=1}^n (z-z_j)
```

be monic with distinct complex roots.  For a polynomial `L`, write `lc_{n-1}(L)`
for the coefficient of `z^(n-1)`, with value zero when `deg L<n-1`.

**Theorem 1 (barycentric `L1` duality).**

```text
sum_{j=1}^n 1/|P'(z_j)|
 = max { |lc_{n-1}(L)| : deg L<=n-1 and |L(z_j)|<=1 for every j }.   (1)
```

### Proof

For data `epsilon_1,...,epsilon_n`, the unique interpolant of degree at most
`n-1` is

```text
L_epsilon(z)=sum_j epsilon_j P(z)/((z-z_j)P'(z_j)).          (2)
```

Every Lagrange basis polynomial in (2) has leading coefficient `1/P'(z_j)`.
Consequently

```text
lc_{n-1}(L_epsilon)=sum_j epsilon_j/P'(z_j).                 (3)
```

The constraints `|L(z_j)|<=1` are exactly `|epsilon_j|<=1`.
Complex `l1`--`linfinity` duality gives

```text
max_{|epsilon_j|<=1} |sum_j epsilon_j/P'(z_j)|
 =sum_j 1/|P'(z_j)|;
```

choose the phases of `epsilon_j` so all summands in (3) have the same
argument.  This proves (1).  `□`

This is not a relaxation: the maximizer is an actual polynomial interpolant.
The moment identities

```text
sum_j z_j^ell/P'(z_j)=0       (0<=ell<=n-2),
sum_j z_j^(n-1)/P'(z_j)=1
```

are precisely the coefficient-extraction identity behind (3).

## 2. Exact monodromy-block version

For a nonempty subset `E` of the roots, define

```text
C_E(P)=sum_{j in E} 1/|P'(z_j)|.
```

**Theorem 2 (block duality).**

```text
C_E(P)=max { |lc_{n-1}(L)| :
  deg L<=n-1,
  L(z_j)=0 for j notin E,
  |L(z_j)|<=1 for j in E }.                                  (4)
```

### Proof

In (2), prescribe `epsilon_j=0` outside `E` and allow
`|epsilon_j|<=1` inside `E`.  Equation (3) and the same phase choice give (4).
`□`

Writing

```text
P_{E^c}(z)=product_{j notin E}(z-z_j),       L=P_{E^c} S,
```

turns (4) into a degree-`|E|-1` problem:

```text
C_E(P)=max { |lc_{|E|-1}(S)| :
  deg S<=|E|-1,
  |P_{E^c}(z_j)S(z_j)|<=1 for j in E }.                       (5)
```

Thus a component end block is not merely a subset of an abstract velocity
vector.  The outside sheets enter through the exact external factor
`P_{E^c}`.  Deleting them or replacing them by a product bound loses the
quantity that (5) exposes.

## 3. Calibration on the regular fibre

For `P(z)=z^n-r^n`,

```text
|P'(r omega_j)|=n r^(n-1),
sum_j 1/|P'(r omega_j)|=r^(1-n).                              (6)
```

The interpolant

```text
L(z)=z^(n-1)/r^(n-1)
```

has modulus one on every node and attains (1).  Hence the regular fibre is an
equality calibration for the desired full-sheet speed comparison.

For a tied-face fibre

```text
Q(z)=-z^n+sum_{m<=M} A_m z^m,        Q(z_j(t))=-t,
```

put `P_t(z)=-Q(z)-t`.  Since `P_t'(z_j)=-Q'(z_j)`, Theorem 1 gives

```text
sum_j |z_j'(t)|
 = max { |lc_{n-1}(L)| : |L(z_j(t))|<=1 for every j }.         (7)
```

The regular baseline is `t^(1/n-1)`.  Therefore the pointwise full-fibre
contraction is exactly the Chebyshev statement

```text
|lc_{n-1}(L)| <= t^(1/n-1)
whenever |L(z_j(t))|<=1 for all fibre nodes.                   (8)
```

Equation (8) is not asserted here; near a critical fibre it can fail or become
singular.  The exact gain is the equivalence (7), which replaces an arbitrary
velocity-vector relaxation by a realizable interpolation problem.

## 4. The corrected two-end research target

Let `E(U)` be the monodromy end block of a negative component.  A useful
producer may take any of the following increasingly weak forms.

1. A pointwise block bound from (5) strong enough to select two sheets.
2. A weak-majorization theorem for the barycentric weights within `E(U)`.
3. An integrated bound for the two smallest block weights along a loop or ray.
4. A weighted bound in which `P_{E^c}` supplies the compensation missing from
   the naive block `L1` inequality.

By the monodromy-loop representation, the required endpoint is not a marked
leftmost pair.  It is one loop class taking some `j in E(U)` to a distinct
`k in E(U)` whose integrated lifted action has nonpositive renormalized defect,
with strictness or equality rigidity at finite radius.

The decisive falsifier should optimize (5) on exact algebraic fibres from the
known quintic no-go and rescue models.  If a proposed inequality fails, the
maximizing interpolant `S` is an exact certificate of the missing hypothesis;
it is more informative than another anonymous velocity vector.

## 5. Claim boundary and formal landing

Theorems 1 and 2 are exact finite-dimensional identities.  They do not prove a
pointwise or integrated contraction, `MLS-strict`, the tied-face selector, or
unrestricted Erdős #1041.

A Lean landing is finite algebra once polynomial interpolation is available:

```text
lagrange_leadingCoeff_eq_barycentric_sum
complex_l1_eq_max_phase_pairing
fibreSpeedL1_eq_interpolationLeadingCoeffSup
blockFibreSpeedL1_eq_vanishingInterpolationSup
```

The monodromy-block analytic continuation and integrated metric consumer remain
ordinary mathematics until separately formalized.
