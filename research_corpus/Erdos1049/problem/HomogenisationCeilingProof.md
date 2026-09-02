# Erdős 1049: the content route ends at `a > b²`, and `3/2` is on the wrong side of it

## The finding in one line

On the fixed-diagonal q-Apéry construction the two homogenised numerators are
**coprime** — there is no content to find — and even if there were, `num(R_j)`
alone already exceeds the decay budget at base `3/2`. The whole content lane is
capped at `a > b²`, and `3 ≤ 2²`.

## What was being hunted

Producer `[0] outward_scalar_primitive_content_bound` had narrowed to

> only a specialization-selective gcd theorem strictly below that resultant
> remains on this diagonal,

and producer `[1]` carries the height half of the same idea. Both look for common
content in the cleared coefficients. This note measures the content, bounds it, and
shows the hunt cannot succeed at `3/2` no matter what it finds.

## The decision rule, exactly

Write `ρ_j = L_j/R_j`, `B_j = den(ρ_j)`, `A_j = num(ρ_j)`, `D_j = (3/2)j²`. From the
Casoratian tail, `|S − ρ_j| = q^{−2D_j + O(j)}`. Since `|B_jS − A_j| = B_j·|S − ρ_j|`,

> the linear form decays **iff** `log B_j < 2 D_j log(a/b)`.

At `q = 3/2` that budget is `3 log(3/2)·j² = 1.21640 j²`.

## Three exact growth identities

The three-point estimator `(f(j+2) − 2f(j+1) + f(j))/2` annihilates every linear and
constant term, so a constant output is an identity, not a fit. It returns, with **zero
drift** at every index tested and agreement to `3·10⁻⁸` (the float accuracy of the
log routine on 10⁵-bit integers):

| quantity | measured | closed form |
|---|---|---|
| `log num(R_j)/j²` | `1.647918433` | `(3/2)·log 3` |
| `log den(R_j)/j²` | `1.039720771` | `(3/2)·log 2` |
| `log |R_j|/j²` | `0.608197662` | `(3/2)·log(3/2)` |

So `num(R_j) = a^{D_j+O(j)}` and `den(R_j) = b^{D_j+O(j)}`: the denominator is exactly
the homogenisation power, nothing more.

## There is no content

Measured at `j = 40, 60, 80, 100, 120`:

```
gcd( num(R_j), num(L_j) )  =  1      exactly, at every index
```

and the full cross-content that the primitive vector removes is

```
log gcd = 1.04256 j²   of which the 2-power is 1.04256 j²   odd remainder = 0.00000
```

The primitive vector strips the homogenisation power of 2 and **nothing else**.
`B_j` is coprime to 6, and `log B_j = 1.98739 j²` — which is exactly
`(3/2)log 3 + (3/π²)log 3 = 1.98186`, i.e. `num(R_j)` times the cyclotomic clearing,
with no cancellation between them.

### And the Casoratian proves the bound

This is not only measured. Let `p ∤ 6` divide both numerators at index `j` while
dividing neither denominator at index `j−1`. Then

```
v_p(W_{j−1}) ≥ min( v_p(L_j)+v_p(R_{j−1}),  v_p(L_{j−1})+v_p(R_j) ) ≥ 1 ,
```

and the closed form `W_{j−1} = −3^j(3^j + 2^{j+1}) / (2^j(3^j − 2^j))` forces
`p | 3^j + 2^{j+1}`. Hence the shared content divides `3^j(3^j + 2^{j+1})` and

> **`log gcd(num R_j, num L_j) ≤ 2j·log 3 = O(j) = o(j²)`.**

A gcd theorem on this diagonal can move the *linear* term. It cannot touch the
quadratic constant, which is the only thing that decides decay.

## The ceiling

`B_j` is a multiple of `num(R_j)/gcd(num R_j, num L_j)`, so with `C_j ≥ 0` the extra
clearing,

```
log B_j  ≥  D_j log a  −  O(j)  +  C_j .
```

Decay needs `log B_j < 2D_j(log a − log b)`. Taking `C_j = 0` — a *perfect* content
theorem, better than anything producer [0] could prove — this still requires

```
D_j log a  <  2 D_j (log a − log b)   ⟺   2 log b < log a   ⟺   a > b² ,
```

and **the degree exponent `D_j` cancels**. The ceiling is a property of the base
alone: no choice of diagonal, degree, or growth rate moves it.

### This also derives the recorded threshold law

Put the actual clearing back, `C_j = (3/π²)j² log a`, with `D_j = (3/2)j²`:

```
(3/2)log a + (3/π²)log a  <  3(log a − log b)   ⟺   log b/log a < 1/2 − 1/π² .
```

That is the packet's threshold law, here **derived** instead of measured — and the
derivation names its parts. The `1/π²` is exactly the cyclotomic clearing
`Σ_{r≤n} φ(r) ~ 3n²/π²`; deleting it moves the threshold from `1/2 − 1/π²` to `1/2`,
which is the same statement as `a > b²`.

## What it decides

| base | `log b/log a` | current method | perfect content | `a > b²` |
|---|---|---|---|---|
| `2/1`, `3/1` | 0 | closes | closes | yes |
| `7/2` | 0.35621 | **closes** | closes | yes |
| `5/2` | 0.43068 | no | **closes** | yes |
| `10/3` | 0.47712 | no | **closes** | yes |
| `3/2` | 0.63093 | no | **no** | **no** |
| `4/3` | 0.79248 | no | no | no |
| `5/4` | 0.86135 | no | no | no |

- **Producers [0] and [1] cannot reach `3/2`.** Not "have not yet"; cannot. Their
  height half is capped strictly below the target by a base-only inequality.
- Their maximum possible prize is the band `b² < a` with `log b/log a ≥ 1/2 − 1/π²`.
  The **smallest member is `5/2`**, then `10/3`, `11/3`, `13/3`, `14/3`, `17/4`, …
  Whether `5/2` is open in the literature is a prior-art question this note does not
  answer, and it should be asked before spending on it.
- Reaching `3/2` needs a construction that does not look for content **after**
  building the rows — because there is none — but imposes the divisibility while
  choosing the combination. That is precisely producer `[3]`
  (congruence-constrained adelic Hermite–Padé), whose own statement already says

  > The current architecture builds rows first and looks for divisibility
  > afterwards, via gcds or four-jet collisions. Impose the 2-adic and 3-adic
  > constraints WHILE choosing the combination instead.

  This note is the quantitative reason that framing is right: looking afterwards
  returns `gcd = 1`.

## Relation to the step-1 result

[`FixedPrimeInfiniteTailProof.md`](FixedPrimeInfiniteTailProof.md) gives a
conditional fixed-prime route for the window-divisor part of step 1 of producer
[1].  Its finite harmonic and q-Apéry replay is certified through row 301 and
5-adic levels 1, 2, and 3; the all-level monodromy/continuity premise needed to
promote that replay to a permanent denominator tail remains open.  Thus this
note does not make step 1 unconditionally free or remove the need to state its
continuity premise.  The two results are complementary and both are needed to
see the situation clearly: the conditional window divisor is for the
non-vanishing `1/q` step, never for height — and the height is where the lane
ends.

## Claim boundary

A no-go for the content lane on the fixed diagonal, not an irrationality theorem.
It assumes the two structural facts it verifies (`den(R_j) = b^{D_j+O(j)}`,
`|S − ρ_j| = q^{−2D_j+O(j)}`) and the Casoratian closed form (C), all of which are
established. It says nothing about producers [3], [4] or [2], and Erdős #1049 at
base `3/2` remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_homogenisation_ceiling.py --max-index 132
```

Six falsifiers: the three exact growth identities by second difference; coprimality
of the two numerators; the Casoratian cap as a live bound; the content being purely
the 2-power with odd remainder exactly zero; the height exceeding the decay budget
with the irreducible floor `(3/2)log 3` **already** over it; and agreement of the
derived rule with both the recorded threshold `1/2 − 1/π²` and the ceiling `a > b²`
across eight bases. Exit `0` iff all six pass. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_homogenisation_ceiling_receipt.json`.
