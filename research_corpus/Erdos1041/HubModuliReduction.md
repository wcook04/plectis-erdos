# Erdős 1041: the minimal hub has exactly `n-2` complex moduli, and at degree three admissibility is the whole content

Status: one exact reduction, one complete map of the degree-three moduli space,
one structural consequence. 2026-08-24. This does not prove Erdős #1041. What it
supplies is the **exact quotient** the branch-length problem lives on, an
explicit form for the constraint everything in this directory keeps colliding
with, and a measurement of what that constraint is worth.

> **Attribution, same day.** The affine normalisation of §1 is **not first
> here.** A concurrent line landed it as **Theorem N** of
> [AffineNormalisedModuli.md](AffineNormalisedModuli.md) (commits `3d7992495a`,
> `ad1360f5b4`), in the form `P(u) = f(c + lambda u)/f(c)` with `lambda^n = f(c)`,
> with the same conclusion — residual freedom exactly `C^{n-2}`, and the whole
> equality family collapsing to the single point `a = 0`. The two derivations are
> the same coordinate change up to a sign convention (`P = 1 - G`), reached
> independently within the same hour. §1 is retained because the rest of this
> note is stated in its coordinates; read it as a restatement of Theorem N, and
> cite that.
>
> What is **not** in that note, and is this one's: the plurisubharmonicity of §5
> and the maximum principle it gives, the reduction of degree three to the single
> complex parameter `gamma` with admissible region the complement of `D(-1,1)`,
> the measured margin of §3, and the explicit one-real-parameter pencil of §5a.
> Its Theorem R (room converts into length) and Theorem B (the two-root component
> is one Blaschke product) are its own and are not touched here.

## 1. The reduction

Let `c*` be the minimal critical point, `mu = |f(c*)|`, `rho = mu^{1/n}`.
Translate `c*` to `0`, scale by `rho`, and rotate so that `arg f(c*) = pi`. Since
`f` is monic and `rho^n = mu`,

```text
f(rho zeta) / f(c*)  =  1 - G(zeta),
G(zeta) = zeta^n - sum_{k=2}^{n-1} beta_k zeta^k          (monic, G(0) = G'(0) = 0).
```

Every affine degree of freedom is used: translation fixes the hub, rotation
fixes `arg f(c*)`, scaling fixes `|f(c*)|`. **What is left is exactly the `n-2`
complex numbers `beta`.** In these coordinates:

| object | in `beta` coordinates |
|---|---|
| the two descending branches | `G(zeta) = s`, `s : 0 -> 1`, from `zeta = 0` |
| the roots of `f` | the roots of `G(zeta) = 1` |
| `Rt := R/rho` | circumradius of those roots |
| **the hub is minimal** | every other critical value `v` of `G` has `\|1 - v\| >= 1` |
| the strong form `L(c*) <= 2 mu^{1/n}` | `L(beta) <= 2` |
| the obligation `L(c*) <= 2R` | `L(beta) <= 2 Rt(beta)` |
| Fekete | `Rt >= 1` |

The last two lines say the strong form implies the obligation, and that the gap
between them is exactly the Fekete deficit.

**Minimality reads as an explicit domain.** `|f(c_k)|/mu = |1 - G(zeta_k)|`, so
the hub is the minimal critical point precisely when the critical values of `G`
avoid the **open disk `D(1,1)`**. Write `A_n` for that set of `beta`. `A_n` is
exactly the image of the normalisation map: a `beta` outside it is not a missing
case, it is a polynomial that normalises at a different hub.

**`beta = 0` is the equality family.** `G = zeta^n`, the branches are two radii
of length `1`, the roots are the `n`-th roots of unity, `L = 2` and `Rt = 1`
exactly — this is `z^n - r^n`. And `|1 - 0| = 1`, so **`beta = 0` lies on the
boundary of `A_n`, not in its interior.**

## 2. `n = 2` has an empty moduli space

There are no `beta_k` at all: `G = zeta^2`, the branches are `+/- sqrt(s)`, and
`L = 2` identically. **That is the structural reason every monic quadratic is an
equality case.** It is not a coincidence of the normalisation and not a family
of extremals — it is the absence of any parameter to vary. The corpus records
"every quadratic attains equality" as an observed fact in four places; this is
what it means.

## 3. `n = 3` is one complex parameter

`G = zeta^3 - beta zeta^2`. The map `zeta -> omega zeta`, `omega^3 = 1`, sends
`beta -> omega^2 beta` and preserves every length, so everything depends only on

```text
gamma = 4 beta^3 / 27  =  -G(2beta/3),   the other critical value of G,
```

and admissibility is exactly `|1 + gamma| >= 1`: **`gamma` outside the open disk
`D(-1,1)`.** The extremal `z^3 - r^3` is the single point `gamma = 0`, which sits
**on the boundary circle** of that disk.

So the whole degree-three branch-length problem is one function of one complex
variable on the complement of one disk. Mapped:

| | sup of `L/2` |
|---|---|
| over admissible `gamma` (outside `D(-1,1)`) | `1`, approached only as `gamma -> 0` |
| over **inadmissible** `gamma` (inside `D(-1,1)`) | **`1.0163478`** at `gamma = -0.0984808 + 0.0173648 i` |

> **At the minimal degree, the entire content of the strong form is the
> minimality of the hub.** Drop that hypothesis and the bound fails by 1.6%;
> keep it and the bound holds with the extremal on the constraint boundary.

This is the exact sense in which "admissibility is load-bearing and cannot be
erased by affine normalisation" — the phrase `research_packet.json` uses without
a margin attached. Here is the margin.

Along the constraint boundary `|1 + gamma| = 1`, writing `gamma = -1 + e^{i psi}`:

| `psi` | 0.005 | 0.02 | 0.08 | 0.3 | 0.8 | 1.6 | 3.0 |
|---|---|---|---|---|---|---|---|
| `L/2` | 0.96438 | 0.94093 | 0.90055 | 0.83624 | 0.76875 | 0.71726 | 0.68759 |

monotone decreasing, with supremum `1` at `psi -> 0`, i.e. at `gamma = 0`. The
approach is `1 - kappa |beta| + O(|beta|^2)` with `|beta| ~ |gamma|^{1/3}` — the
cusp, in the coordinate where it is visible — and the measured `kappa` is about
`0.22`, in the same place as the `kappa_3 >= 15 sqrt3/32 - 3/5 = 0.2119` that
[NearFeketeCuspPositivityProof.md](NearFeketeCuspPositivityProof.md) proves by a
different route. (Same place, not the same constant: the perturbation parameters
differ and no attempt is made here to match normalisations.)

## 4. Near the extremal the admissible set is a thin cone

For small critical values `v` the constraint `|1 - v| >= 1` is
`Re v <= |v|^2/2`, i.e. essentially `Re v <= 0`, and it must hold at **all**
`n-2` non-hub critical values at once. For `G = zeta^n - eps zeta^2` the critical
values are `-eps(1-2/n)(2eps/n)^{2/(n-2)} omega_k^2` over the `(n-2)`-th roots of
unity `omega_k`, whose squares are spread around the circle, so the condition
fails as soon as some `omega_k^2` has negative real part, i.e. for `n >= 5`.
Measured at `eps = 1e-6`, both the `beta_2`-only direction and the all-equal
direction `beta_2 = ... = beta_{n-1} = eps` give slack `>= 0` at `n = 3, 4` and
slack `< 0` at `n = 5, 6, 8` (`-1.6e-11`, `-3.8e-10`, `-2.4e-9`), exactly as the
formula predicts. That is why neither direction can calibrate an instrument at
`n >= 5`: it leaves the domain of the conjecture, and the simple-hub model
over-reports there by about `|beta|^{1/(n-2)}`.

Two consequences. Most small perturbations of `z^n - r^n` are **not** admissible
at the same hub — they renormalise at a different one, which is `negative_results`
entry 32's "hub selection dominates the form of the bound" seen from the moduli
side. And any search that perturbs the extremal without checking minimality is
sampling mostly outside the domain of the conjecture.

## 5. `L` is plurisubharmonic in `beta`, so the extremum lives on the tie locus

> **Proposition.** On the interior of `A_n`, `L(beta)` is plurisubharmonic.

*Proof.* Fix `s in (0,1]`. Admissibility puts every critical value of `G` outside
`D(1,1) ⊃ (0,2)`, so no critical value lies on `(0,s]` and the branch
`zeta_±(s,beta)`, continued from the hub along `[0,s]`, is holomorphic in `beta`
away from the locus where the two branches are exchanged. There
`∂zeta_±/∂s = 1/G'(zeta_±)` is holomorphic and non-vanishing, so `|∂zeta_±/∂s|`
is plurisubharmonic. The **sum** over the two branches is single-valued (it is
symmetric under the exchange) and locally bounded, so it extends
plurisubharmonically across the exchange locus. Integrating over `s in (0,1)`
against `ds` preserves plurisubharmonicity. ∎

Hence `L` has no strict interior maximum on `A_n`, and — since `L -> 0` as
`beta -> infinity` (the branches solve `zeta^2 ~ -s/beta_2`, so their length is
`O(|beta_2|^{-1/2})`) — its supremum is attained on `∂A_n`.

**`∂A_n` is exactly the locus where a second critical value of `f` ties with the
hub in modulus.** That is a one-line explanation of a pattern this directory has
recorded four separate times without a mechanism:

* the extremal `z^n - r^n` has **all** critical values equal — the deepest tie;
* `negative_results` entry 29's refutation of the strong form has its two
  smallest critical values agreeing to `2.3e-9` relative;
* [ComponentDepthRefutation.md](ComponentDepthRefutation.md)'s witness has them
  agreeing to `2.5e-5`;
* entry 32 records that 196 of 197 symmetric-bound violations sit at non-minimal
  hubs, i.e. where the selection is contested.

Extremal configurations for a branch-length bound have contested hubs **because
the maximum principle puts them on the boundary of the admissibility constraint**,
and that boundary is the tie locus.

*Cross-check.* The sub-mean-value inequality was tested directly, on circles
whose **whole disk** stays admissible with margin (`slack >= 0.03` at every
sample) and away from a near-degenerate hub: **74 circles at `n = 3,4,5,6`, zero
failures**, worst relative defect `+3.5e-5`, i.e. positive everywhere. The
hypothesis is not decoration: the same test run **without** constraining the
circle to stay admissible fails, 8 times in 70 circles at `n = 3…7`, with worst
relative defect `-2.0e-2`. Off the admissible region a critical value of `G` can
cross `(0,1]`, the branch continuation is no longer holomorphic in `beta`, and
the sub-mean-value inequality goes away — which is what the Proposition's
hypothesis is for, and is a measurement of what it is worth.

## 5a. At degree three the tie locus is one real parameter, explicitly

For `f = z^3 + p z + q` the critical values are `q +/- w` with
`w = (2p/3) sqrt(-p/3)`, so they are equal in modulus exactly when
`Re(conj(q) w) = 0`. Put `p = -3u^2`, so `w = -2u^3`; choosing `u = -2^{-1/3}`
makes `w = 1`, and the tie condition becomes `q` purely imaginary. Scaling fixes
`|w|`, rotation fixes `arg w`, and conjugation fixes the sign of `a`, so **up to
the symmetries the entire degree-three tie locus is**

```text
f_a(z) = z^3 - 3 * 2^{-2/3} z + i a,          a >= 0,
```

with both critical values of modulus `sqrt(a^2 + 1)` for every `a`. Measured:

| `a` | 0 | 0.3 | 1 | 3 | 10 | 50 | 300 |
|---|---|---|---|---|---|---|---|
| `psi = arg(f(c_2)/f(c_1))` | `pi` | 2.5587 | 1.5708 | 0.6435 | 0.19934 | 0.03999 | 0.006667 |
| `L(c*)/(2 mu^{1/3})` | 0.687365 | 0.691295 | 0.718531 | 0.784920 | 0.859428 | 0.923481 | 0.960490 |

increasing in `a`, with limit `1` as `a -> infinity` (where `p/q -> 0` and `f_a`
degenerates to `z^3 + i a`, the extremal family). These numbers come from the
**root-coordinate** engine and match the `gamma`-circle profile of §3, which
comes from the moduli engine, at every shared `psi` — two independent routes to
the same curve, agreeing at `a = 0` to all nine digits (`0.687364818`).

**So the degree-three strong form has been reduced to a one-real-variable
inequality on an explicit cubic pencil**: given the Proposition of §5, together
with `L -> 0` at infinity, `L(c*) <= 2 mu^{1/3}` for every cubic is equivalent to
`L/(2 mu^{1/3}) <= 1` along `f_a`. That last step is not proved here.

## 6. What this is for

`beta`-space is the right search space. It is `2(n-2)` real parameters against
`2n` for a root configuration, with translation, rotation and scale already
quotiented out and admissibility an explicit inequality rather than something a
search has to stumble into. Every adversarial search recorded in this directory
has been run in root coordinates, where the near-Fekete shell is a `1e-7`-thin
target that `HardRegimeIsNearFekete.md` says a bulk search "has essentially no
chance" of entering; in `beta` coordinates that shell is the neighbourhood of the
origin.

## 7. Claim boundary

Not first here: the affine normalisation of §1 is
[AffineNormalisedModuli.md](AffineNormalisedModuli.md)'s Theorem N, landed the
same day by a concurrent line.

Proved, by ordinary mathematics, and first here so far as this directory goes:
the form of the admissibility constraint as "critical values of `G` avoid
`D(1,1)`", the empty moduli space at `n = 2` and the identity
`L = 2` there, the `gamma` reduction at `n = 3` and its constraint `|1+gamma|>=1`,
the critical-value formula of §4, and the Proposition of §5 with its two
corollaries.

Measured, reproducible from the receipt: the two suprema of §3, the boundary
profile and its monotonicity, the slack values of §4, and the calibration
`L -> 2`, `Rt -> 1` at `n = 3, 4` (exact to `1e-9`) with mesh self-consistency
`2e-16` to `8e-10`.

Measured, not proved: the sub-mean-value cross-check of §5 (74 circles, 0
failures) and the table of §5a.

### Measured: the supremum of `L/2` over the admissible moduli space, per degree

Hill-climbing in `beta` with `slack >= 1e-10` enforced (16 restarts, 300 steps,
light mesh; the `n = 4` winner re-verified at four mesh depths, by the
independent root-coordinate engine, and by a 50-dps chord-sum lower bound):

| `n` | 3 | 4 | 5 |
|---|---|---|---|
| `sup L/2` over admissible `beta` | `0.99988` | **`1.00107`** | **`1.00438`** |

So the strong form `L(c*) <= 2 mu^{1/n}` is true at `n = 3` — where the extremal
is the single boundary point `gamma = 0` — and **false from `n = 4`**, which is
where `negative_results` entry 29 already put it, now located in the coordinates
that make the search cheap. The `n = 4` winner does more than that: its Fekete
deficit `R/mu^{1/4} = 1.00091` is smaller than its excess, so the **obligation**
`L(c*) <= 2R` fails there too — see
[ComponentDepthRefutation.md](ComponentDepthRefutation.md) §8. Degrees `6` and
above were not reached before closeout.

Not established: the supremum of `L/2` over `A_n` for `n >= 6`; the
one-real-variable inequality along `f_a` that §5a reduces degree three to; anything
about the obligation `L <= 2 Rt` beyond degree three; and any claim that this
reduction is new to the literature rather than to this directory — it is an
ordinary affine normalisation and a priority check should precede any novelty
claim. **Erdős #1041 remains open.**

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_hub_moduli.py
```
