# Erdős #1041: the two-root path length is lower semicontinuous, so a dense class suffices

Status: complete ordinary proof, exact rational checker, focused Lean kernel.
2026-08-25. **This does not prove Erdős #1041.** It removes one open producer
from the dependency graph and restates the unrestricted problem as a single
extremal question on a compact set.

## 0. What was open, and why the producer looked hard

`open_producers::collar_component_and_slack_stability_after_generic_perturbation`
asks for the transfer half of every genericity argument:

> prove that the selected sublevel component remains the intended component
> with strict data-dependent slack `q_g > q/2`, and quantify a root-transfer
> length budget relative to that same polynomial.

`negative_results` entry 3 is the recorded obstruction:

> No polynomial-independent positive length slack is available, even for the
> quadratic Cassini family: root distances `2-2/m` approach two. Any
> generic-perturbation reduction must preserve a starting-polynomial-dependent
> margin; a fixed global transfer budget is eliminated.

Both statements are about carrying a path **from** a polynomial **to** its
neighbours. That is an upper-semicontinuity statement, and entry 3 says it has
no uniform modulus.

This note observes that the reduction never needed that direction. What it
needs is the opposite one — carrying a path from the neighbours **to** the
polynomial — and that direction is unconditional, needs no margin, and is
already compact. The producer is therefore not a prerequisite of any genericity
argument in this directory.

## 1. The functional

Let `K_n` be the set of monic degree-`n` polynomials with all roots in the
**closed** unit disk, identified with its compact set of coefficient vectors in
`C^n`. For `g in K_n` with root list `b_1, ..., b_n` listed with multiplicity,
put

```text
Lam(g) = min over i != j of
         inf { len(gamma) : gamma : [0,1] -> {|g| <= 1} rectifiable,
                            gamma(0) = b_i,  gamma(1) = b_j }
```

with values in `[0, +infinity]`. The `min` is over ordered index pairs of the
root **list**, so a repeated root gives `Lam(g) = 0` by the constant path, and
the value does not depend on the labelling.

`K_n` is the closed-disk class on purpose. The minimum-enclosing-disk
normalisation of `VisibilityOverlapReduction.md` §3 leaves the open-disk class
and lands in `K_n` with at least two roots on the boundary, so any statement
that is to be composed with that normalisation must be stated on `K_n`.

`Lam` is finite on `K_n`: Fekete gives `mu(g) <= 1`
(`VisibilityOverlapReduction.md` §3(a)), and at level `mu` the descent arc
through the minimising critical point is a rectifiable arc joining two roots
inside `{|g| <= mu}` (`AffineNormalisedModuli.md` Theorem B(B3)). Finiteness is
not used below; `[0, +infinity]` is enough.

## 2. Theorem L — lower semicontinuity

> **Theorem L.** `Lam` is lower semicontinuous on `K_n`. Equivalently, for
> every `c` the sublevel set `{ g in K_n : Lam(g) <= c }` is closed in `K_n`.

Three ingredients.

**(L1) A priori containment.** If all roots of `g` lie in the closed unit disk
and `|z| >= 2`, then

```text
|g(z)| = prod_j |z - b_j| >= prod_j (|z| - |b_j|) >= (|z| - 1)^n >= 1.
```

Hence `{|g| <= 1}` is contained in the fixed compact disk `{|z| <= 2}`, for
every `g in K_n` simultaneously. This is the only place the closed-disk
hypothesis is used, and it is what makes the family of admissible paths
uniformly bounded.

**(L2) Compactness of the path family.** Curves of bounded length in a fixed
compact set, parametrised at constant speed on `[0,1]`, form an
equi-Lipschitz, uniformly bounded family; Arzelà–Ascoli extracts a uniformly
convergent subsequence.

**(L3) Lower semicontinuity of length.** Length is lower semicontinuous under
uniform convergence of parametrised curves.

*Proof of Theorem L.* Let `g_v -> f` in `K_n` with `Lam(g_v) <= c` for all `v`,
`c < infinity`. Choose root labellings with `b_j^v -> b_j` (continuity of roots
as a multiset). For each `v` pick an index pair `(i_v, j_v)` and a path
`gamma_v` from `b_{i_v}^v` to `b_{j_v}^v` inside `{|g_v| <= 1}` with

```text
len(gamma_v) <= Lam(g_v) + 1/v <= c + 1.
```

There are finitely many index pairs, so pass to a subsequence on which
`(i_v, j_v) = (i, j)` is constant. Reparametrise each `gamma_v` at constant
speed on `[0,1]`; then every `gamma_v` is `(c+1)`-Lipschitz, and by (L1) its
image lies in `{|z| <= 2}`. By (L2), pass to a further subsequence with
`gamma_v -> gamma` uniformly on `[0,1]`.

The limit has the three properties required.

* Endpoints: `gamma(0) = lim b_i^v = b_i` and `gamma(1) = lim b_j^v = b_j`,
  and `i != j`.
* Containment: `g_v -> f` uniformly on the compact disk `{|z| <= 2}` (the
  coefficients converge and the disk is fixed), and `gamma_v -> gamma`
  uniformly, so `|f(gamma(t))| = lim |g_v(gamma_v(t))| <= 1` for every `t`.
* Length: by (L3), `len(gamma) <= liminf len(gamma_v) <= c`.

Hence `Lam(f) <= c`. Since `c` was an arbitrary finite bound valid along the
sequence, `Lam(f) <= liminf_v Lam(g_v)`, which is lower semicontinuity. ∎

**Two remarks on the proof.** The `(c+1)`-Lipschitz reparametrisation makes the
limit automatically `(c+1)`-Lipschitz, so (L3) can be replaced by the remark
that a `(c+1)`-Lipschitz curve on `[0,1]` has length at most `c+1`; the sharper
`liminf` form is what gives the clean statement. And the argument uses no
property of the endpoints beyond continuity of roots, so it applies verbatim to
any closed condition on a compact family of curves.

## 3. Corollary D — a dense class suffices

> **Corollary D.** Let `G` be any subset of `K_n` whose closure is `K_n`. If
> `Lam(g) <= 2` for every `g in G`, then `Lam(g) <= 2` for every `g in K_n`.

*Proof.* `{Lam <= 2}` is closed by Theorem L and contains `G`, hence contains
`closure(G) = K_n`. ∎

The classes actually used in this directory are dense in `K_n`:

| class | dense in `K_n` because |
|---|---|
| all roots in the **open** disk | `g(z) -> s^n g(z/s)`, `s -> 1^-` |
| squarefree | discriminant is a nonzero polynomial in the coefficients |
| one-coefficient genericity with finite exceptional set | finite sets are nowhere dense |
| any nonempty Zariski-open coefficient condition | complement is a proper subvariety |

Any finite intersection of these is still dense, so the hypotheses those
arguments assume may be conjoined freely.

## 4. Corollary S — the strictification is already free

`VisibilityOverlapReduction.md` §3 proves, for `f` monic with roots in the open
unit disk, distinct, with minimum enclosing disk `D(z_c, R)` and
`g(w) = R^{-n} f(z_c + R w) in K_n`, that `0 < R < 1` and that pulling a path
back along `w -> z_c + R w` gives

```text
|f| = R^n |g| <= R^n < 1   on the path,        length <= 2R < 2.
```

> **Corollary S.** To prove Erdős #1041 in degree `n` it suffices to prove
> `Lam(g) <= 2` for every `g` in **some** dense subset of `K_n`.

*Proof.* Corollary D upgrades the dense hypothesis to all of `K_n`; the
normalisation above converts `Lam(g) <= 2` into the two strict inequalities the
target asks for. A repeated root is the trivial case. ∎

Both strict inequalities come from `R < 1`, and none of them is asked of the
hypothesis. This is exactly why entry 3 is not an obstruction here: the
argument spends **no** slack at all, so there is nothing for the Cassini
degeneration `2 - 2/m -> 2` to consume.

### Compact-witness projection: valid, but weaker than Theorem L here

A returned Type-B packet proposed the following abstract closure principle.
Let `X` be a configuration space, let `K` be a compact witness space, and let
`R ⊆ X × K` be closed. If a dense set `D ⊆ X` satisfies

```text
for every x in D, there exists k in K with R(x,k),
```

then the same existential statement holds for every `x in X`. The reason is
that projection along a compact factor is a closed map, so
`{x : exists k, R(x,k)}` is closed and contains `D`. The Lean theorem
`exists_compact_witness_of_closed_relation_of_dense` formalises this exact
logical kernel. In particular, this argument needs no continuous selector of
a root, face, hub, ellipse, or path.

For the present problem, however, Theorem L is stronger and cheaper. It proves
directly that the success set `{g : Lam(g) <= 2}` is closed, without choosing a
finite-dimensional normalization of ellipse parameters, contact data, or
barycentric multipliers. Any bounded-length path sequence already has a
convergent subsequence in the fixed disk `|z| <= 2`; the limiting curve is the
witness. Thus escape of auxiliary ellipse parameters, loss of contacts, and
stationary-versus-minimizing distinctions are artifacts of an unnecessarily
narrow witness representation, not new obligations for Corollary D.

The returned argument also does **not** close tied Newton faces. Its dense-set
hypothesis must consist of configurations for which a complete path of length
at most `2` in the closed lemniscate has been proved. The currently proved
unique-face result covers monotone unique outer faces in the near-Fekete local
model; it is not a theorem that all unique-face configurations form such a
globally successful dense class in `K_n`. Replacing that missing global path
theorem by an assumed closed witness relation would be circular. The exact
residual therefore remains the producer half: construct length-`<= 2` paths on
some genuinely dense subclass (or prove the bound directly everywhere).

**What the hypothesis must actually deliver.** Corollary D transports a
*path*. A generic theorem that proves containment, a slack inequality, or a
component-identity statement without exhibiting a path of length at most `2` in
the closed lemniscate of the normalised polynomial is not in the scope of this
reduction.

## 5. Theorem E — the constant is exactly attained, and the extremal is rigid

> **Theorem E.** `Lam(z^n - 1) = 2` for every `n >= 2`.

*Proof.* Write `g = z^n - 1` and `w_k = exp(2 pi i k/n)`.

**Upper bound.** For `t in [0,1]`, `|g(t w_k)| = |t^n - 1| = 1 - t^n <= 1`, so
each radial segment `[0, w_k]` lies in `{|g| <= 1}`. The concatenation
`w_i -> 0 -> w_j` has length exactly `2`, so `Lam <= 2`.

**Sublevel characterisation.** `|z^n - 1| <= 1` is `|z|^{2n} - 2 Re(z^n) + 1 <= 1`,
that is

```text
|z|^{2n} <= 2 Re(z^n).                                            (E)
```

**Petal split.** If `z` satisfies (E) and `z != 0`, then
`Re(z^n) >= |z|^{2n}/2 > 0`. Writing `z = rho exp(i theta)` with `rho > 0`,
this says `cos(n theta) > 0`, i.e.

```text
theta in S_k := ( 2 pi k/n - pi/(2n),  2 pi k/n + pi/(2n) )
```

for exactly one `k` modulo `n`. Consecutive sector centres are `2 pi/n` apart
and each sector has half-width `pi/(2n) < pi/n`, so the `n` open sectors are
pairwise disjoint. Hence

```text
{|g| <= 1} \ {0}  =  disjoint union over k of ( {|g| <= 1} cap S_k ),
```

a partition into relatively open sets, with `w_k` in the `k`-th piece. (This is
`negative_results` entry 29 for the open sublevel set; the statement above is
the closed-lemniscate form, and the sector computation is the reason.)

**Lower bound.** Let `gamma` join `w_i` to `w_j`, `i != j`, inside
`{|g| <= 1}`. If `gamma` avoided `0`, its image would be a connected subset of
`{|g| <= 1} \ {0}`, hence contained in a single sector piece — impossible,
since `w_i` and `w_j` lie in different pieces. So `gamma(t_0) = 0` for some
`t_0`, and

```text
len(gamma) >= |w_i - 0| + |0 - w_j| = 2.
```

Hence `Lam(z^n - 1) = 2`. ∎

Theorem E is the exact reason no *chord* argument can be universal: at `r = 1`
every chord between two roots of unity is strictly shorter than `2` and
therefore, by the lower bound, cannot lie in `{|g| <= 1}`. That recovers
`negative_results` entry 9 from the geometry rather than from a witness.

For `r < 1` the same radial construction gives `Lam(z^n - r^n) <= 2r`, and the
origin is interior, so the petal argument does not apply and no matching lower
bound is claimed here.

## 6. Theorem Q — the unrestricted problem as one extremal question

> **Theorem Q.** For each `n >= 2` the following are equivalent.
>
> 1. Erdős #1041 holds in degree `n`: every monic degree-`n` polynomial with
>    all roots in the open unit disk has two roots joined by a curve of length
>    `< 2` inside `{|f| < 1}`.
> 2. `Lam(g) <= 2` for every `g in K_n`.
> 3. `sup { Lam(g) : g in K_n } = 2`.

*Proof.* (2) implies (1) is Corollary S. For (1) implies (2), let `g in K_n`
and put `g_v(z) = s_v^n g(z/s_v)` with `s_v = 1 - 1/v`; then `g_v` is monic with
roots `s_v b_j` in the open unit disk, and `g_v -> g` in coefficients. By (1)
there are two roots of `g_v` joined inside `{|g_v| < 1} subset {|g_v| <= 1}` by
a curve of length `< 2`, so `Lam(g_v) <= 2`; Theorem L gives `Lam(g) <= 2`.
(2) and (3) are equivalent by Theorem E, which supplies `sup >= 2`. ∎

So the unrestricted problem is exactly the assertion that `z^n - 1` maximises
`Lam` on the compact class `K_n`. Note what is **not** claimed: `Lam` is lower
semicontinuous, so it attains its **minimum** on `K_n`, not its maximum. The
supremum in (3) is attained if and only if the conjecture holds, at `z^n - 1`.

## 7. The semicontinuity dichotomy

| direction | statement | status |
|---|---|---|
| lower | `Lam(f) <= liminf Lam(g_v)` — transport a path **to** the limit | Theorem L, unconditional, no margin |
| upper | `limsup Lam(g_v) <= Lam(f)` — transport a path **from** `f` | the content of the collar/slack producer |

The producer is the upper half. Entry 3 shows it admits no uniform modulus, and
under the conjecture it would follow trivially from `Lam <= 2 = Lam(z^n - 1)`
at the only place it is tight — so it is neither free nor decisive. The
reduction uses only the lower half. Nothing in this note proves or disproves
upper semicontinuity; it proves that no argument in this directory has to.

## 8. Appendix — the direct positive solution of the producer, recorded but not used

The producer also has a direct affirmative answer by a value-preserving
holomorphic isotopy, which is worth keeping because it is quantitative and may
be reusable where an actual comparison of two nearby polynomials is wanted.

Let `f` be a polynomial, `A` compact inside an open `U` on which `f'` has no
zero, and `h(z) = lambda z + beta`, `F_s = f + s h` for `s in [0,1]`. Put

```text
m = min over closure(U) of |f'|,      Z = max over closure(U) of |z|,
H = Z |lambda| + |beta|,              d = dist(A, complement of U),
M = max over conv(closure(U)) of |f''|,
delta = H/(m - |lambda|),             B = |lambda| + M delta,
```

and assume `|lambda| < m`, `delta < d`, `B < m`. Integrating the non-autonomous
holomorphic field `X_s(z) = -h(z)/F_s'(z)` gives an injective isotopy `Phi_s`
near `A` with `Phi_0 = id` and

```text
d/ds [ F_s(Phi_s(z)) ] = h(Phi_s z) + F_s'(Phi_s z) X_s(Phi_s z) = 0,
```

so `F_s(Phi_s(z)) = f(z)` — the **complex value**, not just its modulus, is
preserved. Differentiating in `z` gives `F_s'(Phi_s(z)) Phi_s'(z) = f'(z)`,
and `|F_s'(Phi_s z) - f'(z)| <= M |Phi_s z - z| + |lambda| <= B`, whence

```text
m/(m + B) <= |Phi_s'| <= m/(m - B)     on A.
```

Level curves therefore map to level curves at the same level and the same
argument, lengths distort by at most those factors, the transported collar
slack satisfies `q_{F_s} >= (m/(m+B)) q_f > q_f/2`, and the argument principle
along `Phi_s(Gamma)` shows the transported Jordan curve bounds a component of
`{|F_s| < r}` with the same zero count. A Rouché budget on disjoint root disks
supplies the root-transfer cost.

This is a correct theorem and it satisfies the producer as literally stated. It
is recorded rather than landed as the route, because Corollary D deletes the
obligation instead of discharging it: every constant above is
polynomial-dependent, exactly as entry 3 requires, whereas Corollary D needs no
constant at all.

## 9. What is not first here

* The minimum-enclosing-disk normalisation, `R < 1`, and the observation that
  both strict inequalities come from the normalisation rather than the
  hypothesis: `VisibilityOverlapReduction.md` §3, and
  `AdaptiveMecDichotomyLab.md` §1 for the same rescaling.
* `mu(g) <= 1` by Fekete: `VisibilityOverlapReduction.md` §3(a),
  `negative_results` entry 23.
* The splitting of `{|z^n - 1| < 1}` into `n` components meeting only at the
  origin: `negative_results` entry 29. §5 gives the closed form and the sector
  computation, and uses it for a length lower bound, which entry 29 does not.
* Arzelà–Ascoli and lower semicontinuity of length are classical.
  `VisibilityOverlapReduction.md` §2 already uses both, but for a **fixed**
  polynomial, to close the visibility sets `S_j`. Theorem L uses them **across**
  polynomials; that is the only difference, and it is the whole content.
* The descent arc as a rectifiable analytic arc: `AffineNormalisedModuli.md`
  Theorem B.

## 10. Claim boundary

**Proved, by ordinary mathematics:** Theorem L; Corollaries D and S; Theorem E,
including the exact sublevel characterisation (E), the sector split and the
length lower bound; Theorem Q; the appendix isotopy identities and the
distortion bounds `m/(m+B) <= |Phi_s'| <= m/(m-B)`.

**Not proved:** Erdős #1041, in any degree not already closed elsewhere in this
directory. Theorem L transports a path; it never produces one. Nothing here
says which dense class is easier to attack, and nothing here bounds
`sup Lam`. Upper semicontinuity of `Lam` is untouched.

**Verified formally:** the a priori containment (L1), the affine strictification
arithmetic of Corollary S, the closed-sublevel-plus-dense skeleton of Corollary
D, its compact-witness projection wrapper (without any selector), the
uniform-limit Lipschitz bound behind (L2)–(L3), and the sublevel
characterisation and strict positivity `Re(z^n) > 0` of §5, in
`GenericSufficiencyClosure.lean`. Arzelà–Ascoli itself is not formalised here.

**Not established: novelty.** Theorem L is an elementary compactness argument
and the extremal computation in §5 is a short exercise. Both should be assumed
classical, or at least folklore, until a priority search says otherwise. What
is claimed is the **use**: that the closedness of `{Lam <= 2}` retires
`collar_component_and_slack_stability_after_generic_perturbation`, and that
Theorem Q turns the unrestricted problem into a single extremal statement about
`z^n - 1` on a compact class.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_generic_sufficiency_closure.py
lake env lean research_corpus/Erdos1041/GenericSufficiencyClosure.lean
```
