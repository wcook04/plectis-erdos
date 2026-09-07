# Erdős 1041: the cubic spoke identity generalises to every degree

Status: one identity, proved and verified symbolically at `n = 3, 4, 5, 6`, plus
the containment criterion it yields. 2026-08-23. This does not prove Erdős
#1041. It converts straight-spoke containment at a normalised hub from a
path-tracking question into an explicit algebraic one, at every degree.

## The normalisation

Let `c` be a critical point of monic `f` with `f(c) != 0`. Translate `c` to the
origin and scale by `lambda = f(c)^{1/n}`, dividing through by `f(c)`. The
result is

```text
G(w) = w^n + a_{n-1} w^{n-1} + ... + a_2 w^2 + 1,
```

with **no linear term** — that is exactly `G'(0) = 0` — and `G(0) = 1`. Lengths
in the original coordinates are `|f(c)|^{1/n}` times lengths in `G` coordinates,
and `|f| < 1` becomes `|G| < 1/|f(c)|`, which is weaker than `|G| <= 1` because
`|f(c)| < 1`. So it suffices to keep `|G| <= 1` on a spoke.

## The identity

Let `w` be a **root** of `G` and set `c_k = a_k w^k` for `k = 2, ..., n`, with
`a_n = 1` so `c_n = w^n`. Since `G(w) = 0`,

```text
sum_{k=2}^{n} c_k = -1.                                            (*)
```

> **Identity (S).** For every `t`,
>
> ```text
> G(tw) = (1 - t^2) - t^2 (1 - t) Q(t),
>     Q(t) = sum_{k>=3} c_k (1 + t + t^2 + ... + t^{k-3}).
> ```

*Proof.* `G(tw) = 1 + sum_{k>=2} c_k t^k`. Subtract and add `t^2` using (*):
`G(tw) = (1 - t^2) + sum_{k>=2} c_k (t^k - t^2)`. The `k = 2` term vanishes, and
for `k >= 3`, `c_k(t^k - t^2) = -c_k t^2 (1 - t^{k-2})` with
`1 - t^{k-2} = (1-t)(1 + t + ... + t^{k-3})`. ∎

Verified symbolically with the root relation imposed: the difference
`G(tw) - [(1-t^2) - t^2(1-t)Q(t)]` simplifies to exactly `0` at `n = 3, 4, 5, 6`.

## The containment criterion

Since `1 - t^2 >= 0` on `[0,1]`,

```text
|G(tw)| <= (1 - t^2) + t^2 (1-t) |Q(t)|,
```

and the right side is at most 1 precisely when `t^2(1-t)|Q(t)| <= t^2`. Hence

> **Criterion (SC).** If `(1 - t) |Q(t)| <= 1` for all `t` in `[0,1]`, then
> `|G| <= 1` on the entire straight spoke from `0` to the root `w`, so that spoke
> lies in the target lemniscate.

**This recovers the cubic case exactly.** At `n = 3` the sum has one term and
`Q(t) = c_3 = w^3` is constant, so (S) reads
`G(tw) = 1 - t^2 - t^2(1-t)w^3` — which is verbatim the identity in
[CubicCriticalHub.md](CubicCriticalHub.md) — and (SC) reads
`(1-t)|w|^3 <= 1`, guaranteed by `|w| <= 1`, which is that proof's condition.
The reduction was checked symbolically.

**Quartic specialisation.** At `n = 4`, `Q(t) = a_3 w^3 + (1 + t) w^4`, so the
criterion is

```text
max_{t in [0,1]} (1 - t) | a_3 w^3 + (1 + t) w^4 |  <=  1.
```

A crude sufficient form is `|a_3||w|^3 + 2|w|^4 <= 1`, but the maximum is
attained in the interior of `[0,1]` and the sharp form is materially weaker;
anyone using this should compute the sharp maximum rather than the crude bound.

## What this buys, and what it does not

Containment on a spoke becomes an explicit algebraic condition in the normalised
coefficients and the root, with **no path tracking at all**. That matters here:
this directory records four false counterexamples that were all branch-tracking
artifacts, and a shared-engine defect that puts start directions up to 50 degrees
out. (SC) is immune to both.

For a length bound one still needs roots close to the hub. The product of the
roots of `G` has modulus 1, so **some** root satisfies `|w_i| <= 1` — but that is
only one. Two roots with `|w_i| <= 1` and both spokes contained would give total
length `2|f(c)|^{1/n} <= 2R < 2` by the discriminant/Fekete bound `T* <= R^n`,
which is the whole conjecture at that hub.

**So the mechanism reduces to: at the minimal-critical-value hub, what forces a
*second* root of the normalised polynomial into the closed unit disk?**

## Correction, 2026-08-23: the section below overstated its conclusion

**The heading that follows originally read "Answer: nothing does, from degree
four onward", and the claim that the second-root premise is FALSE at degree four
is retracted.** The measurement is right; the inference was not, and it was wrong
twice over.

*First error.* The premise was tested in its **crude** form `|w_i| <= 1`, not in
the actual criterion (SC). Re-testing the three stored witnesses against the
sharp form `max_t (1-t)|Q(t)| <= 1`, **two** roots pass at every one of them —
`(0.7709, 1.0280)`, `(1.0514, 0.7541)`, `(0.7619, 1.0340)` with SC values between
`0.49` and `0.67` — and both spokes really are contained. A root at `|w| = 1.028`
passes SC at `0.512` while the crude bound evaluates to `2.97` there and is
useless. So those three configurations **satisfy** the mechanism rather than
refuting it, and they are not witnesses to anything.

*Second error, found while fixing the first.* The length requirement was also
overstated. A spoke from `c` to root `z_i` has length `lambda |w_i|` with
`lambda = |f(c)|^{1/n} < 1` at any admissible hub, so two spokes total
`lambda(|w_1| + |w_2|) < |w_1| + |w_2|`. Hence

> two roots satisfying (SC) with `|w_1| + |w_2| <= 2` suffice.

Individual `|w_i| <= 1` is **not** needed. Sampling minimal-hub configurations,
the "two roots pass SC" and "two roots pass SC with sum `<= 2`" counts are
*identical* at every degree tested — 35430/35430 at `n = 3`, 23988/23988 at
`n = 4`, 7970/7970 at `n = 5` — so the sum condition never binds and the sharp
criterion is the whole content.

*Why no replacement witness is offered here.* Configurations where fewer than two
roots pass (SC) do exist from degree four (552 of 24540 minimal-hub cases at
`n = 4`, 128 of 8098 at `n = 5`). But at three such configurations examined
directly, **two spokes were still contained** — `max |G| = 1.000000000` — because
(SC) is sufficient and not necessary, and is lossy by roughly 10 percent at the
margin. So SC failure does not establish containment failure, and no honest
witness to the premise failing can be built from SC alone.

The question of whether *sublevel* containment on two spokes survives at degree
four is settled elsewhere and not by this note:
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §2 records
that the sublevel straight-spoke form dies at degree four, with its own exact
witnesses. That remains the authority. What this note contributes is the identity
(S), the criterion (SC), and the corrected sufficient condition above — not a
degree-four refutation.

## Retracted: what the measurement does and does not show

Two facts are automatic in the normalisation. The constant term gives
`prod |w_i| = 1`, and `G'(0) = 0` gives `sum 1/w_i = 0`. Together they yield
**one** root with `|w_i| <= 1`, never two. Choosing the hub of least critical
value is exactly the condition

```text
|G(c')| >= 1   at every other critical point c' of G,
```

since `|G(c')| = |f(c')|/|f(c)|` and `|G(0)| = 1`. At `n = 3` that minimality
supplies the second root. **At `n = 4` it does not, and the failure is exhibited,
not conjectured.**

Sampling normalised `G`, keeping only minimal-hub configurations, and counting
roots in the closed unit disk:

| n | sampled | minimal-hub | exactly one root inside | fewest inside |
|---|---|---|---|---|
| 3 | 400000 | 236554 | **0** | 2 |
| 4 | 400000 | 164174 | **508** | **1** |
| 5 | 200000 | 55409 | **2** | **1** |
| 6 | 200000 | 37670 | 0 | 2 |
| 7 | 200000 | 27257 | 0 | 2 |

Three degree-four witnesses are stored as exact IEEE-754 hexadecimal literals in
[`scripts/check_erdos1041_second_root_premise.py`](scripts/check_erdos1041_second_root_premise.py)
and replay at 50 digits with `|G(root)| ~ 1e-15`: minimal hub confirmed (other
critical values `1.0075` to `1.0317`, all `>= 1`), and root moduli such as
`0.7709, 1.0280, 1.0928, 1.1546` — one inside, three outside, with the nearest
outsider only `1.028` from the unit circle, which is why the configurations are
stored in hex rather than decimals.

The zero counts at `n = 6, 7` are sampling statements only and must not be read
as the premise holding there; `n = 5` produced just 2 failures in 55409
minimal-hub configurations, so absence at a given sample size means little.

**This is an independent rediscovery of a boundary already on file.**
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §2 records
that the *sublevel* straight-spoke form "dies at degree four". What is added here
is the mechanism: the identity (S) is perfectly general, and what breaks at
degree four is not the containment estimate but the supply of a second root
inside the unit disk at the minimal hub. So the degree-three theorem does not
extend, and the reason is arithmetic rather than geometric.

Two independent reasons this is not a proof of anything beyond degree three, both
already on file: the *sublevel* straight-spoke form is recorded as dying at degree
four, and the *open* form at degree six, where
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) §3 exhibits
exact witnesses with no admissible hub carrying two contained spokes. (SC) is a
sufficient condition, not a necessary one, so those witnesses bound how far it
can reach: at degree six it must fail at every hub.

## Claim boundary

Proved: identity (S) and criterion (SC), by elementary algebra, verified
symbolically at `n = 3, 4, 5, 6`, with the `n = 3` case checked to reduce to the
corpus's existing cubic identity.

Not established: that two roots satisfy (SC) at any selected hub for `n >= 4`;
any length bound; anything about degrees where straight spokes are already known
to fail. Erdős #1041 remains open.

Receipt: [`scripts/check_erdos1041_general_spoke_identity.py`](scripts/check_erdos1041_general_spoke_identity.py).
