# Rational death census — instrument, one kill, and one retraction

Scripts: `scripts/rational_death_census.py`, `scripts/late_hazard_profile.py`
Receipt: `state/formal_math/erdos257_period_noncollapse/rational_death_census_receipt.json`

## 0. RETRACTION, stated first

`late_hazard_profile.py` was built to resolve what I took to be an unexamined
tension: the measure model gives a summable death hazard, so a positive
proportion of targets survive forever, which applied to rationals would refute
Erdos 257. **That tension is not new and was already resolved.**
`erdos257_hole_geometry/notes/ProgrammeSpine.md` section 12 records it as
family **K6**, "killed as *vacuous*, the more dangerous failure — `m(S_N) = 1`
exactly for every `N`, so 'almost every point survives' is true and proves
nothing; `Acal` is a **fat** Cantor set."

The same section records what I had backwards: **survival refutes 257, death
proves it**, and Erdos himself, read in the primary ([11, p.222], *"I know no
example ... though it seems likely that this can happen"*), **expected 257 to
be false**. So a 62% survival rate is not a paradox to be explained away; it is
the expected shape, and it is exactly why measure arguments cannot decide
anything here.

The hazard-profile script is retained only as a certified instrument. Its
framing question is closed. Do not re-derive it.

## 1. What the instrument is, and that it is correct

`rational_death_census.py` runs **every** rational with a fixed denominator,
not a sample. This matters: for small `q` only about `qE` distinct targets
exist, so a random `p/q` ensemble repeats individual targets and any single
unusual target inflates its own rank's death count. A census has no sampling
noise and no repetition confound.

Every take, skip and death decision is certified by integer enclosures at `P`
bits, with an undecidable comparison reported rather than resolved:

    Z[n]  <= 2^P z_n  <  Z[n] + 1
    TT[n] <= 2^P T_n  <  TT[n] + (P - n) + 2

Undecidable **death** tests are reported separately from undecidable **takes**,
because `r ~ T_n` is precisely the interesting event and must never be pooled
with a boundary take. Across every run reported here, `indeterminate_death = 0`.

**Independent verification.** The enclosure engine was checked against an
exact-`Fraction` greedy sharing no code with it, using the rigorous tail bound
`sum_{k>K} 1/(2^k - 1) < 2^{-K+1}`. For `x = 1/257` at depth 60 both engines
agree: alive, residual `3.312695e-19`, against `T_60 = 8.673617e-19`, and the
invariant `0 <= r_60 <= T_60` holds. The support words agree termwise.

## 2. KILLED — the exact `phi(q)` survivor-count law

The census first suggested an exact arithmetic law. At depth 60 the number of
surviving `p/q` was *exactly* `phi(q)`:

| q | targets | survivors | phi(q) |
|---|---|---|---|
| 101 | 161 | 100 | 100 |
| 257 | 411 | 256 | 256 |

That is not the measure prediction and would have been an exact statement about
which rationals are representable. There is even a clean structural reason to
expect an even count: since `z_1 = 1` exactly,

    C = C_{>=2}  disjoint-union  (1 + C_{>=2}),     C_{>=2} subset [0, T_1]

and `p_0/q in C_{>=2}` already forces `p_0 <= q T_1`, so each residue
`p_0 in [1, q-1]` contributes to the survivor count **twice or not at all**.
Hence survivors `= 2 m_q` exactly, and the law would say `m_q = phi(q)/2`.

**The law is false.** Extending the census over nine primes at depth 120:

| q | survivors − phi(q) |
|---|---|
| 101 | 0 |
| 103 | −4 |
| 107 | 0 |
| 109 | +2 |
| 113 | +2 |
| 127 | −2 |
| 257 | 0 |
| 509 | −10 |
| 1021 | −16 |

The deviation grows like `sqrt(q)`, which is exactly equidistribution noise
around `|C_{>=2}| = 1/2`. The three exact hits were coincidence. So the count
carries no arithmetic information beyond the measure `|C| = 1` that K6 already
records as vacuous.

The `survivors = 2 m_q` factorisation above survives as an exact statement, but
it is elementary and follows from `z_1 = 1` alone.

## 3. The horizon, restated as an instrument limit

`ProgrammeSpine.md` section 12: any hypothesis that is a statement about a
finite window of the orbit is an **open condition**, while survival is **nowhere
open**. So no depth `D` this or any census can reach converts "alive at `D`"
into "alive". The census is therefore a *falsifier* only in one direction: it can
kill a candidate denominator by exhibiting death, never confirm one.

Two further reasons the depth axis is treacherous here, both checked:

- `ord_q(2)` is not the relevant horizon. `ord_257(2) = 16`, far inside depth
  60, yet the census records **zero** terminations at `q = 257`. Termination
  needs the remainder to hit exactly zero, which effectively never happens; it
  is not a mechanism that disposes of survivors.
- Survivor support density is `0.4897` (`q = 101`) and `0.5008` (`q = 257`),
  consistent with the `rho -> 1/2` measured in `notes/HarmonicMassOfSupport.md`
  and with supports being harmonically divergent — the regime where neither P1
  nor the reciprocal-summable theorem reaches.

## 4. What this leaves

The only lane `ProgrammeSpine.md` section 12 leaves open is **support-first**: a
divisor-structure statement about `A` from which rationality follows
algebraically. Nothing in this note touches it. Any further orbit-window
statistics, hazard profiles, survival fractions, or denominator censuses are
K6 in a new coordinate and should not be run.
