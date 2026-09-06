# Erdős #243: unit record-increment rigidity under arbitrary cancellation

This package isolates the composed true-record-increment consequence of the
weighted-record octuple's `r01` return, for exact primitive reciprocal-tail
dynamics with arbitrary (unbounded) cancellation

\[
w_n+v_n=a_nu_n,\qquad w_n=h_nu_{n+1},\qquad a_nv_n=h_nv_{n+1},\qquad
\gcd(u_n,v_n)=1,
\]

with `vₙ, wₙ > 0`. Write the centred error as

\[
e_n = v_n-(a_n-1)u_n.
\]

Assume the eventual nearest-integer centring bound `2|eₙ| < uₙ`, division-free
normalized vanishing (`K|eₙ| < uₙ` eventually for every fixed `K`), the TRUE
record-increment bound

\[
R_{n+1}-R_n\le 1,\qquad R_n=\max_{k\le n}u_k,
\]

and a fresh prime-power supply of the reduced denominator dominating the
current record: `p^l \mid v_s` with `R_s+3\le p^l` at arbitrarily late indices
`s`. The compared theorem proves

- `aₙ₊₁ = aₙ² - aₙ + 1` eventually.

## Mathematical boundary

The unit record-increment bound and the prime-power supply are both
hypotheses; neither is derived here from the underlying dynamics. In
particular the theorem does not bound the record-setting *jump*
`u_{n+1}-u_n` at a step that sets a new record — that jump can be large even
when the true record increment is at most one, because the jump also has to
pay off any drawdown accumulated since the last record:

\[
u_{n+1}-u_n=(R_{n+1}-R_n)+(R_n-u_n).
\]

The fixture `(u,v)=(8,177) \to[a=23] (7,4071) \to[a=583] (10,2373393)` has
true record increment `10-8=2` while its record-setting jump is `10-7=3`, so
the two quantities are genuinely different even in a short segment, and
successive record heights (`8`, `10`) need not be coprime even though
adjacent primitive numerators are. This theorem constrains the increment, not
the jump, so it is incomparable with any theorem stated in terms of
record-setting jumps (such as a two-unit record-jump bound): neither implies
the other, and both are separate hypotheses on the same underlying orbit.
Erdős #243 remains open.

`Challenge.lean` imports only Mathlib and exposes the composed consumer.
`Solution.lean` transports the source-current theorem
`ErdosProblems.Erdos243.recordIncrementOne_sylvesterNext_eventually` by
showing the locally defined `runningMax` agrees with the corpus `runningMax`
(same primitive recursion) and rewriting the `hinc`/`hsupply` hypotheses
across that equality. The deliberate negative keeps every hypothesis but
swaps in the unrelated, strictly weaker vanishing-error conclusion, so
Comparator must reject it as a type mismatch rather than accepting a
watered-down version of the result.

## Verification

From the problem library `ErdosProblems/Erdos243`:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification243RecordIncrementBarrier/Challenge.lean \
  ExternalVerification243RecordIncrementBarrier/Solution.lean \
  ExternalVerification243RecordIncrementBarrier/NegativeSolution.lean \
  ExternalVerification243RecordIncrementBarrier/AxiomAudit.lean
```

The checked-in replay actuator runs the positive and deliberate-negative
Comparator configurations on a supported Linux host. Exit `75` is an
environment-unavailability receipt, not a Comparator verdict.

## Palomar disposition

This is a first-wave Palomar candidate. Eventual exact rigidity of the
multiplier sequence under a true record-increment bound and a recurring
fresh prime-power supply, with no oddness requirement and no bound on the
cancellation factors, is a coherent research-note result with a
number-theory and formal-mathematics audience. The open unrestricted parent
problem is the claim boundary, not a reason to withhold this theorem.

Submission still requires a public GitHub repository at a full immutable
commit SHA, this exact config path, terminal positive acceptance, deliberate
negative rejection, and source-current metadata. These local files are not a
Palomar decision, registry entry, novelty ruling, or peer review.

## File map

- `Challenge.lean` — trusted Mathlib-only statement (one specification `sorry`).
- `Solution.lean` — proof by transport from `ErdosProblems.Erdos243.RecordIncrementBarrier`.
- `NegativeSolution.lean` — deliberately weakened same-named declaration for Comparator's negative-mismatch check.
- `AxiomAudit.lean` — `#print axioms` of the compared declaration.
- `comparator.json` — positive Comparator config (Challenge vs. Solution).
- `comparator-negative-mismatch.json` — negative Comparator config (Challenge vs. NegativeSolution).
- `formalization.yaml` — Palomar submitter metadata.
