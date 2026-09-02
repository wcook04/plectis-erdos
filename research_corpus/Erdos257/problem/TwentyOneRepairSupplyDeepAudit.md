# Repair-supply deep audit: (CD120)/(M120R)/(PM120) are false

Status: theorem-grade exact falsification on the validated zero-undecided orbit,
2026-08-23. Companion executable
`../../scripts/twenty_one_repair_supply_deep_audit.py`; receipt
`../../../../../state/formal_math/erdos257_period_noncollapse/twenty_one_repair_supply_deep_receipt.json`.
This note does not claim a solution of Erdős problem 257.

## 1. Why this audit had to run before any proof effort

`RecordCofinitenessBoundary.md` §5 verified the repair family

\[
\tag{M120R} f(120k)\ge Q_{120k-1}+t_{120k},
\qquad
\tag{PM120} \textstyle\sum_{d\mid 120k,\ d<120k}b_d\ge Q_{120k-1}+1,
\qquad
\tag{CD120} Q_{120k}\le Q_{120k-1}
\]

on all 16,666 multiples of 120 through rank 2,000,002 with zero violations, and
named `(CD120)` the shortest unconditional route to a disproof. But the
strictly stronger past-owned shortcut `(PU120)` had also passed that same
horizon before failing first at rank 3,175,080
(`PrimorialProducerFalsification`). A producer that survived one audit horizon
has already once been a trap. This audit applies the horizon that killed
`(PU120)` — rank 20,000,002 on the same rigorously bracketed engine — before
anyone spends proof effort on `(CD120)`.

Engine validation carried by the run itself: pinned itinerary count 249,858 at
rank 500,002 reproduced; zero undecided decisions; minimum decision margin
3,139,869,089 units against a rigorous error bracket of 10,760 (safety factor
2.9·10⁵); and the known `(PU120)` falsification reproduces exactly (17
violations, first at 3,175,080, minimum margin −3).

## 2. Result: the periodic repair family is false

Through rank 20,000,002:

| producer | rows | violations | first violation | min margin |
|---|---:|---:|---:|---:|
| `(PU120)` | 166,666 | 17 | 3,175,080 | −3 |
| `(PM120)` | 166,666 | 14 | 3,175,080 | −3 |
| `(M120R)` = `(CD120)` | 166,666 | 6 | 5,686,680 | −3 |

All six `(M120R)` violation certificates have prime cofactor `k`
(5 primes, one `2·prime`) — the same failure class as `(PU120)`:

| n | k | kind | f(n) | b_n | Q_{n−1} | margin |
|---:|---:|---|---:|---:|---:|---:|
| 5,686,680 | 47389 | prime | 16 | 1 | 16 | −1 |
| 7,091,160 | 59093 | prime | 11 | 0 | 11 | −1 |
| 9,724,560 | 2·40519 | composite | 12 | 0 | 13 | −2 |
| 10,251,240 | 85427 | prime | 14 | 1 | 14 | −1 |
| 11,496,120 | 95801 | prime | 11 | 0 | 13 | −3 |
| 13,680,120 | 114001 | prime | 12 | 0 | 12 | −1 |

At the earlier row 3,175,080 the self-bit rescues `(M120R)` while killing
`(PM120)`: `f(n)=Q_{n−1}=12` with `b_n=1`, so the proper load alone (11)
falls one unit short. The strict hierarchy of the three producers is thereby
confirmed row-by-row, and all three die inside the old `(PU120)` failure
neighbourhood.

## 3. Why `(CD120)` was structurally doomed

For prime `k`, `τ(120k)=32`: the divisor load of a prime-cofactor column is
bounded once and for all, while the running maximum of `Q` grows without a
known bound (128 by rank 18,960,479, tracking ≈(ln N)² across the audited
decades). Failures begin as soon as high-defect rows start meeting low-load
prime columns: the six violations sit at defects 11–16 against loads 11–16.
This is an explanation of the observed failure class, not a proof of eventual
collapse; the collapse itself is already a computed fact above.

## 4. The corrected producer: cofinal repairs, not periodic repairs

The boundary theorem consumes only a *cofinal* supply of non-record ranks;
the multiple-of-120 column was merely the conjectured periodic subfamily. The
global census at the same depth says the actual supply is far stronger:

* 8,859,815 one-step repairs among 20,000,002 ranks — density 0.443;
* maximum repair gap **11**, attained starting near rank 12,156,133; last
  repair at the horizon end;
* gap law by decade of rank: max gap 2, 4, 6, 8, 10, 10, 11 — growth like
  ≈2·log₁₀(N) with strong saturation, mean gap drifting only 1.32 → 2.28;
* after rank 3,200,000 the surviving repairs use **all 120 residue classes**
  mod 120 — the supply is not migrating to another single progression;
* non-record ranks are 19,999,946 of 20,000,002; 56 strict records; maximum
  defect 128.

So the live open producer sharpens to its weakest useful form:

\[
\boxed{\text{(CRG)}\quad \text{one-step repairs } f(n)\ge Q_{n-1}+t_n
\text{ occur beyond every cutoff}.}
\]

Any all-depth bound of the shape "repair gap ≤ g(N)" — bounded, logarithmic,
or even just cofinality itself — proves `(CRG)`, hence no final skip, hence
`1/21 ∈` mersenneAchievementSet by the Lean-checked cofinal-skip
characterization, hence an infinite representing support by
`finiteErdosSum_ne_one_div_twenty_one`, hence ¬Universal. The measured gap
law suggests the honest conjecture is "max repair gap ≤ C·log N"; even the
qualitative statement is sufficient.

## 5. What changed in the frontier

1. `(CD120)`, `(M120R)`, `(PM120)` move from *open producers* to
   *falsified* — they must not be cited as live routes, and any Lean module
   or audit text still listing them as open targets inherits a false
   hypothesis.
2. The shortest live disproof route on this lane is now `(CRG)` +
   boundary theorem + cofinal-skip characterization + finite-support
   exclusion. Every consumer after `(CRG)` is already checked or proved.
3. `(DRMH)`/record-midpoint remains the alternative live lane, untouched by
   this falsification (its own 20M discriminator passed; see
   `TwentyOneRunningMaximumProducerAudit.md`).
4. The failure anatomy concentrates all four dead producers on prime-cofactor
   columns. Any future periodic-column candidate should first be stress-tested
   against the prime-cofactor subclass at depth ≥ 10⁷, where defect values
   11–16 collide with divisor-capped loads.

## 6. Reproduction

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  twenty_one_repair_supply_deep_audit.py
```

Runtime ≈ 40 s. Exit code 0 requires: pinned match, zero undecided decisions,
and reproduction of the `(PU120)` falsification at depth.

## 7. Claim ceiling

Finite exact falsifications and finite exact survival statistics. No claim is
made about `(CRG)`, 1/21 membership, or Erdős problem 257. No finite run can
supply the cofinal quantifier.
