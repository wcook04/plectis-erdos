# The socket lane, pointed at the actual candidates — and rationality's own cap

Status labels are strict. **[PROVED]** = elementary derivation, given here and in Lean.
**[COMPUTED]** = exact integer computation, reproducible from the named script.

Scripts: `scripts/socket_parity_on_candidates.py`, `scripts/socket_run_rational_cap.py`.
Lean: `ErdosProblems/Erdos257/SocketRunRationalCap.lean`.
Receipts: `state/formal_math/erdos257_period_noncollapse/socket_parity_on_candidates_receipt.json`,
`…/socket_run_rational_cap_receipt.json`.

## 0. The gap this fills

`CertificateSocketCollapse.md` section 46 proves the parity obstruction — with
`Odd_A := {m : τ_A(m) odd}`, every socket run fits strictly between consecutive elements of
`Odd_A`, so `maxrun ≤ maxgap(Odd_A) − 1`, and syndetic `Odd_A` makes the Erdős-1948
mechanism *unavailable*. Section 66 adds `Odd_{ℕ∖E} = Sq XOR Odd_E`.

**Neither was ever evaluated on a candidate counterexample.** Section 46's census covers
`ℕ`, primes, `{2^i}`, `{3^i}`, `3ℕ`; section 66's table covers `{}`, `{2^i}`, primes,
`{2^i} XOR primes`, `4ℕ`. All are *constructed* supports. The greedy supports of
`1/2, 1/21, 4/9, 1/465, 1/5, 5/12` appear in neither.

## 1. The bridge to the carry lane [PROVED]

Sections 3 and 11 give `ε_m = (τ_A(m) + C_m) mod 2`. Hence for the greedy support of any
rational target,

    Odd_A  =  { m : τ_A(m) odd }  =  { m : ε_m ≠ C_m mod 2 },                      (P)

so `Odd_A` is exactly the disagreement set of the periodic digit word and the carry parity,
and `maxgap(Odd_A)` is the longest run on which they **agree**. This connects section 46's
parity obstruction to section 11's transducer; the two lanes were previously unlinked.

## 2. The obstruction is LOOSE on every candidate [COMPUTED]

Depth 20,000, exact integer arithmetic. Calibrator in the same run, per corpus discipline:
`A = ℕ` reproduces `Odd_ℕ = squares` exactly, maxgap **281** against `2√M = 282`, density
`0.00705`.

| `y` | (P) viol | density `Odd_A` | maxgap | socket maxrun | `max τ_A` | magnitude cap | parity cap | binds |
|---|---|---|---|---|---|---|---|---|
| `1/2` | 0 | 0.50530 | 17 | 2 | 40 | 5 | 16 | **magnitude** |
| `1/21` | 0 | 0.50205 | 14 | 3 | 40 | 5 | 13 | **magnitude** |
| `4/9` | 0 | 0.49895 | 17 | 3 | 41 | 5 | 16 | **magnitude** |
| `1/465` | 0 | 0.50125 | 13 | 3 | 36 | 5 | 12 | **magnitude** |
| `1/5` | 0 | 0.50340 | 12 | 3 | 38 | 5 | 11 | **magnitude** |
| `5/12` | 0 | 0.48695 | 14 | 3 | 41 | 5 | 13 | **magnitude** |

* **(P) is exact** — zero violations at every rank, every candidate.
* **`Odd_A` is not syndetic**: maxgap grows slowly with the dyadic band (`b6: 4–8` up to
  `b15: 9–14`), consistent with `~log₂ M` rather than the `~√M` of the calibrator.
* **Density is `≈ 1/2`** for every candidate, against `0.007` for `A = ℕ`. A density-`1/2`
  support makes `τ_A(m) mod 2` a sum of `d(m)` fair bits; the squares structure of `Odd_ℕ` is
  a density-zero phenomenon and does not survive to the candidates.
* **The binding constraint is magnitude, not parity, for all six.** A run of length `K` needs
  `τ_A(N+k) ≥ 2^k`, so `K ≤ log₂ max τ_A = 5`, while section 46's parity cap permits 11–16.

> **Section 46's kill class does not reach the candidates**, and the reason the socket route
> fails on them is divisor magnitude. Anyone attacking a candidate through Erdős 1948 must
> beat `τ_A` magnitude — go to primorial towers, as Erdős's own construction does — not
> parity.

## 3. Rationality supplies its own cap, and it lands on the carry [PROVED]

A socket run of length `K` at `N` makes each head term `τ_A(N+k)·2^(−k)` an integer, so

`frac(2^N y) = frac(Σ_{k>K} τ_A(N+k) 2^(−k)) ≤ Σ_{k>K} τ_A(N+k) 2^(−k) = S / 2^K`,

where `S := Σ_{j≥1} τ_A(N+K+j) 2^(−j)` is the local divisor mass whose floor is the forward
carry, so `S < C_{N+K} + 1`. If `y = p/q` in lowest terms with `q` odd, `frac(2^N y)` is a
multiple of `1/q`, hence vanishes or is `≥ 1/q`. Therefore

> **Theorem (rational socket cap).** `2^K < q · (C_{N+K} + 1)`, i.e.
> `K < log₂ q + log₂(C + 1)`.

Lean: `socketRun_cap_of_rational`, `socketRun_cap_nat`, `no_rational_of_long_socketRun`, and
the head-integrality lemma `socketHead_integral`. Build `rc = 0` captured, 3285 jobs,
serialized Lake authority replay; axioms `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`.

**The contrapositive is the producer shape:** a support exhibiting socket runs longer than
`log₂(q(C+1))` cannot sum to `p/q`.

## 4. The cap is tight, not vacuous [COMPUTED]

Depth 8000, every socket run of every candidate:

| `y` | runs | violations | tightest `q(C+1)/2^K` | at `N` | `K` | `C` |
|---|---|---|---|---|---|---|
| `1/2` | 0 | 0 | **dyadic — vacuous** | | | |
| `1/21` | 3034 | **0** | 5.25 | 38 | 2 | 0 |
| `4/9` | 3329 | **0** | 2.25 | 3287 | 3 | 1 |
| `1/5` | 3112 | **0** | **1.25** | 68 | 2 | 0 |
| `5/12` | 3230 | **0** | 4.50 | 457 | 3 | 2 |
| `1/465` | 2907 | **0** | 116.25 | 134 | 2 | 0 |

**15,612 runs, zero violations, tightest ratio 1.25.** `1/2` is dyadic, so
`frac(2^N y) = 0` for every `N ≥ 1` and every run is the excluded case — which is exactly
why Erdős's criterion always excludes dyadic `y`, and it falls out of the instrument rather
than being assumed.

## 5. Classification against the closeout's allocation guard [and it goes against this note]

`Erdos257ResearchFrontierCloseout.md` is the authority on mechanism families, and it was
unread when sections 1–4 were written. Applying it here, as `CertificateSocketCollapse.md`
section 76.4 applies it to section 66:

The closeout lists five proof shapes for which **the corpus already contains exact
countermodels** — among them *"a bounded window of divisor loads"* and *"scalar residual mass,
denominator height, support count, or phase"*. The rational socket cap uses exactly a bounded
window (the run window of length `K` and the local mass `S`) together with one scalar (`q`).
**It sits inside two of the five forbidden shapes.** The countermodels *"can reproduce an
arbitrarily long dangerous suffix together with all local divisor congruences"*, so they
survive the cap.

The allocation guard is explicit about the bar:

> "A reopened route must supply at least one genuinely new producer: a one-way theorem from
> the actual initial state that uses the complete Boolean/divisor ancestry (or proves why a
> smaller state is sufficient) and forces a cofinal return, excludes the boundary mode, or
> constructs an admissible infinite support. Finite checks are consistency and falsification
> evidence only."

**The cap does not clear that bar.** It is source-insensitive — it never touches the actual
initial state or the earlier divisor ancestry — and its census is a finite check. It is a
correct, tight, machine-checked *necessary condition*, and it is **not a new route**. It does
not create a mechanism family; the count remains twenty-five.

What survives classification, stated at its true size:

* the cap as a **falsifier**: a candidate exhibiting a socket run longer than `log₂(q(C+1))`
  is excluded. That is a real test, though no one can currently force such runs;
* the identity `Odd_A = {m : ε_m ≠ C_m mod 2}`, linking section 46's parity lane to the
  section 11 transducer — a dictionary entry, not a producer;
* section 2's census, which removes the reading that section 46's kill class might already
  cover the candidates. That is a one-way negative and it stands.

Per the closeout's final paragraph, no route ranking is inherited from any of this: *"no entry
or working-memory surface may inherit a next route from this document."*

## 6. What this does not claim

* Nothing here proves or refutes Erdős 257, and nothing here proves any irrationality.
* Section 3's theorem is a **necessary condition on a counterexample**, not a producer. It
  becomes a producer only when someone forces long socket runs on a candidate support, which
  no one has.
* The Lean module is the abstract inequality, with the divisor theory in prose — the same
  scope convention `PrimeSlackTwoValued.lean` uses for section 84.
* Section 2's maxgap growth is **[COMPUTED]** to depth 20,000 on six targets. It does not
  prove `Odd_A` is non-syndetic for any candidate; it removes the reading that section 46's
  kill class might already cover them.
* T12 applies to the socket maxrun figures: finite search never refutes existence, and
  section 46 makes the same caveat for its own `A = ℕ` row.
