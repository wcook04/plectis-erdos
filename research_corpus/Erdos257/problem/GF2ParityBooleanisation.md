# The characteristic-two lane's only obstruction is the carry parity, and it is high-entropy

Status labels are strict. **[PROVED]** = elementary derivation given here.
**[COMPUTED]** = exact integer computation, reproducible from the named script.

Script: `scripts/gf2_parity_booleanisation.py`.
Receipt: `state/formal_math/erdos257_period_noncollapse/gf2_parity_booleanisation_receipt.json`.

## 0. The caveat this replaces

`CharacteristicTwoRealLiftScan.md` builds supports by the `F_2` Dirichlet inverse
`b = g * μ (mod 2)`, so that `τ_A(n) ≡ g(n) (mod 2)` exactly, then asks whether the real sum
`S_B = Σ_{b(n)=1} 1/(2^n − 1)` has an eventually periodic binary output. It exhausts 7,650
sources at `D = 1024` and finds none. Its section 4 records what is **not** excluded —
larger source periods, larger real periods — and warns that extending only those bounds is
another horizon audit.

This note does not extend the bounds. It isolates the obstruction, so that section 4's
caveat stops being a horizon and becomes a reason.

## 1. The lane collapses onto one word [PROVED]

The corpus's carry identity (`RunLengthMarginLawAndDivisorMultiplicity.md` sections 3 and
11) is binary addition of the divisor-multiplicity stream:

    ε_m = (τ_A(m) + C_m) mod 2,        C_{m−1} = (τ_A(m) + C_m) div 2.

In the characteristic-two lane `τ_A(m) ≡ g(m) (mod 2)` holds **by construction**, so

    ε_m ≡ g(m) + C_m   (mod 2),

and because `g` is periodic,

> **`S_B` is rational ⟺ `ε` is eventually periodic ⟺ `C_m mod 2` is eventually
> periodic.**    (P)

The lift scan tests the composite real output. (P) says the composite carries no
information the carry parity does not already carry: the whole characteristic-two lift
problem is one binary word, and any future lift law must act on `C mod 2` or on nothing.

## 2. That word is high-entropy [COMPUTED]

Depth 4000, exact integer carries (`C_m = ⌊Σ_{k≥1} τ_A(m+k)2^{−k}⌋`, `K = 64`, zero ranks
with an ambiguous floor), measured on the second half of each word against a matched
Bernoulli null at the same density — the methodology of section 19:

| source `g` | `|A|` | (P) holds | max `C` | `C mod 2` period (pre ≤ 64, per ≤ 512) | `p(12)` | null `p(12)` | entropy |
|---|---|---|---|---|---|---|---|
| squarefree, `10` (pre 1, per 1) | 2433 | yes | 18 | **none** | 1492 | 1570 | 0.9958 |
| `(3,7)` best finite fit `0011111000` | 1959 | yes | 18 | **none** | 1550 | 1612 | 1.0000 |
| period 7 `0110100` | 1731 | yes | 14 | **none** | 1581 | 1615 | 1.0000 |
| period 3 `011` | 430 | yes | 11 | **none** | 1473 | 1584 | 0.9963 |
| period 6 `010011` | 428 | yes | 10 | **none** | 1511 | 1606 | 0.9999 |
| period 5 `01101` | 399 | yes | 10 | **none** | 1482 | 1584 | 0.9967 |
| period 2 `01` | **1** | yes | 0 | `(0,1)` | 1 | 1 | 0.0000 |

Read three things off it.

* **(P) is exact.** `τ_A(m) ≡ g(m) (mod 2)` verified at every rank for every source, which
  is the `F_2` construction working as `CharacteristicTwoRealLiftScan.md` section 1 says.
* **Every infinite support has a high-entropy carry parity.** No eventual period at all up
  to preperiod 64 / period 512; subword complexity indistinguishable from the matched
  Bernoulli null (slightly below it, as finite samples are); entropy within `0.005` of one
  bit. Including the two sources the lift scan singled out — the squarefree witness and the
  best finite fit.
* **The one periodic row is the finite-support case.** `g` of period 2 yields `|A| = 1`
  through depth 4000, `C ≡ 0`, carry parity of period 1 — and a rational value. That is
  exactly the boundary `LambertPeriodicBooleanisationNoGo.md` describes (periodic `τ_A`
  forces every element of `A` to divide the period, hence `A` finite), reappearing inside
  the characteristic-two lane as its only periodic point. The lane's sole success is the
  case that is not a counterexample.

## 3. Consequence

Section 4 of `CharacteristicTwoRealLiftScan.md` reopens the lane only for "a specific lift
law that the present family omits". (P) says where such a law would have to act, and
section 2 says what it is up against: the target word is not merely aperiodic within a
scanned window, it is statistically indistinguishable from a fair coin for every infinite
support tested, and the only periodic instance is finite. A longer scan over larger source
or real periods is therefore not the missing ingredient.

## 4. What this does not claim

* Nothing here proves or refutes Erdős 257, and nothing here proves any irrationality.
* Entropy and subword complexity are **[COMPUTED]** on seven sources to depth 4000. They do
  not prove the carry parity is aperiodic for every source; they remove the reading that a
  bounded-period fit was merely out of scan range.
* (P) is an equivalence, not a producer. It relocates the characteristic-two problem; it
  does not solve it.
* It says nothing about the non-characteristic-two lanes, the prime skeleton, or the
  non-linear residual of `CertificateSocketCollapse.md` 73.4.
