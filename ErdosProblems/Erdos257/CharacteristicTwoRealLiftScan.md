# Characteristic-two supports do not Hensel-lift by Boolean correction

## Status

This is an exact rigidity result plus a bounded exhaustive falsifier for a
direct construction mechanism.  It does not prove Erdős 257 and it does not
promote a source word or rational target.

The characteristic-two Lambert problem has abundant infinite Boolean
solutions.  The simplest is the squarefree support:

\[
 \sum_{a\text{ squarefree}}\frac1{t^a-1}=\frac1t
 \qquad\text{in }\mathbf F_2((1/t)).
\]

The disposable proposal tested here was to lift these solutions through the
real binary carries.  The first deduction is that there is no Hensel freedom
in the support at all.  The exact scan then eliminates every lift having the
declared bounded characteristic-two and real periods.

## 1. Boolean lift rigidity

Let `g : N -> F_2` be eventually periodic.  In characteristic two the unique
Dirichlet inverse construction is

\[
 b=g*\mu\pmod2,
 \qquad
 g(n)=\sum_{d\mid n}b(d)\pmod2.                 \tag{1}
\]

Suppose a real Boolean support `B` reduces to this characteristic-two
solution.  Reduction

\[
 \{0,1\}\longrightarrow\mathbf F_2
\]

is injective.  Therefore every real support bit is already fixed by (1):

\[
 \mathbf 1_B(n)=b(n)\quad\text{as an integer}.  \tag{2}
\]

In particular, a correction divisible by two cannot be added to a Boolean
coefficient.  A lift may change the chosen source `g`, but it cannot repair a
fixed characteristic-two support layer by layer.  This is an all-depth
no-go, not a numerical observation.

## 2. Exact real-output test

For each eventually periodic binary `g` in the declared finite family, the
scanner constructs the unique support (1) through rank `D`.  It verifies at
every rank that the selected-divisor count has parity `g(n)`.

It then encloses the real sum

\[
 S_B=\sum_{b(n)=1}\frac1{2^n-1}
\]

with integers at dyadic precision `P`.  Each retained term is rounded down;
the total rounding loss is smaller than the selected count.  The unrestricted
omitted tail satisfies

\[
 \sum_{n>D}\frac1{2^n-1}<2^{1-D}.               \tag{3}
\]

Thus the common binary prefix of the enclosure is rigorous even if every
omitted exponent is selected.  For that certified prefix the program
challenges every eventually periodic real binary output with preperiod at
most `L` and period at most `T`.  A mismatch at one certified digit rules out
that rational-output class for that support.

## 3. Exhaustive receipt

The durable run used

```text
D = 1024
P = 1280
characteristic-two source preperiod <= 3
characteristic-two source period <= 8
real binary preperiod <= 32
real binary period <= 64
```

It exhausts 7,650 source words.  Of these, 7,418 still have selected support
in the back half of the scanned range.  All 7,650 characteristic-two
identities verify exactly, and no back-half-live support has a real periodic
output surviving the certified prefix.

The best finite fit has characteristic-two source `(preperiod,period)=(3,7)`
and word `0011111000`.  Its real output fails at fractional binary digit 109;
1,020 fractional digits are certified.  This is only twelve repeated digits
beyond the 32 arbitrary preperiod digits and the first 64 digits that define
the candidate period.

The squarefree witness occurs explicitly as source word `10` with
`(preperiod,period)=(1,1)`.  Its reconstructed support agrees with the
squarefree indicator at all 1,024 ranks, with zero mismatches.  Its best
bounded real-period fit fails at fractional binary digit 102.

The machine-readable authority is

```text
state/formal_math/erdos257_period_noncollapse/
  characteristic_two_real_lift_scan_receipt.json
```

with payload hash

```text
89ea50e018aa205e203500e9273564b7e09b2e53191f6a1330a04bb37a84fcef
```

## 4. Mechanism decision

This kills two distinct proposals:

1. a fixed characteristic-two solution cannot be Hensel-corrected while
   retaining Boolean support, by the injectivity argument (2);
2. varying over all characteristic-two sources inside the declared bounded
   preperiod/period family produces no real rational output inside the
   declared bounded real preperiod/period family, by exact exhaustive scan.

The computation is finite.  It does not exclude larger source periods,
larger real periods, or an aperiodic construction whose rationality is proved
by another all-depth identity.  Extending only these bounds would be another
horizon audit, so this lane should reopen only if a new producer supplies a
specific lift law that the present family omits.

## Reproduction

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/characteristic_two_real_lift_scan.py

./repo-python formal_math/erdos257_period_noncollapse/scripts/characteristic_two_real_lift_scan.py \
  --check state/formal_math/erdos257_period_noncollapse/characteristic_two_real_lift_scan_receipt.json
```
