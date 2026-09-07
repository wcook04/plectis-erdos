# Pure binary periods and a post-period fatal falsifier

## Status

The complete numerator lattices through period 20 suggested that every fatal
pure-period target dies no later than its source period.  Exact
meet-in-the-middle searches refute both natural versions of that statement.
A period-26 target first dies at rank 26, killing the strict `<P` bound.  More
decisively, a period-29 target survives its complete source period and first
dies at rank 30.  Thus one-period survival is not an all-depth certificate.
Both witnesses are fatal, so neither decides Erdős 257.

The executable source is
[`pure_period_fatal_horizon.py`](../../scripts/pure_period_fatal_horizon.py),
and the canonical receipt is

    state/formal_math/erdos257_period_noncollapse/pure_period_fatal_horizon_receipt.json.

The exact falsifier is independently replayed by
[`pure_period_fatal_horizon_counterexample.py`](../../scripts/pure_period_fatal_horizon_counterexample.py),
with receipt

    state/formal_math/erdos257_period_noncollapse/pure_period_fatal_horizon_counterexample_receipt.json.

## 1. The exact target family

Write

\[
 w_n=\frac1{2^n-1},\qquad
 T_n=\sum_{k>n}w_k.
\]

For every period `P>=2`, the script exhausts every nonzero target below one
with a `P`-periodic binary presentation,

\[
 x_{P,m}=\frac{m}{2^P-1},
 \qquad 1\le m<2^P-1.                         \tag{1}
\]

The ordinary Mersenne greedy algorithm maintains a residual `r_n` after rank
`n`.  Once `r_n>T_n`, even selecting every later exponent cannot fill the
residual; this is a fatal rank.  Strict superincreasingness then makes the
greedy support the unique possible support.

Every comparison in the census is directed.  If `S=2^2048`, the target,
residual, each weight, and the complete infinite tail are carried as integer
lower and upper bounds after scaling by `S`.  A fatality is recorded only when
the residual lower bound exceeds a rigorous upper bound for the infinite
tail.  A safe rank is accepted only when the residual upper bound is at most a
rigorous tail lower bound.  The remaining exact-weight ties are replayed with
`Fraction` and verified to terminate in the stored finite support.  There are
no unresolved tail comparisons.

## 2. The exact finite result

For every `P=2,...,20`, all `2^P-2` numerators in (1) were followed through
rank `8P`.  This is 2,097,110 targets, not a random sample.  The global
partition is

| class | count |
|---|---:|
| certified fatal | 1,048,555 |
| exact finite boundary | 157 |
| certified safe through `8P` | 1,048,398 |
| unresolved tail comparisons | 0 |

No fatality occurs at or after the target's own period.  More sharply, for
every one of the nineteen periods, the largest certified fatal rank is
exactly

\[
 P-1.                                                \tag{2}
\]

The counts at each individual period are exact formulas.  If `tau(P)` is the
number of divisors of `P`, then

\[
\begin{aligned}
 \#\text{fatal} &= 2^{P-1}-1,\\
 \#\text{finite boundary} &=2^{\tau(P)-1}-1,\\
 \#\text{safe through }8P
   &=2^{P-1}-2^{\tau(P)-1}.                         \tag{3}
\end{aligned}
\]

The middle formula has a transparent arithmetic source.  If `d|P`, then
`2^d-1` divides `2^P-1`, so every subset of the weights with exponents
`d|P`, `d>1`, lies on the period-`P` numerator lattice.  These are exactly the
finite-boundary rows found by the independent rational replay.  What is not
explained by this observation is why all remaining numerator-lattice
fatalities occur before `P`, or why the other half stays safe for the next
seven periods.

Examples at the smallest nontrivial periods are already sharp.  At `P=3`,
the targets `3/7` and `4/7` are safe through rank 24; `1/7=w_3` is the sole
finite boundary; the other three numerators die by rank two.  At `P=6`, 31
targets die by rank five, seven are finite boundaries, and 24 survive through
rank 48.  The survivor list includes

\[
 \frac3{63}=\frac1{21}.                            \tag{4}
\]

## 3. Both one-period horizon bounds are false

The period-20 census selected the following target-independent statement.

> **Pure-period fatal-horizon conjecture.**  If a rational target has a pure
> binary period `P` and its Mersenne greedy orbit ever enters a fatal gap, its
> first fatal rank is strictly less than `P`.

It is refuted at `P=26`.  Put

\[
 D=2^{26}-1=67108863,\qquad m=16559772,
\]

and

\[
 x=\frac mD=\frac{5519924}{22369621}.
\]

The reduced denominator has multiplicative order 26 for 2, so this is a
genuine pure-period-26 target.  Its repeated 26-bit word is

    00111111001010111010011100.

Exact rational replay gives the greedy prefix

\[
 F=\{3,4,5,8,10,14,16,19,21,23,24\}.
\]

Rank 26 is skipped, and the terminal residual `r` satisfies

\[
 2^{-26}<r<\frac1{2^{26}-1},\qquad
 r>2^{-26}+\frac{4^{-26}}{3(1-2^{-27})}>T_{26}.  \tag{7}
\]

The last strict inequality uses

\[
 \frac1{2^k-1}-2^{-k}
 =\frac{4^{-k}}{1-2^{-k}}
 <\frac{4^{-k}}{1-2^{-27}}
\]

and sums it over `k>26`.  Thus rank 26 is not merely dyadically unsafe: it is
the actual first fatal rank.  The script checks the greedy word and all three
cleared positive gaps with integer arithmetic.

The period-26 example fails at the terminal rank of its first period.  By
itself it left open the corrected producer:

> **Corrected pure-period horizon conjecture.** If a pure-period-`P` target
> ever enters a fatal gap, its first fatal rank is at most `P`.

That corrected statement is also false.  Put

\[
 P=29,\qquad D=2^{29}-1=536870911,
 \qquad m=182693966,
\]

and

\[
 x=\frac{182693966}{536870911}.
\]

The fraction is reduced and 2 has multiplicative order 29 modulo its
denominator.  Its pure 29-bit source word is

    01010111000111011000001001110.

Exact greedy replay through rank 30 selects

\[
 F=\{2,8,9,10,14,15,17,18,20,21,23,24,25,26,27\}
\]

and skips rank 30.  If `r` is the residual there, then

\[
 2^{-30}<r<\frac1{2^{30}-1},\qquad
 r>2^{-30}+\frac{4^{-30}}{3(1-2^{-31})}>T_{30}.  \tag{8}
\]

The residual before every earlier rank is bounded by the corresponding finite
tail through rank 30, so no earlier fatality is possible.  Consequently this
target survives ranks `1,...,29` and has actual first fatal rank

\[
 30=P+1.                                             \tag{9}
\]

This is the decisive falsifier: passing the complete source period does not
imply all-depth survival.

## 4. How the falsifier was located

At a putative skipped rank `n`, let `S_F` be the selected finite prefix.  A
dyadically unsafe residual asks for an integer `m` in

\[
 D_P\bigl(S_F+2^{-n},\ S_F+w_n\bigr).             \tag{5}
\]

When `P=n`, write `D_n=2^n-1`.  Since `D_n w_n=1`, the interval contains an
integer exactly when the fractional part

\[
 \left\{D_nS_F\right\}
 =\left\{\sum_{d\in F}
   \frac{2^{n\bmod d}-1}{2^d-1}\right\}           \tag{6}
\]

lies strictly between zero and `2^-n`.  This is the finite-prefix version of
the repository's `Lambda` residue coordinate.  Meet-in-the-middle subset-sum
search found

\[
 F=\{3,4,5,8,10,14,16,19,21,23,24\},
\]

for which the value in (6), after multiplication by `2^26`, is approximately
`0.3958034337696`.  Choosing `m=floor(D_26 S_F)+1` leaves the residual about
`0.6041965752336 * 4^-26` above the dyadic seam.  The Mersenne tail is less
than `4^-26/[3(1-2^-27)]` above that seam, so the residual is fatal.

This explains why the sharper maximum `P-1` pattern through period 20 did not
persist.  For the decisive search, the same meet-in-the-middle calculation was
run with `P=29` and `n=30`, targeting the much thinner translated interval

\[
 D_{29}\bigl(S_F+T_{30},\ S_F+w_{30}\bigr).
\]

It returns the period-29 prefix above.  Exact replay places its terminal
residual about `0.7064849036732 * 4^-30` above the dyadic seam, while the
complete correction tail is below `4^-30/[3(1-2^-31)]`.  This is why the
candidate is certified fatal rather than merely inside the larger dyadic
sliver.

## 5. Claim boundary

The 2,097,110-target census through period 20 remains an exact finite result,
including its partition counts.  The period-26 target eliminates the strict
`first_fatal<P` extrapolation, and the period-29 target eliminates the corrected
`first_fatal<=P` producer.  Both are actual greedy states with rigorously
bounded infinite tails.  Both are also fatal, so this is a decisive mechanism
elimination rather than a rational infinite Mersenne support.  Any replacement
finite-horizon theorem needs genuinely more state than the source period alone;
checking one periodic block cannot certify immortality.
