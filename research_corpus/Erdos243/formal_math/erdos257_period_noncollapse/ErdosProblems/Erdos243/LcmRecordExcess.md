# Weighted first crossings of LCM numerator records

Erdős 243 remains open. This note verifies the supplied *Arithmetic first
crossings and LCM record excess* argument and extends its reciprocal weight to
every positive decreasing weight with divergent integral. The extension gives
smaller sufficient summability conditions, including arbitrary fixed iterated
logarithmic discounts. It does not establish any of these conditions from the
parent assumptions.

Evidence: ordinary mathematical proof for the global theorems; the four finite
arithmetic/charging statements are isolated in `LcmRecordExcess.lean`. Exact
bounded computation is in `scripts/check_lcm_record_excess.py`. No global
analytic theorem in this note is asserted to be Lean checked.
The draft `LcmRecordCrossing.lean` connects the progression spacing, unique
first crossings, and the finite record-only sum; its Lean validation is
outstanding. The proofs below are ordinary mathematical arguments.

Attribution: the unweighted first-crossing proof, LCM-record restriction,
growing product-scale baseline, growth-defect identity, and subcritical
record-only log-log theorem are from the user-supplied attachment
`800c8dc4-803e-4914-93f1-b89c46722429/pasted-text.txt` on 2026-09-05.
The general weight, its growth-defect transfer, and the comparison of the
resulting criteria are developed in this continuation. Local verification does
not establish novelty relative to the external literature. The prior bounded
LCM and strict-rise results are already in `R2CumulativePayment.md`; raw-record
and shifted-excess results are in `EightReturnRigidityCriteria.md`.

## 1. Target and coordinates

The target is eventual `a_(n+1)=a_n^2-a_n+1` under positive increasing integer
digits, `a_(n+1)/a_n^2 -> 1`, and rational reciprocal sum `p/q`.
For `x_n=sum_(k>=n) 1/a_k`, set

\[
D_n=q\prod_{k<n}a_k,\quad C_n=D_nx_n,\quad
E_n=D_n-(a_n-1)C_n,
\]
\[
\Lambda_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1}),\quad
M_n=D_n/\Lambda_n,\quad U_n=C_n/M_n,\quad V_n=E_n/M_n.
\]

These are integers, with `C_n,U_n,M_n` positive. The additive rational tail
has denominator dividing `Lambda_n`. With `rho_n=gcd(Lambda_n,a_n)`,

\[
C_{n+1}=C_n-E_n,\quad D_{n+1}=a_nD_n,\quad
M_{n+1}=M_n\rho_n,\quad
\rho_nU_{n+1}=U_n-V_n,\quad V_n=\Lambda_n-(a_n-1)U_n.
\]

Koizumi's nearest-integer reduction supplies, eventually,
`-U_n <= 2V_n < U_n` and `theta_n=V_n/U_n -> 0`.
See [Koizumi, Theorem 1 and Conjecture 6](https://arxiv.org/html/2504.05933v1).
We use the centred selector, never `floor(D/C)+1` without rounding.

Write `R_n=max_(j<=n) U_j` and let `mathcal R={n:U_(n+1)>R_n}`.
Every late strict rise has `rho_n=1`, since `rho_n>=2` would give
`U_(n+1)<=3U_n/4`. Its actual jump is consequently `d_n=-V_n`.
At a record step this jump includes recovery from any drawdown:
`d_n=R_(n+1)-R_n+(R_n-U_n)`. It is not the record increment alone.

For example, the exact centred orbit starting from `C=54,D=385` begins
with LCM numerators `54,47,69`: its second step rises by `22` but sets a
record only `15` above the old one. The successive digits are `8,67`, both
LCM-fresh. This finite prefix illustrates the distinction without asserting
anything about a non-Sylvester infinite orbit.

## 2. A finite weighted crossing inequality

Let `B>=1` be an integer, and suppose pairwise coprime integers
`m_0,...,m_(B-1)>B` divide `Lambda_T`, with `T` past the centring threshold.
Set `P=prod m_i`. Choose `x` by CRT with `m_i | x+i` and consider the walls
`tau=x+B+kP`. Let `f:[1,infinity)->[0,infinity)` be finite and nonincreasing.
For every `N>=T`,

\[
\boxed{\quad
\sum_{\substack{T\le n<N\\n\in\mathcal R}}
(-V_n-B)_+ f(U_n)
\ \ge\sum_{\substack{R_T<\tau\le R_N\\\tau\equiv x+B\pmod P}} f(\tau)
\ \ge\frac1P\int_{R_T+P}^{R_N}f(t)\,dt .\quad} \tag{W}
\]

**Proof.** A first crossing has `U_n<=R_n<tau<=U_n+d_n` and is a record.
If `d_n<=B`, then `tau-B<=U_n<tau`, so one of the covering `m_i` divides
`U_n`. It also divides `Lambda_n`, hence divides
`d_n=(a_n-1)U_n-Lambda_n`. This contradicts `0<d_n<=B<m_i`.

Put `r=d_n-B>=1`. If `h` walls are first crossed by this step, their spacing
gives `(h-1)P<d_n`. Since `P>=B+1`, we have
`d_n=B+r<=Pr`, so `h<=r`. Monotonicity of `f` gives
`sum_(new walls) f(tau)<=h f(U_n)<=r f(U_n)`. Every new wall is charged once;
downward excursions and subsequent recrossings cause no extra charge.

More explicitly, for each selected height `tau>R_T` reached by time `N`,
choose the least `m>T` with `U_m>=tau`. Then `n=m-1` satisfies
`U_j<tau<=U_(n+1)` for every `j<=n`, so `n` is a strict record step.
Two steps cannot both be its first crossing: the successor of the earlier
one would be an earlier state for the later one. Thus the selected heights
partition by crossing time. The endpoint `U_N` may lie below a previously
crossed height; only reachability by time `N`, equivalently the bound by
`R_N`, matters. No monotonicity of the numerator sequence is used.

For the first wall `tau_0>R_T`, `tau_0<=R_T+P`. If any walls are crossed,
their adjacent intervals of length `P` cover `[R_T+P,R_N]` when this interval
is nonempty, and `int_tau^(tau+P) f <= P f(tau)`. This gives (W).
If no wall is crossed, then `R_N<R_T+P` and the integral is nonpositive. ∎

For `f(t)=1/t`, (W) is the supplied finite bound
`(1/P)log(R_N/(R_T+P))`. The general weight is a consequence of the same
crossing mechanism, not a separate arithmetic exclusion.

**Why the baseline is subtracted from the actual jump.** The distinction
can already matter in the local arithmetic. Take `B=3`, covering divisors
`5,7,11`, and `x=20`; then `5|20`, `7|21`, and `11|22` cover the integers
immediately below the wall `tau=23`, with period `P=385`. Put
`L=14245`, `a=751`, and `U=19`. These give
`gcd(L,a)=1` and `d=(a-1)U-L=5`, hence a successor `U'=24` with centred
error `V=-5`. If the prior running maximum is `22`, this step crosses
`23`, while `(U'-22-B)_+=0`. Its actual excess is `d-B=2`, which can
pay for the wall. This is a local arithmetic witness against replacing
the jump in the charging argument; the prescribed prior maximum is not
claimed to arise from an infinite canonical orbit. The exact checker
reproduces both this witness and the finite prefix above, and separately
tests the first-crossing partition on nonmonotone words.

## 3. Discharging the arithmetic supply; exact weighted criteria

The supply follows directly from unbounded numerator height. If `U_n` is
unbounded, there are infinitely many record steps. Each is fresh, and its
digit exceeds one: the positive jump satisfies
`d_n=(a_n-1)U_n-Lambda_n>0`. For two record steps `r<s`, the earlier digit
`a_r` divides `Lambda_s`, whereas `gcd(a_s,Lambda_s)=1`. Thus the record
digits are pairwise coprime. Since they exceed one, they are distinct; only
finitely many can be at most any fixed `B`. Choose `B` record digits greater
than `B`, and take `T` after their indices. They all divide `Lambda_T` and
provide exactly the supply required in (W). No estimate for the density of
fresh indices, or for the growth of `C_n`, is needed.

**Arithmetic weighted-record dichotomy.** More generally, suppose positive
integer sequences `a_n,Lambda_n,U_n` and an integer sequence `V_n` satisfy

\[
\Lambda_{n+1}=\operatorname{lcm}(\Lambda_n,a_n),\qquad
\rho_n=\gcd(\Lambda_n,a_n),\qquad
\rho_n U_{n+1}=U_n-V_n,\qquad
V_n=\Lambda_n-(a_n-1)U_n,\qquad -U_n\le 2V_n.
\]

For any finite nonnegative nonincreasing `f` on `[1,infinity)` with divergent
integral, and any fixed integer `B>=0`,

\[
\sup_n U_n<\infty
\quad\Longleftrightarrow\quad
\sum_{n\in\mathcal R}(-V_n-B)_+ f(U_n)<\infty. \tag{A}
\]

**Proof.** If `U_n` is bounded, its positive integer running maximum can
increase only finitely many times. The series therefore has finitely many
nonzero terms. If `U_n` is unbounded, the lower centring bound alone makes
every rise fresh: `rho_n>=2` would imply `U_(n+1)<=3U_n/4`. The preceding
record-digit argument supplies the CRT block for any `B>=1`. Apply (W) after
that block enters the cumulative LCM and let `R_N` tend to infinity. Its
integral lower bound diverges. The case `B=0` follows by comparison with
`B=1`. All finitely many terms before the chosen `T` are harmless. ∎

This is a theorem about the arithmetic recurrence. It needs neither a
reciprocal-sum representation nor `V_n/U_n -> 0`, and not even the upper
centring bound. Those hypotheses enter when bounded height is converted to
the original problem's eventual recurrence. Assertion (A) is an ordinary
proof here, not a new kernel-checked statement.

Centred zero is absorbing. If `E_n=0`, then
`D_n=(a_n-1)C_n` and `C_(n+1)=C_n`; centring at the next index forces
`a_(n+1)=a_n(a_n-1)+1` and `E_(n+1)=0`.
If the endpoint fails, `V_n` is eventually a nonzero integer, so
`1/U_n<=|theta_n| -> 0`. Thus `U_n -> infinity` and `R_n -> infinity`.

**Weighted record theorem.** Fix any nonnegative, finite, nonincreasing `f`
with `int_1^infinity f(t)dt=infinity`. Under the parent assumptions,

\[
\boxed{\quad
\text{eventual Sylvester recurrence}
\quad\Longleftrightarrow\quad
\exists B\in\mathbb Z_{\ge0}:\ 
\sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty .\quad} \tag{E}
\]

Indeed, on a non-Sylvester orbit (W) diverges for every fixed `B>=1`, and
`B=0` follows by domination. Conversely, an eventual Sylvester tail
telescopes to `x_n=1/(a_n-1)`, so `V_n=0` eventually.

This includes `f(t)=1/[t log(et)]`, giving a smaller series than the supplied
one and a finite lower bound

\[
\frac1P\log\frac{\log(eR_N)}{\log(e(R_T+P))}.
\]

More generally put `L_1(t)=log(et)` and `L_(j+1)(t)=log(eL_j(t))`. For any
fixed `k>=1`, `f_k(t)=1/[t L_1(t)...L_k(t)]` is positive decreasing, and its
integral diverges because it is the derivative of `log L_k(t)`.
Thus finiteness of any one of these more heavily discounted record sums
already forces the endpoint. In the ambient class of arbitrary sequences of
nonnegative terms these finiteness conditions are successively weaker; on
canonical orbits (E) proves that they are all equivalent to the same endpoint.
There is no claim of a weakest possible divergent weight or of new parent
progress from counting equivalent reformulations.

## 4. The original growth defect

Put `gamma_n=a_n^2/a_(n+1)-1`. Exact algebra gives

\[
\gamma_n+\theta_n=
\frac{(1-\theta_n)(a_n-1+\theta_{n+1})}{a_{n+1}}.
\]

Eventually `0<gamma_n+theta_n<3/a_n`. Positive-part Lipschitz continuity
therefore gives

\[
0\le U_nf(U_n)(\gamma_n-B/U_n)_+
-(-V_n-B)_+f(U_n)\le3U_nf(U_n)/a_n. \tag{G}
\]

The upper bound is summable for every weight allowed above: `f(U_n)<=f(1)`,
`U_n<=C_n=exp(o(n))`, and `a_n>=exp(c2^n)` eventually. These last bounds
follow by iterating the tail update and `a_(n+1)>=a_n^2/2` after `a_n>2`.
Consequently (E) is also equivalent to

\[
\exists B\ge0:\quad
\sum_{n\in\mathcal R}U_nf(U_n)
\left(\frac{a_n^2}{a_{n+1}}-1-\frac{B}{U_n}\right)_+<\infty. \tag{G-E}
\]

For the logarithmically discounted example the factor `U_nf(U_n)` is simply
`1/log(eU_n)`. Original growth convergence alone still supplies no proof of
this summability. The universal quantifier over genuine canonical orbits in
any fixed instance of (G-E) is an exactly equivalent parent producer.

## 5. Record-only subcritical log-log bound

The supplied argument also proves: if, for some `delta in (0,1)`, every late
LCM record step satisfies
`d_n <= (1-delta) log_2 log_2 max(4,U_n)`, then the endpoint holds.

For clarity the scale argument is retained. Choose small `eta>0` with
`(1-delta)(1+2eta)<1`. For large integer `B`, let `T=ceil((1+eta)B)`.
Only `o(B)` preceding digits are nonfresh, and only `O(log log B)` are at
most `B`, since `log a_n` lies between positive constants times `2^n`.
Choose `B` preceding fresh digits above `B`. Their product satisfies
`B^B<P<=D_T`, `R_T<P`, and
`log_2 log_2(2P+B)<=(1+2eta)B` for large `B`.
Take the CRT representative `P<=x<2P` and the first crossing of `x+B`.
Its source is below `2P+B` and its jump is less than `B`, contradicting the
covered-wall lemma. This restricts only records, unlike the older R2 theorem
which restricts every strict rise. The inclusive raw-record constant from
`EightReturnRigidityCriteria.md` is not transported to `U` here.

## 6. Discriminating checks and the remaining obstruction

Three structurally different routes were compared in this continuation:

| Route | Supporting asset | Contrary evidence and cheapest probe | Disposition |
| --- | --- | --- | --- |
| LCM first crossings | Permanent old divisors and exact centred feedback | Weighted wall-count and charge inequalities on direct rational orbits | Survives; proves (W), (E), and (G-E), but no automatic upper bound |
| Scalar growth/integer envelopes | Critical-boundary rounding and subexponential `C_n` | Test `U_n=C_n=n^2+1`, `V_n=E_n=-(2n+1)` against discounted sums | Cannot supply finiteness from these scalar facts; genuine denominator feedback is still essential |
| Primitive protected prime powers | `primitive_valuation_no_drop` and two-unit record barrier | Exact `(u,v)=(10,187)`, `a=20`, `e=-3`, `u'=13`, protected prime `11` | A single protected prime cannot exclude a rise of three; do not rerun this as a parent route without a multi-prime mechanism |

For the scalar model `theta_n -> 0`, centring eventually holds and every step
is a record, yet the `f_1` summand is asymptotic to `1/(n log n)`, hence
diverges for every fixed `B`. It is not a rational-tail counterexample: its
numerators modulo five at indices `2,3,4` are `0,0,2`, impossible under the
exact numerator/denominator update, where two consecutive zero numerators
force all subsequent numerators to remain zero modulo five.

Nor can each positive record charge be paid by local overlap. For `m>=1`,
`c>2m`, `gcd(c,m)=1`, take
`D=c(c+m)-m`, `C=c`, `a=c+m+1`. Then `E=-m`, `gcd(C,D)=gcd(a,D)=1`,
and `U'=c+m`: a positive record charge with no overlap increase. This is a
finite exact fixture, not an infinite counterexample. The corpus already
contains arbitrarily long clean fixtures.

The checker independently covers 6,008 seed–modulus cases (6,000 distinct
rational seeds), 26,171 nonterminal transitions and 6,008 terminal states:
32,179 inspected states. Thus the attachment's figure 32,179 is reproduced
as states, not nonterminal transitions. All cases reach centred zero within
15 steps and the 20,000-bit cap. It checks 1,002 first-crossed walls on 814
charged steps, both rational weights `1/t` and
`1/[t ceil(log_2 max(2,t))]`, the exact growth-defect identity, and the two
local falsifiers above. Finite data do not prove universal termination.

A separate reconstruction tests the composition used by
`finite_record_bound_of_old_coprime_moduli`: it constructs the CRT phase in
`[P,2P)`, assigns each selected height directly to the earliest state reaching
it, and checks the old-divisor covering and exact feedback at that state.
It then compares the total wall mass with the record-excess sum, independently
of the local charge totals. The same 6,008 cases give 12,016 exact rational
weighted comparisons and 997 selected heights. The five additional heights
in the local check lie below the translated CRT progression's starting point.
This is finite evidence for the composition; the Lean draft still requires
kernel validation and the infinite analytic argument remains separate.

The remaining mathematical obligation is to derive finiteness in (G-E) for
one admissible weight and one fixed `B` from genuine rational denominator
feedback, or to find another contradiction to a nonterminal orbit. The
extra logarithmic discount weakens what suffices; it does not establish it.
The global parent remains open.
