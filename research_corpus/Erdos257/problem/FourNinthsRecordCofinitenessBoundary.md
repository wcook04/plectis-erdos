# Causal cofinal repair candidates for `4/9`

Status: exact analytic reduction plus certified finite theorem selection.  The
all-depth inequality isolated below is open.  Nothing in this note claims that
finite computation proves membership or settles Erdős 257.

## 1. Why a cofinal non-record class is enough

Let `b_n` be the exact rational-greedy support for `4/9`, let

\[
 f(n)=\sum_{d\mid n}b_d,
 \qquad Q_n=2Q_{n-1}+t_n-f(n),
\]

and let `t_n` be the period-six binary word `011100` of `4/9`.

The general final-gap argument is target-independent.  If the greedy has a
last skip, its positive residual gap gives `Q_N/2^N -> delta>0`.  Since
`f(N)<=N`, every sufficiently late rank is then a strict `Q`-record.  Hence
any cofinal class on which

\[
 Q_n\le Q_{n-1}
\]

holds excludes the fatal branch.  The recurrence gives the exact repair form

\[
 Q_n\le Q_{n-1}
 \quad\Longleftrightarrow\quad
 f(n)\ge Q_{n-1}+t_n.                           \tag{R}
\]

If the greedy survives, its support sums to `4/9`.  Lean now proves directly
that no finite Boolean support on ranks at least two can have this value:
the reduced-denominator order theorem makes its rank lcm divide six, leaving
only ranks `2`, `3`, and `6`, and exact arithmetic excludes all eight subsets.
The support is therefore infinite and is a counterexample to Erdős 257.

## 2. The seven-column law

For `30|n`, define

\[
\begin{aligned}
 U_{30}(n)={}&f(n/2)+f(n/3)+f(n/5)\\
             &-f(n/6)-f(n/10)-f(n/15)+f(n/30).
\end{aligned}
\]

By inclusion-exclusion, `U_30(n)` counts exactly those selected ranks `d` for
which the codivisor `n/d` is divisible by at least one of `2,3,5`.  Every such
`d` is a proper divisor of `n`, so `U_30(n)<=f(n)` without using the current
bit `b_n`.

The certified `4/9` word supports the following candidate:

\[
 \boxed{U_{30}(120k)\ge Q_{120k-1}.}            \tag{F120}
\]

Because `t_(120k)=0`, `(F120)` implies `(R)` at every multiple of `120`.
An all-depth proof would therefore give a cofinal non-record class, prove that
`4/9` belongs to the Mersenne achievement set, force the representing support
to be infinite, and disprove Erdős 257.

This is more causal than the full load inequality: all seven columns lie at
rank at most `n/2`, and the current bit is absent.

## 3. The target phase cancels exactly

At `n=120k`, direct inspection of the word `011100` gives `t_n=0`, and the
full inclusion-exclusion pulse vanishes:

\[
t_{n/2}+t_{n/3}+t_{n/5}
-t_{n/6}-t_{n/10}-t_{n/15}+t_{n/30}=0.          \tag{P}
\]

Substituting `f(m)=2Q_{m-1}+t_m-Q_m` into `U_30(n)` therefore removes the
target digits completely.  If

\[
\begin{aligned}
J^-(n)={}&Q_{n/2-1}+Q_{n/3-1}+Q_{n/5-1}\\
          &-Q_{n/6-1}-Q_{n/10-1}-Q_{n/15-1}+Q_{n/30-1},\\
J(n)={}&Q_{n/2}+Q_{n/3}+Q_{n/5}\\
       &-Q_{n/6}-Q_{n/10}-Q_{n/15}+Q_{n/30},
\end{aligned}
\]

then `(F120)` is exactly

\[
 \boxed{2J^-(n)-J(n)\ge Q_{n-1}.}               \tag{PF120}
\]

Thus the missing theorem is a phase-free comparison between the defect at the
end of a doubled block and a three-prime inclusion-exclusion projection of
seven earlier scales.  It is not a statistical density claim.

## 4. Why computation changed the conjecture twice

At depth `10,000`, a two-prime version appeared to hold on multiples of `24`.
A certified run to `50,000` falsified it at

```text
19464, 38904, 41352, 43944, 46344, 49992.
```

The first row has three-column load `5` and predecessor defect `6`.  The same
run then suggested a modulus-48 two-prime law.  The exact one-million-rank
cylinder kills that version too: nine violations, first at `214224`.  This
depth-sensitivity correction is recorded in Task Ledger capture
`cap_quick_erdos257_four_ninths_short_prefix_modulu_4ef3f4333edb`.

The one-million-rank rescan next selected the seven-column modulus-60 law, but
the exact two-million-rank cylinder kills it once, at

```text
1912380 = 60 * 31873,  margin = -1.
```

The quotient `31873` is odd.  Restricting to the additional 2-adic layer gives
`(F120)`.  The certified cylinder through rank ten million has `83,333`
tested rows, zero violations, zero equalities, and minimum margin one.  The two
tightest rows are `3175080` and `8754360`.  Thus the larger computation did not
turn the observed law into a roomy estimate: it exposed genuine near-equality.
The modulus-60 correction is recorded in Task Ledger capture
`cap_quick_erdos257_four_ninths_modulus_60_law_firs_8179d651a34a`.

The stronger law is now tight.  The exact replay through rank twenty million
still had no violation, but first reached equality at `14369640` and
`19161960`.  The rank-fifty-million replay tested `416,666` modulus-120 rows:
there were again zero violations, but fourteen equalities.  Thus `(F120)`
remains a legitimate all-depth candidate, while its zero slack makes the
prime-cofactor columns the natural falsification boundary.  It should not be
treated as more secure than the analogous `1/21` law, whose first deep failure
also occurred on a prime-cofactor column.  In fact all fourteen equality rows
have the exact form `120*p` with `p` prime.  This concentration is recorded in
Task Ledger capture
`cap_quick_all_fourteen_tight_four_ninths_modulus_1_52597bd2f448`.

Those equalities are not tight for the actual repair endpoint.  If
`n=120p` with prime `p>5`, the only divisors omitted by `U_30(n)` have
codivisor `1` or `p`, hence are `n` and `120`.  The exact forced word has
`b_120=1`, so

\[
 f(120p)=U_{30}(120p)+b_{120p}+1.
\]

Consequently even `U_30(120p)>=Q_(120p-1)-1` implies the required full repair.
The fourteen observed `(F120)` equalities retain at least one unit of true
endpoint slack.  This correction is recorded in
`cap_quick_prime_cofactor_four_ninths_equality_rows_8f12c7df98e3`; future
prime-column work should target the endpoint-aligned minus-one inequality,
not mistake failure of the stronger display for failure of repair itself.

The same fifty-million replay also measured the strictly weaker producer that
does not prescribe a congruence class.  It found `21,316,576` global one-step
repairs (density `0.42633152`), with last repair at the terminal rank and
maximum observed gap twelve (starting at `22763988`).  The defect had maximum
`168`, sixty-one strict records, and last strict record `49008959`.  These are
finite observations, not a proof of repair cofinality.  Their durable capture
is `cap_quick_four_ninths_one_step_repairs_remain_dens_28d047d1b33b`.

The extended census then stress-tested the tempting smaller periodic classes
against the *actual* repair inequality rather than the stronger seven-column
lower bound.  The modulus-12 law already fails at rank `20676`, with margin
`-1`, and reaches minimum margin `-12` by fifty million.  Every other tested
proper-divisor modulus of `120` also fails; modulus `120` alone has zero
actual-repair violations in `416,666` rows and minimum actual margin `+1`.
Thus the factor from `12` to `120` is substantive, not an artifact of the
causal lower bound.  The exact global gap histogram has eight gaps of length
`12` and eight of length `11`; there are no larger gaps in the audit.  This
falsification is captured as
`cap_quick_four_ninths_modulus_12_repair_law_fails_9dce6b99d7df`.

This is the role of the computation: kill three successively attractive false
theorems and expose the substantive extra factor two.  The resulting modulus
`120` is not isolated to `4/9`: the independent `1/21` record-boundary lab
selects the same `U_30(120k)` law.  In both period-six targets the
inclusion-exclusion target pulse equals `t_(120k)`, so both reduce to the same
phase-free formula `(PF120)`.  This cross-target agreement is evidence for one
shared lemma, not a proof of it.

The companion lab obtains the word from the exact globally reachable
even-cylinder recurrence.  It independently cross-checks a bounded prefix
against the directed fixed-point real greedy, reconstructs `f` and `Q` by
integer arithmetic, and reports the surviving and falsified laws:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  four_ninths_record_boundary_lab.py --ranks 10000000
```

Increasing the rank cap is not a proof.

## 5. Connection to the existing `4/9` frontier

The bits in this lab are the same word as the executable diagonal state in
`FourNinthsDiagonalNoPositiveFatal.lean`; both begin
`010110110001`.  The established diagonal route reduces failure to a globally
reachable selected small-margin event.  `(PF120)` is an orthogonal sufficient
producer: it would rule out the terminal record suffix directly.

The coordinate mismatch at the start of that attack is now removed.  The
kernel-checked theorem
`fourNinthsDiagonalState_rho_eq_target_sub_prefixQuotient` identifies the
executable diagonal remainder exactly with

\[
 \rho_d=\left\lfloor\frac{4^{d+1}}9\right\rfloor
 -\sum_{a\le d}b_a\left\lfloor\frac{4^d}{2^a-1}\right\rfloor .
\]

Thus `rho_d` is the signed Mersenne quotient defect at the even endpoint
`2d`; nonnegativity is exactly quotient admissibility.  This does not prove
`(PF120)`: the remaining bridge must still express the seven values in
`J^-(120k)` and `J(120k)` through these even quotient coordinates and use
cylinder nesting to prove the required endpoint comparison.  The next proof
attack should work in that shared coordinate rather than invent another
state.

There is now also a kernel-checked consumer at the weakest falsification-safe
level.  `FourNinthsCofinalRepairConsumer.lean` defines the scalar defect

\[
 Q_N=\left\lfloor\frac{4\,2^N}{9}\right\rfloor-P_N
\]

for the actual rational greedy orbit and proves
`four_ninths_mem_mersenneAchievementSet_of_repairCofinal`: if one-step
repairs `Q_(N+1)<=Q_N` occur beyond every cutoff, then `4/9` belongs to the
Mersenne achievement set.  The proof uses the exact floor-bit recurrence,
the universal divisor-pair load bound, and the generic fatal-tail
conservation law.  Consequently `(F120)` is only one possible producer for
the checked endpoint; a direct proof of global repair cofinality would be
strictly weaker and is better aligned with the finite orbit.

The same module closes the finite-support side condition rather than leaving
it as a computational classification.  Its theorem
`finiteErdosSum_ne_four_div_nine` proves that no finite support on ranks at
least two sums to `4/9`.  Therefore
`exists_infinite_four_ninths_counterexample_of_repairCofinal` upgrades the
membership consumer to an infinite support of exact rational value, and
`not_universal_of_fourNinths_repairCofinal` packages the resulting conditional
negation of the universal irrationality assertion.  The word *conditional*
is essential: cofinal repairs remain the missing producer.

For the surviving periodic candidate, `FourNinthsMultiple120RepairSupply`
states the actual repair inequality at every positive multiple of `120`.
Lean proves that this supply is cofinal and packages both its membership and
full-counterexample consequences in
`four_ninths_mem_of_multiple120RepairSupply` and
`not_universal_of_fourNinths_multiple120RepairSupply`.  Thus the finite audit
and the open all-depth theorem now meet at an exact checked interface.

`FourNinthsPrimorialRepair.lean` closes the remaining *consumer* wiring for
the causal form `(F120)`.  It defines the subtraction-free union of selected
divisors already visible at `n/2`, `n/3`, or `n/5`, proves the exact
seven-column identity and its inclusion in the full load, and proves the
periodic target bit is zero immediately before every positive multiple of
`120`.  Its endpoint
`not_universal_of_fourNinths_primorialRepair` states precisely that the
all-depth seven-column inequality would refute universal irrationality.  The
inequality remains open; the new module removes no arithmetic hypothesis.

The prime-cofactor boundary is also now exact.  For prime `p>5`,
`fourNinthsPrimorialUnionLoad_primeColumn` splits the entire causal load at
`120p` into the fixed base load at `120` plus one finite support-pullback
column on the divisors of `60`, `40`, and `24`.  Hence
`fourNinthsPrimePrimorialRepair_iff_column` turns every prime row into one
defect-versus-finite-column inequality.  This matches the fifty-million
observation that every tight `(F120)` row has prime cofactor and identifies
the exact boundary a future proof or falsifier must attack.

The fixed column is not a trusted script constant: Lean evaluates the exact
rational greedy prefix and proves
`fourNinthsPrimorialUnionLoad_120 : U_30(120)=10`.  Consequently
`fourNinthsPrimePrimorialRepair_iff_defect_le_column_add_ten` gives the final
prime normal form

\[
 Q_{120p-1}\le \operatorname{PullbackColumn}(p)+10.
\]

The corresponding exact-computation finding is captured as
`cap_quick_four_ninths_prime_boundary_has_fixed_bas_6ce73ad0e33e`.

The moving column has now been flattened one step further.  The divisors of
`60`, `40`, and `24` have union exactly

\[
 \operatorname{Div}(120)\setminus\{120\}
 =\{1,2,3,4,5,6,8,10,12,15,20,24,30,40,60\}.
\]

Lean proves
`fourNinthsPrimePullbackColumnLoad_eq_properDivisors`, so the prime boundary
is literally a fifteen-bit ancestry inequality.  It also proves that this
column is at most fifteen; consequently any repaired prime row has
`Q_(120p-1)<=25`, giving a cheap exact falsifier for future searches.

The exact fifty-million-rank replay contains `35,128` primes `p>5`, zero
violations, and fourteen equalities.  Their fourteen selected-divisor words
are all different, have loads from one through six, have no common selected
position, and occur in both residues `p=1,5 mod 6`.  Thus a common-bit or
prime-phase argument cannot prove the boundary.  The durable finding is
`cap_quick_four_ninths_prime_repair_boundary_is_a_l_bc40945396c8`; the next
discriminator tests coupled margin descent along cofactor factorization.

The deterministic version of that descent is false.  Put
`M(k)=U_30(120k)-Q_(120k-1)` and delete the largest prime factor of each
composite `k`.  Through cofactor `416,666`, the comparison

\[
 M(k)\ge M(k/\operatorname{lpf}(k))
\]

has `266` violations among `381,534` composite edges and minimum difference
`-5`.  Therefore the conditional largest-prime-factor route from the
`1/21` audit must not be copied here.  This no-go is captured as
`cap_quick_four_ninths_largest_prime_factor_margin_a39b7bb55105`.  Only the
weaker existential question—some proper-divisor ancestor for each
composite—survives this computation.

The weaker question also fails at the same deep horizon.  Among the
`381,534` composite cofactors there are eight rows whose margin is smaller
than the margin at every proper-divisor ancestor; the first is `k=18087`,
and the minimum difference is `-3` at `k=231573` and `k=316658`.  The
composite margins themselves remain positive—minimum one, twice—so this is a
no-go for factor-lattice descent, not a counterexample to `(F120)`.  The
capture is
`cap_quick_four_ninths_existential_proper_divisor_m_cd9cec1257d0`.

The new local-window census also resolves the eight maximum repair gaps.
Every gap of length twelve begins with post-repair defect one, two, or three;
eleven strict rises take the predecessor defect to between `51` and `102`;
then a selected-divisor load between `99` and `202` resets it.  The rescue
ranks lie in the same target phase modulo twelve but occupy residues `0`,
`60`, and `72` modulo `120`.  Crucially, all eight are divisible by `84`.
At each endpoint the union of the selected `/2`, `/3`, and `/7` parent
columns already clears the predecessor defect by between `44` and `97`, while
omitting only two through twelve selected divisors from the full load.  The
intersection of the eight full selected-divisor sets is exactly
`{2,4,7,12,21,28}`, the six selected positions in the modulus-`84` base
union.  This identifies the `2·3·7` causal mechanism behind those particular
rescues and supplies a sharply falsifiable periodic candidate.  The receipts are
`cap_quick_four_ninths_maximum_repair_gaps_are_twel_e0b7b062026b` and
`cap_quick_four_ninths_gap_12_rescues_are_modulus_8_28ec1ef81264`.

For `42|n`, define the `2·3·7` union

\[
\begin{aligned}
 U_{42}(n)={}&f(n/2)+f(n/3)+f(n/7)\\
              &-f(n/6)-f(n/14)-f(n/21)+f(n/42).
\end{aligned}
\]

It counts selected divisors visible in at least one of the three parent
columns and is therefore at most `f(n)`.  Since `t_(84k)=0`, the exact causal
candidate

\[
 \boxed{U_{42}(84k)\ge Q_{84k-1}}              \tag{F84}
\]

would imply an actual repair at every positive multiple of `84`.  A certified
prefix through rank one million tested `11,904` rows, found zero violations,
three equalities, and minimum margin zero.  The deeper replay then falsified
both claims.  The first causal and actual violation is

```text
2008356 = 84 * 23909,  margin = -1,
```

with prime cofactor `23909`.  Through rank fifty million, `(F84)` has `375`
violations among `595,238` rows, `888` equalities, and minimum margin `-6`.
The actual modulus-`84` repair law also reaches minimum margin `-6`.
Therefore modulus `84` explains the observed maximum-gap rescues but is not a
cofinal periodic producer.  The prefix selection and deep falsification are
captured respectively as
`cap_quick_four_ninths_modulus_84_causal_seven_colu_f153e7ed9a34` and
`cap_quick_four_ninths_modulus_84_repair_producer_f_f312c4f2526c`.

The target phase cancels here too.  At `n=84k`,

\[
t_{n/2}+t_{n/3}+t_{n/7}
-t_{n/6}-t_{n/14}-t_{n/21}+t_{n/42}=0.
\]

Therefore, if `K^-(n)` and `K(n)` denote the same signed seven-term
combination of `Q_(m-1)` and `Q_m` at scales
`m=n/2,n/3,n/7,n/6,n/14,n/21,n/42`, then `(F84)` is exactly

\[
 2K^-(n)-K(n)\ge Q_{n-1}.                       \tag{PF84}
\]

The modulus-`84` route is consequently a phase-free defect comparison, not a
claim driven by a favorable target digit; the exact replay shows that even
this source cancellation does not supply the needed inequality.

The same Lean module now exposes `(F84)` without weakening it.  It proves the
subtraction-free seven-column identity, inclusion in the full divisor load,
the exact base value `U_42(84)=6`, the zero floor bit before every positive
multiple of `84`, and the conditional endpoint
`not_universal_of_fourNinths_heptadicRepair`.  On a prime row `84p`, `p>7`,
the causal union splits into its six-position fixed base plus a pullback
column on the eleven proper divisors of `84`.  Lean identifies that column
literally and bounds it by eleven, so every repaired prime row must satisfy
`Q_(84p-1)<=17`.  These are exact reductions and finite-column boundaries;
they expose and classify `(F84)` but cannot rescue its false all-depth claim.

The failed three-prime class suggests adding the missing prime `5` rather
than abandoning the causal-union geometry.  For `210|n`, let `U_210(n)` be
the union of selected divisors visible at `n/2`, `n/3`, `n/5`, or `n/7`.
In expanded form this is the fifteen-term inclusion-exclusion expression over
the nonempty products of `{2,3,5,7}`.  At `n=420k`, the target floor bit is
zero, so

\[
 \boxed{U_{210}(420k)\ge Q_{420k-1}}           \tag{F420}
\]

would give a cofinal repair supply.  Unlike `(F84)`, this candidate retains
substantial slack in the deep replay: through rank fifty million it has
`119,047` rows, zero causal violations, zero equalities, and minimum causal
margin `+2`, first attained at rank `47612460`.  The actual repair inequality
on the same class has zero violations and minimum margin `+4`.

The fifteen target-bit terms cancel exactly at `420k`, so `(F420)` also has a
phase-free form `2L^-(n)-L(n)>=Q_(n-1)` for the corresponding signed
fifteen-scale defect combinations.  The extra slack therefore comes from the
additional selected-divisor ancestry exposed by the prime `7`, not from the
period-six source clock.

Lean defines the subtraction-free four-parent union, proves it is contained
in the full selected-divisor load, evaluates the exact base load
`U_210(420)=12`, proves the zero predecessor floor bit, and connects the
all-depth hypothesis to `not_universal_of_fourNinths_tetraprimeRepair`.
It now also exposes the exact prime-cofactor boundary.  For every prime
`p>7`, the fifteen-column identity and prime support split give

\[
 U_{210}(420p)=12+
   \#\{d: d\mid420,\ d<420,\ b_{pd}=1\}.
\]

The moving term is literally a filter on all twenty-three proper divisors of
`420`, so it is at most `23`; in particular any repaired prime row satisfies
`Q_(420p-1)<=35`.  This is an exact finite-coordinate reduction and a cheap
future falsifier, not a proof that the prime rows repair or that composite
cofactors descend to them.

There is nevertheless a precise way for those two missing statements to
meet.  Write `M(k)=U_210(420k)-Q_(420k-1)`.  The formal consumer
`fourNinths_tetraprimeRepair_of_primeBoundary_of_descent` proves the unit
cofactor exactly (`Q_419=7<12`) and asks for repair at every prime cofactor,
together with one proper divisor `a|k` with
`M(a)<=M(k)` for each composite `k`; strong induction then yields `(F420)` at
every positive cofactor.  The exact fifty-million-rank discriminator is
unlike the failed modulus-120 experiment: all `107,828` composite
largest-prime-factor deletion edges survive, with minimum difference `0`;
the weaker best-proper-divisor test also has zero violations and minimum
difference `4`, while every composite margin is at least `+9`.  All `11,214`
prime rows survive with zero equalities and minimum margin `+2`.  Thus every
tight `+2` or `+3` row in the full census is genuinely on the prime boundary.

The unit row sharpens the descent interface further.  Since
`U_210(420)=12` and `Q_419=7`, choosing the unit proper divisor shows that the
entire existential descent hypothesis follows from the phase-free composite
bound

\[
  Q_{420k-1}+5\le U_{210}(420k) \qquad(k>1\text{ composite}). \tag{CM5}
\]

Lean packages this as
`fourNinths_properDivisorDescent_of_compositeMarginFive` and connects it
directly to the full producer.  It also kernel-checks repair at the four
exceptional prime cofactors `2,3,5,7`; the exact finite evaluation gives their
margins as respectively `8,8,7,8`.  Consequently the prime obligation now begins genuinely at
`p>7`, rather than hiding a finite base inside a universal hypothesis.

An orthogonal ten-million-rank discriminator initially suggested the stronger
claim `M(k/q)<=M(k)` for every distinct prime factor `q` of `k`: all `57,462`
tested edges survived.  The fifty-million extension decisively falsifies that
claim.  Among `307,792` edges there are eight violations, all obtained by
deleting the smallest prime factor `2`; the worst margin drop is `-3`, first
at `k=40192`.  Every bad cofactor has the sharper form `2^a p` with `p`
prime.  The largest-prime-factor deletion statement still has no
violations, but universal divisibility monotonicity is no longer a live proof
route.

Crucially, this falsification leaves `(CM5)` untouched.  Across all `107,828`
composite cofactors in the same fifty-million gate, the minimum margin is
`+9`, so there are no violations of the five-unit boundary.  All seven rows
attaining `+9` are semiprimes `q p` with `q` in `{2,5,7}` and `p` prime.  The clean proof
geometry is therefore the direct split already exposed in Lean: prove the
large-prime boundary and prove `(CM5)` itself, without inserting a stronger
factor-lattice monotonicity lemma.  This remains finite evidence: neither
large-prime repair nor `(CM5)` is yet proved at all depths.
The all-depth causal inequality remains unproved.  Its finite evidence is
captured as
`cap_quick_four_ninths_modulus_420_tetraprime_produ_e65bb7551791`.

### Hundred-million-rank descent falsifier

The exact cylinder has now been replayed through rank `100,000,000`.  The
primary modulus-`420` producer remains positive on all `238,095` tested rows,
with no equality and minimum margin `+2`.  The prime boundary has no failure
among `21,060` primes above seven, again with minimum margin `+2`, and `(CM5)`
has minimum margin `+7` on `217,030` composite cofactors.

Replay with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/four_ninths_record_boundary_lab.py \
  --ranks 100000000 --fixed-point-crosscheck 0 \
  --output /tmp/four_ninths_100m.json
```

For this run the checker SHA-256 is
`12b412be922c31318e013875b0778263b3b75d69d0df986452cf2d065c5541c5`,
the imported cylinder engine SHA-256 is
`45745f784faa95a293cc462b42268a2801854c3fa1b225e4db5d4a961d5839bc`,
and the output SHA-256 is
`2441f69ec7b87c68e9f35c216e40c7a2091173bd78c5bded729ee2ddc6fcb1e2`.

The remaining largest-prime-factor induction, however, is false.  Its first
failure is

```text
k = 226726 = 2 * 113363,
parent cofactor = 2,
M(k) = 7 < 8 = M(2),
rank = 420*k = 95224920.
```

At the child row the defect and four-parent union load are `21` and `28`; at
the parent they are `9` and `17`.  Thus deleting the largest prime factor can
decrease the repair margin.  The existential proper-divisor descent still
survives this finite replay, but frequently only by choosing the unit
cofactor, so it supplies no recursive leverage beyond `(CM5)` itself.

This is an exact falsifier for the proposed monotone induction, not a
counterexample to `(F420)` or `(CM5)`.  The four-ninths route still requires a
direct all-depth prime-boundary theorem together with `(CM5)`; it is not a
cheaper replacement for the half-target first-fatal exclusion.
