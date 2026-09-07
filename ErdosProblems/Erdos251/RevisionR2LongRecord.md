# Erdős #251 Type B r2 long-record intake

Source: `state/formal_math/type_b_return_batches/erdos_revision_packets_r2_20260906/work/erdos_251/03_long_record_notes.md`.
This is a destination map and correction register, not a second manuscript.

## Argument map

The argument has three layers. Summation by parts and the dyadic recurrence
identify the exact arithmetic criterion. Countermodels show which properties of
an integer coefficient sequence cannot supply that criterion. The remaining
prime-specific task is a lower bound producing suitable configurations of
actual consecutive primes. Finite certificates establish particular inequalities
and denominator exclusions at a fixed precision.

The two live countermodels are complementary, not competing:

- Polynomial word `g_n = 2(n^2+4n+2)`, `T_n = 2(n+4)^2`, series value `32`
  (one-based gap series) / `18` (zero-based `Σ c_n 2^{-(n+1)}`). Palomar
  headline: `ExternalVerification251PolynomialShiftCountermodel`.
- Bounded rationalising perturbation of the *actual* prime gaps: binary digits
  of `(r-S)/M`, vanishing before a cutoff. Lean:
  `BoundedPerturbationCountermodel.lean`.

## Corrections absorbed from file 03

### Real-tail versus fractional-part dynamics

Rationality confines the fractional parts of the tails to an eventually
periodic orbit of multiplication by 2 modulo 1. Tails in the same eventual
residue class modulo the orbit period have integral difference. Their real
values can be distinct and unbounded. Witness: `U_N = 2(N+4)^2` is an injective
integral tail orbit already present in the polynomial countermodel.

### Sparsity

For each fixed offset, the adjacent-window event has natural density zero. Its
counting function could still tend to infinity; any positive lower bound tending
to infinity would prove cofinality. Density zero rules out a positive-proportion
conclusion and leaves sparse averaging available. The squares already show that
an average of an indicator can tend to zero while the unnormalised count tends
to infinity.

With `X` a prime-value cutoff, a scan consistent with count `X/(log X)^2` is a
finite heuristic. With `X` the number of prime indices, the corresponding scale
would be `X/log X`. Neither heuristic follows from Schlage-Puchta Lemma 4.

### Recurring small values

The factorial construction supplies `2` and `4` at indices in the common residue
class `0` modulo each fixed modulus, not in every index residue class. The
all-residue repair is `AllResidueCarryCountermodel.lean` (finite telescope
kernel-checked; scheduling lemmas).

### Parity

For even `M` the rationalising perturbation also preserves eventual evenness.
Qualitative size properties invariant under bounded additive changes transfer;
a theorem with a specified numerical bounded-gap constant requires its own check.

### Range comparison (mandate Q1)

`O(log N)` is not smaller than `(log log x)^3` under `x ≈ p_N ≈ N log N`.
Land's construction already uses an `O(log log X)`-sized structured tuple
(`k = ⌈log₂ log X + 4 log₂ ℓ⌉`) with at most two additional shifts, and span
`H = ⌊log X · ℓ³⌋`. Cardinality reduction below that size is already weaker
than the restriction present in the construction. Span reduction to `O(log X)`
is a different question and is not implied by the existing tail-selection
estimates.

### Q3 zero perturbation

A property required of the actual gaps and forbidden for *every* perturbation
`g + M ε` with `ε_n ∈ {0,1}` is impossible: the zero perturbation reproduces
the actual gaps. The live Lean statement is existential (there exist digits
making the sum rational), which is the coherent obstruction.

### Closed analytic bridge

Unconditional prime and gap summability, the actual real tail recurrence, and
the real/rational bridge are established in `PrimeGapDyadicTail.lean` and
`RealPrimeGapTail.lean`. The live prime-specific obligation is cofinal escape;
adjacent small mismatch is one sufficient producer.

### Fixed-lattice print repair

For a rational bound `b(N)` with `|D_N| ≤ b(N)`, fixed-lattice escape means:
for every cutoff `K` there exist `N > K` and `r ≥ 0` such that, for every
integer `z`, `|B_{h,N,r} − 2^r z| > b(N+r)`. The domination assumption is:
for every `N` and positive integer `q` there exists `r` with
`2 b(N+r) q < 2^r`. Under those two assumptions, cofinal fixed-lattice escape
is equivalent to failure of eventual integrality of `D_N`. Source:
`AffineCylinderCollapse.lean`.

## Destination of original short-note labels

See Type B file 03 table. The live corpus note retains the polynomial
countermodel as Palomar lead and absorbs the perturbation as a complementary
first-page mechanism. Research Propositions A–D stay out of the short note:
A is an unproved sufficient inequality; B is the free-pair count (Lean in
`FreePairCounting.lean`); C is a growing-block sieve estimate pending
specialist check of Kuperberg Theorem 4.1; D is the all-residue construction.
