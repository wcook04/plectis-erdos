# Digital-height comparison: the existing full-support certificate cannot meet a final-skip gap

## Scope

Let `M` be a final greedy skip for target `1/21`, `F = twentyOneSkippedPrefix M`,
`s_F = finiteErdosSum F 2`, `p_F = 1/21 + s_F`, and
`δ_F = p_F - erdosBorweinMersenneConstant`. The cofinite selected support has
coefficient `τ - c_F`. This note asks whether the *existing* full-support
(`τ`) certificate construction can be quantitative in `M` enough to defeat
the known `O(4^-M)` fatal gap. It introduces no new theorem.

## Formal inputs

`lastTwentyOneSkip_erdosBorwein_fatalInterval`
([TwentyOneQuotientGreedy.lean:3735](../../Erdos257PeriodNoncollapse/TwentyOneQuotientGreedy.lean#L3735)) proves, from a final skip,

```text
0 < δ_F < mersenneGap M.
```

`mersenneGap_le`
([HalfGapMass.lean:45](../../Erdos257PeriodNoncollapse/HalfGapMass.lean#L45)) proves

```text
mersenneGap M ≤ (2/3)·4^(-M) + 3·8^(-M)  (M > 0).
```

Put `D = s_F.den`. With the routine nonempty/nonzero/lcm hypotheses on the
actual prefix, `lcm_lt_den_finiteErdosSum`
([CertificateKernel.lean:5260](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L5260)) gives `F.lcm id < D`.
As `M ∈ F`, this yields `M < D`. Set `q = 21D`; then `q p_F` is an integer.
This deliberately avoids claiming that the *reduced* denominator of `p_F`
retains `D`, which addition of `1/21` could cancel.

For full support, `supportCoeff_univ_eq_card_divisors`
([CertificateKernel.lean:9062](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L9062)) identifies the coefficient with `τ`.
At base `2`, period `1`, requested precision `Q`,
`exists_weighted_coeff_certificates_supportCoeff_periodic`
([CertificateKernel.lean:11588](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L11588)) literally chooses

```text
B = 2,
K = 9(Q + 103),
κ = 3(4K² + 1) + (4K²(K(K+1)+1) + Q + 4),
L = 2^κ.
```

Its closure arithmetic is certified in
`certificate_param_arithmetic_periodic`
([CertificateKernel.lean:11448](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L11448)).
The exact-valuation frame provides a prime `p > L` in the first block
([CertificateKernel.lean:11307](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L11307)); at its application in the certificate proof
([CertificateKernel.lean:11613](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L11613)), that prime divides `N+1`. Thus the constructed exponent has

```text
N ≥ L = 2^κ.
```

This is a direct deduction from the proof's exposed frame data. Since
`K ≥ 9Q`, its literal schedule gives

```text
κ ≥ 4K^4 ≥ 26244 Q^4,
N ≥ 2^(26244 Q^4).                                      (1)
```

`near_int_witness_of_weighted_coeff_block_certificate_linear`
([CertificateKernel.lean:12345](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L12345)) then turns the block into `0 < 2^N E - z < 1/Q` for an integer `z` and the full-support series `E`.

## Exact comparison

Request the certificate at `Q = 2q = 42D`, and write
`ε = 2^N E - z`; so `0 < ε < 1/(2q)`. Since `q p_F` and `z` are integers,

```text
H = q·2^N·p_F - qz = q·2^N·δ_F + qε
```

is a positive integer. Hence the one strict condition

```text
2q · 2^N · mersenneGap M < 1                         (DH)
```

would contradict existence of the final skip: the fatal interval makes the
first term in `H` below `1/2`, and certificate precision makes the second
below `1/2`.

## Quantitative no-go for the present schedule

The fatal interval supplies only the `4^-M` scale. Even the coarse
consequence `mersenneGap M ≤ 2·4^-M` would make (DH) require approximately

```text
N < 2M - log₂(q) - O(1).                              (2)
```

But `D > M`, hence `Q = 42D > 42M`; while the actual construction forces

```text
N ≥ 2^(26244 Q^4) > 2^(26244 (42M)^4).
```

Therefore the existing gap upper bound cannot prove (DH) for the literal
certificate constructed by
`exists_weighted_coeff_certificates_supportCoeff_periodic`: multiplying by
`2^N` destroys its `4^-M` saving.

This is a narrow no-go. It does not say that `δ_F` is not far smaller than
its known upper bound, nor that a different short certificate cannot exist.
It says that these exact two existing outputs do not compose. The
eventual-periodic reduction also provides no `M`-to-`N` height bound; its
consumer retains an integer multiplier but makes no such quantitative claim:
`irrational_of_rat_prefix_tail_near_int_witnesses`
([CertificateKernel.lean:9688](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L9688)).

## Smallest missing digital-height lemma

The minimal joint bridge is:

```text
For D = (finiteErdosSum (twentyOneSkippedPrefix M) 2).den and q = 21D,
there is a full-support near-integer certificate at precision 2q with
exponent N satisfying 2q · 2^N · mersenneGap M < 1.
```

It immediately contradicts a final skip by the integer `H` above. A more
syntactic sufficient assertion is `N ≤ 2M - ceil(log₂(8q))`; the current
prime-frame construction has the opposite scale. Retaining its huge `N`
would instead demand the much stronger, absent estimate
`δ_F < 1/(2q·2^N)`. Thus the missing datum is a joint digital-height theorem
coupling a final skip, its clearing denominator, and a near-integer exponent;
it is not another qualitative divisor-coefficient certificate.
