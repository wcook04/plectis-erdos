# Certified continued-fraction denominator bounds

An exact rational enclosure gives large finite denominator exclusions for the
series in Erdős #68, #249 and #251. These computations leave irrationality open.

## Why the common prefix gives a bound

Run the continued-fraction algorithm on both endpoints of an enclosure of S.
Retain a quotient when their integer parts agree, subtract it, and invert the
remainders, reversing their order. Stop when the integer parts differ or an
endpoint remainder vanishes. Every retained quotient then belongs to every
number in the enclosure, including a rational S if there is one.

A rational in the enclosure cannot terminate before this common prefix. Its
reduced denominator is therefore at least the last convergent denominator Q,
computed by Q[-2]=1, Q[-1]=0, Q[k]=a[k]Q[k-1]+Q[k-2]. The probe also checks
that the penultimate convergent lies outside the enclosure.

The power bounds are calculated from Q using integer comparisons. If Q has
bit length b, then Q >= 2^(b-1). The strict decimal exponent d satisfies
10^d < Q <= 10^(d+1). These are separate bounds: the binary lower bound need
not itself exceed the decimal lower bound. Earlier receipts mistakenly used
size counts as exponents; the values below are the corrected full replays.

## Enclosures

- **#68:** Put D=2^B and let N be the first index with N!-1>D. Sum
  floor(D/(n!-1)) for 2<=n<N to obtain lo. Each term loses less than one,
  and the tail beginning at N is less than 2/(N!-1), since
  (n+1)!-1>(n+1)(n!-1). Thus hi=lo+(N-2)+floor(2D/(N!-1))+1.
- **#249:** The prefix sum of phi(n)/2^n through n=B is exact at scale
  2^B. Since phi(n)<=n, the omitted tail is at most (B+2)/2^B,
  giving hi=lo+B+2.
- **#251:** Sum the first B+128 terms of the zero-based prime series at
  scale 2^(B+128). Bound the omitted tail with p_i<=1250(i+1)^4,
  then round the enclosure outwards to scale 2^B.

## Full replay at B=80000

| Problem | Common quotients | Binary bound | Strict decimal bound | Scaled width |
|---|---:|---|---|---:|
| #68 | 23449 | q >= 2^39990 | q > 10^12038 | 7053 |
| #249 | 23438 | q >= 2^39989 | q > 10^12038 | 80002 |
| #251 | 23369 | q >= 2^39997 | q > 10^12040 | 1 |

For #251, the prime and prime-gap series differ by the integer 2, so the
same denominator bound applies to both.

For #68, the carry certificate additionally gives q not dividing 299999!.
Equivalently, q contains a prime power beyond its multiplicity in that
factorial. This can hold even when all prime factors of q are at most 299999.
The restriction on prime-power multiplicities and the restriction on size
capture different information.

For #249, the continued-fraction bound subsumes the finite exclusion for
divisors of 2^300(2^30-1), since these are below 2^330. The dyadic-family
exclusion can reach larger denominators within its specified family.

## Finite approximation diagnostics

A partial quotient a[i+1] gives an approximation exponent lower bound
2+log(a[i+1])/log(Q[i]). Its raw size is less informative without Q[i].
For example, #251's largest sampled quotient, 973919, occurs above a
convergent denominator near 10^8520 and contributes exponent about 2.0007.

| Denominator floor | #68 maximum | #249 maximum | #251 maximum |
|---|---:|---:|---:|
| 2^100 | 2.04554 | 2.05057 | 2.04818 |
| 2^1000 | 2.00675 | 2.00744 | 2.00771 |
| 2^10000 | 2.00099 | 2.00116 | 2.00099 |

These measurements describe the certified prefixes. They do not bound later
partial quotients or determine any target's irrationality exponent. The
reported Lévy and Gauss–Kuzmin comparisons are diagnostics, not certificate
inputs or grounds for excluding an infinite approximation method.

## Replay

```sh
./repo-python -m unittest formal_math.probes.test_certified_continued_fraction
./repo-python formal_math/probes/certified_continued_fraction.py --problem erdos_68 --scale-bits 80000
./repo-python formal_math/probes/certified_continued_fraction.py --problem erdos_249 --scale-bits 80000
./repo-python formal_math/probes/certified_continued_fraction.py --problem erdos_251 --scale-bits 80000
./repo-python formal_math/probes/certified_cf_publish_receipts.py
```

Each run checks the interval algorithm against the known continued fraction
of e and the convergent recurrence against 3, 22/7, 333/106 and 355/113 for pi.
Regression tests cover powers of two and ten and rational intervals with
terminating endpoint expansions.
