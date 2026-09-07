# Polynomial Fourier decay of the Mersenne achievement set

Let

\[
  \mathcal A=\left\{\sum_{n\geq1}\frac{b_n}{2^n-1}:b_n\in\{0,1\}\right\},
  \qquad E=\sum_{n\geq1}\frac1{2^n-1}.
\]

[`FairCodingPushforward.md`](FairCodingPushforward.md) proves that fair
Bernoulli coding pushes forward exactly to Lebesgue measure restricted to
\(\mathcal A\).  This note extracts a quantitative harmonic consequence.
With

\[
  \widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i\xi x}\,dx,
\]

one has

\[
  \widehat{\mathbf1_{\mathcal A}}(\xi)
  =e^{-\pi i\xi E}\prod_{n\geq1}
    \cos\!\left(\frac{\pi\xi}{2^n-1}\right).                 \tag{1}
\]

## Uniform decay theorem

> **Theorem.** For every real \(\xi\) with \(|\xi|\geq1\),
> \[
> \boxed{
> \left|\widehat{\mathbf1_{\mathcal A}}(\xi)\right|
> \leq \left(\frac2\pi+\frac{2\pi}3\right)|\xi|^{-1/3}.}
> \tag{2}
> \]

**Proof.**  Formula (1) is the characteristic function of independent fair
digits:

\[
  \prod_n\frac{1+e^{-2\pi i\xi/(2^n-1)}}2
  =e^{-\pi i\xi E}\prod_n\cos\!\left(\frac{\pi\xi}{2^n-1}\right).
\]

Fix \(N\geq0\) and discard the first \(N\) cosine factors, whose absolute
values are at most one.  Compare the remaining Mersenne product with the
binary product.  For finite products of numbers of modulus at most one,

\[
  \left|\prod a_n-\prod b_n\right|\leq\sum|a_n-b_n|.          \tag{3}
\]

Since cosine is one-Lipschitz and

\[
  \frac1{2^n-1}-\frac1{2^n}
   =\frac1{2^n(2^n-1)}\leq2\,4^{-n},
\]

(3), followed by passage to the limit, gives

\[
 \left|\prod_{n>N}\cos\!\left(\frac{\pi\xi}{2^n-1}\right)
       -\prod_{n>N}\cos\!\left(\frac{\pi\xi}{2^n}\right)\right|
 \leq \frac{2\pi}{3}|\xi|4^{-N}.                            \tag{4}
\]

The binary product telescopes exactly:

\[
  \prod_{n>N}\cos\!\left(\frac{\pi\xi}{2^n}\right)
   =\frac{\sin(\pi\xi/2^N)}{\pi\xi/2^N},
\]

so its modulus is at most \(2^N/(\pi|\xi|)\).  Choose
\(N=\lceil\frac23\log_2|\xi|\rceil\).  Then
\(2^N\leq2|\xi|^{2/3}\) and \(4^{-N}\leq|\xi|^{-4/3}\).
Combining these estimates with (4) proves (2).  \(\square\)

The exponent \(1/3\) is the optimum of this first-order comparison: the
binary tail costs \(2^N/|\xi|\), while perturbing the Mersenne phases costs
\(|\xi|4^{-N}\).  A better exponent needs cancellation or higher-order phase
information, not a different choice of cutoff in the same bound.

## Half-integer Fourier zeros and their redundancy

Equation (1) also gives an infinite exact zero family.  For every \(m\geq1\)
and every integer \(k\),

\[
  \widehat{\mathbf1_{\mathcal A}}
  \left(\frac{(2k+1)(2^m-1)}2\right)=0,                      \tag{5}
\]

because the \(m\)-th factor is \(\cos((2k+1)\pi/2)=0\).
This indexing must not be mistaken for independent Mersenne resonance.
Every displayed frequency is an odd half-integer, so it is already killed by
the first factor \(\cos(\pi\xi)\), corresponding to the optional unit coin
\(w_1=1\).  Thus the exact zero set certified here is the single half-integer
lattice; varying \(m\) only gives redundant subfamilies.  The genuinely new
harmonic information is the all-frequency polynomial decay in (2), not an
additional hierarchy of spectral zero lattices.

## Resonance computation

[`scripts/fair_coding_fourier_decay_audit.py`](scripts/fair_coding_fourier_decay_audit.py)
evaluates (1) with directed `mpmath.iv` intervals.  Frequencies

\[
  L_m=\operatorname{lcm}_{1\leq n\leq m}(2^n-1)
\]

make the first \(m\) cosine factors have modulus one, so they are the natural
arithmetic stress test for (2).  Each finite product is extended to the
infinite product using

\[
  \prod_{n>N}\cos\!\left(\frac{\pi\xi}{2^n-1}\right)
  \geq 1-\frac{2\pi^2}{3}\xi^2 4^{-N}
\]

once the factors are in the positive small-angle range.  Same-bit-length
deterministic random integers are recorded as controls, and (5) is checked
symbolically rather than numerically, with its redundancy against the \(m=1\)
factor recorded in the receipt.

The default interval run gives the following representative rows.  The two
middle columns are \(-\log_2|\widehat{\mathbf1_{\mathcal A}}(\xi)|\); a smaller
number means more retained Fourier mass.

| \(m\) | bits of \(L_m\) | at \(L_m\) | matched control | LCM gain (bits) | observed exponent |
|---:|---:|---:|---:|---:|---:|
| 8 | 25 | 18.236 | 27.794 | 9.558 | 0.750 |
| 16 | 83 | 63.842 | 77.521 | 13.678 | 0.775 |
| 24 | 184 | 149.516 | 171.529 | 22.013 | 0.815 |
| 32 | 329 | 279.326 | 294.008 | 14.683 | 0.849 |

Thus exact LCM alignment is visible: it lifts the transform by factors as
large as \(2^{44.1}\) in the audited rows.  It does not produce a nondecaying
subsequence.  The measured exponent rises from about \(0.75\) to \(0.85\) on
the displayed LCM rows, far inside the proved \(1/3\) envelope and consistent
with an eventual \(|\xi|^{-1+o(1)}\) scale.  That last scale is a conjectural
reading of these finite rows, not a theorem.

Default command:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/fair_coding_fourier_decay_audit.py
```

The receipt is
`state/formal_math/erdos257_period_noncollapse/fair_coding_fourier_decay_receipt.json`.

This theorem does not decide whether a prescribed rational belongs to
\(\mathcal A\).  It opens quantitative Fourier and lattice-discrepancy tools;
the exceptional arithmetic-point input required by Erdős 257 remains separate.
