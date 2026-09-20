<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Totient Hankel matrices: maximal uniform obstruction, small mean error

For the normalized totient sequence

\[
h(m)=\frac{\varphi(m)}m\quad(m\ge1),\qquad H(i,n)=h(i+n)\quad(i,n\ge1),
\]

the distance from the entire infinite matrix to matrices of finite separated
rank is exactly one half in the uniform norm. Yet a single explicit family of
finite-rank matrices approximates every leading finite square in mean absolute
error, with bounds independent of the square's size.

These are **candidate ordinary mathematical results with proofs below**. They
have been cross-checked as ordinary arguments but have not been formalized
or independently reviewed by an expert. The companion Python
program verifies finite rational identities, factorizations and inequalities;
it does not verify the infinite assertions. No novelty or irrationality claim
is made. The work connects two existing arguments in the public corpus: the
arithmetic separation behind #249 and the compactness argument already written
for #269. It is separate from sparse factorial interpolation.

The initial corpus reading used commit
`cd92136f7f0f03bd78fb8753e4e4f0527dbe3a83`; the scoped experiment was written
with `HEAD` at `c1321314644cb6bf00434236e33656a01ec57286`. Source paths and
declaration names below identify the ingredients more reliably than line counts.

## 1. Arithmetic translates are separated by exactly one

**Proposition.** For any distinct positive integers \(i,j\),

\[
\sup_{n\ge1}|h(n+i)-h(n+j)|=1.
\]

**Proof.** Set \(\Delta=j-i\ne0\). Given \(\eta>0\), choose a finite set of
primes \(P\), none dividing \(\Delta\), such that

\[
\prod_{p\in P}(1-1/p)<\eta/2.
\]

Such a set exists because the reciprocal-prime series diverges; deleting
finitely many primes does not change that fact. Put \(M=\prod_{p\in P}p\).
The congruences \(q\equiv-\Delta\pmod p\) combine to
\(q\equiv-\Delta\pmod M\). This is a reduced residue class because
\(\gcd(M,\Delta)=1\). Dirichlet's theorem supplies a prime in this class
large enough that \(q>i\) and \(1/q<\eta/2\). With \(n=q-i\), both
arguments are positive, \(n+i=q\), and \(M\mid n+j=q+\Delta\). Thus

\[
h(n+i)=1-1/q>1-\eta/2,
\qquad h(n+j)\le\prod_{p\in P}(1-1/p)<\eta/2.
\]

The difference exceeds \(1-\eta\). Every value of \(h\) lies in \((0,1]\),
so the supremum is one. It need not be attained. The same argument works
after any fixed lower cutoff on the column index. ∎

## 2. The exact uniform finite-rank error

A real matrix has finite separated rank if, for some finite \(r\),
\(A(i,n)=\sum_{a=1}^r f_a(i)g_a(n)\). No boundedness of the individual
factors is assumed.

**Proposition.**

\[
\inf_{A\text{ of finite separated rank}}
\sup_{i,n\ge1}|H(i,n)-A(i,n)|=\frac12.
\]

**Proof.** Suppose the error were \(\varepsilon<1/2\). Each row of \(A\)
would then have supremum norm at most \(1+\varepsilon\). The span of these
rows is finite dimensional and consists of bounded sequences, regardless of
whether the originally chosen factors were bounded. Distinct rows satisfy

\[
\|A_i-A_j\|_\infty\ge\|H_i-H_j\|_\infty-2\varepsilon
=1-2\varepsilon>0.
\]

This would be an infinite uniformly separated family in a bounded subset of
a finite-dimensional normed space, contradicting total boundedness. The
constant matrix \(A(i,n)=1/2\) has rank one and error at most \(1/2\), which
proves equality. ∎

The proof deliberately reuses the existing #269 compactness argument. Exact
infinite rank alone would not imply this conclusion: the arithmetic metric
separation is the additional premise that makes the argument apply.

## 3. Explicit low-rank mean approximation, at every finite size

Let \(\mu\) denote the Möbius function. For a positive integer \(D\), define

\[
A_D(i,n)=\sum_{1\le d\le D}\frac{\mu(d)}d\mathbf1_{d\mid i+n}.
\]

**Proposition.** This single infinite matrix has separated rank at most
\(D(D+1)/2\), and for every positive integer \(N\),

\[
\frac1{N^2}\sum_{i,n=1}^N|H(i,n)-A_D(i,n)|\le\frac2D.
\]

**Proof of the rank bound.** For each positive \(d\),

\[
\mathbf1_{d\mid i+n}
=\sum_{a=0}^{d-1}\mathbf1_{i\equiv a\pmod d}
                         \mathbf1_{n\equiv-a\pmod d}.
\]

These are \(d\) explicit separated factors. Summing over \(d\le D\) gives
the bound \(\sum_{d\le D}d=D(D+1)/2\). The smaller bound
\(\sum_{d\le D,\,\mu(d)\ne0}d\) is also immediate. These bounds are not
asserted to be exact ranks.

**Proof of the error bound.** The divisor identity
\(h(m)=\sum_{d\mid m}\mu(d)/d\) gives

\[
|h(m)-\sum_{d\le D,\ d\mid m}\mu(d)/d|
\le\sum_{d>D,\ d\mid m}\frac1d.
\]

At most \(N\) pairs in \(\{1,\ldots,N\}^2\) have any prescribed sum.
Consequently the mean error is at most

\[
\begin{aligned}
\frac1N\sum_{m=1}^{2N}\sum_{d>D,\ d\mid m}\frac1d
&=\frac1N\sum_{D<d\le2N}\frac{\lfloor2N/d\rfloor}{d}\\
&\le2\sum_{d>D}\frac1{d^2}\le\frac2D.
\end{aligned}
\]

The final inequality follows by comparison with
\(\int_D^\infty x^{-2}\,dx\). All sums preceding that comparison are finite.
If \(D\ge2N\), the approximation is exact on the square. ∎

Thus average error \(\le\varepsilon\) is achieved with
\(D=\lceil2/\varepsilon\rceil\) and rank \(O(\varepsilon^{-2})\), uniformly
over all leading square sizes. Each truncated sequence is periodic, with a
period dividing \(\operatorname{lcm}(1,\ldots,D)\). A one-dimensional version
of the same counting argument gives prefix mean error \(\le1/D\) for
\(h(m)\), so this also supplies a direct Besicovitch mean approximation by
periodic sequences.

The leading-square restriction matters: no bound uniform over arbitrary
translations of a fixed finite square is asserted. Nor is the rate claimed
optimal. Entrywise division by \(i+n\) is not a row or column rescaling, so
the result cannot be transferred unchanged to the unnormalized totient kernel.

## 4. Exact probe and next formal target

Run from the repository root:

```sh
python3 research/experiments/premise_exchange/totient_approximation.py
```

The program uses only the Python standard library and exact `Fraction`
arithmetic. It checks the Möbius identity through each matrix's largest
argument, the residue-factor identity on all residue pairs up to the cutoff,
the explicit factorization on leading blocks of size at most 16, and the
mean-error inequalities on the complete leading squares
\((N,D)=(1,1),(8,2),(32,4),(128,8),(256,16)\). Antidiagonal multiplicities
cover every entry of each square exactly. Four reduced-progression prime
witnesses test the distinct arithmetic premise, including a shift difference
divisible by both 2 and 3. Trial division certifies the primes used; the search
is bounded by 10,000 progression candidates for each chosen modulus.

For example, the \((128,8)\) matrix has a certified rank upper bound 24 and
mean absolute error approximately 0.036205; the general proved bound is 0.25.
The numerical value illustrates the experiment, not an improvement to the
proved rate. The JSON output gives exact fractions as well as decimals.

The useful formal target is a generic lemma: an infinite family of bounded
rows with pairwise supremum distance at least \(\delta>0\) forces uniform
finite-rank error at least \(\delta/2\). Instantiate it with the already
written #269 threshold separation and the totient progression separation
above. Separately formalize the finite divisor-counting mean bound. This tests
the actual reusable proof premise; it does not ask Lean to infer arithmetic
separation from unrelated rank declarations. No Lean build was run for this
experiment.

## 5. Native sources and prior art

- [The #269 long paper](../../../paper/269/erdos269-running-lcm-reasoning-surface.tex),
  subsection **The exact uniform approximation error**, theorem label
  `long269:res:uniform-rank`, already proves the normalized running-LCM
  threshold matrix's sharp uniform barrier by total boundedness. Its later
  comparison explains why the original geometrically decaying kernel admits
  uniform finite-rank approximations. This is an existing ordinary proof,
  not a new finding of this experiment.
- [The #249 short paper](../../../paper/249/erdos-249-binary-totient-series.tex),
  section `sec:rank` and appendix **Affine independence in the earlier
  literature**, gives the CRT/Dirichlet separation mechanism and its credit.
  [TotientMahlerDefect.lean](../../../lean/Erdos249257/TotientMahlerDefect.lean)
  contains `exists_affine_root_mod_prime`, `affine_target_coprime_of_cross`,
  `exists_totientAffinePrimeRow`,
  `exists_separatedMinorCertificate_totientAffineOddFamily`, and
  `linearIndependent_totientAffineOddFamily`. These exact interfaces informed
  the choice of mechanism; none is asserted to prove the normalized Hankel
  statement here. In that file, “normalized affine” means canonical affine
  channels, not the quotient \(\varphi(m)/m\).
- Greg Martin, [*Simultaneous inequalities among values of the Euler
  phi-function*](https://arxiv.org/pdf/math/0603053), Theorem 1, pp. 1–2,
  proves arbitrary simultaneous ratio inequalities for nonproportional
  affine forms on a set of positive lower density. It is prior art for
  arithmetic separation and is already credited in the native #249 paper.
  Its ratio statement alone is not being used as a substitute for the
  additive distance-one proof above.
- V. Bergelson, J. Kułaga-Przymus, M. Lemańczyk and F. K. Richter,
  [*Rationally almost periodic sequences, polynomial multiple recurrence
  and symbolic dynamics*](https://people.math.osu.edu/bergelson.1/BK-PLR_APS_Symb.pdf),
  Definition 1.1 and Corollary 2.17, pp. 3 and 17, explicitly treat rational
  almost periodicity and the sets \(\{n:\varphi(n)/n<x\}\). Mean periodic
  approximation of arithmetic data therefore has substantial antecedents;
  it is not claimed as a new phenomenon here. The explicit finite-matrix
  rank/error pairing is the question examined in this note, with priority
  unassessed.

## 6. Why this connection was selected across the eight papers

The selection read the actual central statements and arguments in these
papers, with exact Lean interfaces inspected for the selected transfer. It
was not an exhaustive audit of every declaration.

| Programme and named source | Mechanism considered and selection consequence |
|---|---|
| #68, `paper/68/erdos-68-factorial-denominator-irrationality.tex` | Strict factorial successor and nonunit-carry denominator exclusion. Valuable exact arithmetic, but no new cofinal producer emerged in this pass. |
| #243, `paper/243/erdos-243-reciprocal-tail-rigidity.tex` | The bounded-negative-part and bounded-rise CRT barrier. Its extra boundedness premise cannot be silently supplied by the original growth condition. |
| #249, `paper/249/erdos-249-binary-totient-series.tex` | All-base kernel bases, affine separation, and exact rank certificates. Selected its arithmetic separation mechanism, after changing the object to a bounded normalized Hankel kernel. |
| #251, `paper/251/erdos-251-prime-gap-dyadic-series.tex`; `lean/ErdosProblems/Erdos251/ResidueFeedbackCore.lean` | Sparse congruence-preserving interpolation and one-site feedback. These were already being developed in the separate factorial/support direction. |
| #257, `paper/257/erdos-257-mersenne-support-subseries.tex`; `paper/synthesis/erdos-synthesis-subsums-across-bases.tex` | Weighted finite-prime supports and divisibility-chain rational-base continuation. Arbitrary ratio words remain a genuine boundary; no unsupported universal Mahler transfer was selected. |
| #269, `paper/269/erdos-269-three-prime-running-lcm.tex` and its long paper above | Exact threshold minors and the already-written uniform-rank barrier. Selected the compactness premise rather than rediscovering the existing conclusion. |
| #1041, `paper/1041/erdos-1041-lemniscate-newton-flow.tex`; `lean/ErdosProblems/Erdos1041/Counterexample/InstanceConnectivity.lean` | Trinomial radial control, four-term radial failure, and whole-segment Bernstein certificates. A general certificate-completeness algorithm would need an additional proof; the existing four segment certificates already replace many subdivisions. |
| #1049, `paper/1049/erdos-1049-rational-base-lambert.tex` | Rational-base denominator obstruction, contour-region irrationality and normalized Hankel determinants. Smith-normal-form discussion already appears in the paper, so proposing it alone would add no new mechanism. |

A further connection worth separate treatment is #269's finite threshold
minor with the greater-than matrix in approximate-rank theory. Alon, Lee,
Shraibman and Vempala's
[*The Approximate Rank of a Matrix and its Algorithmic Applications*](https://web.math.princeton.edu/~nalon/PDFS/epsrank9.pdf),
§3.2, studies that matrix. It distinguishes finite-sample approximate rank
from the infinite uniform obstruction, but importing those established
bounds is a different task from the arithmetic proposition proved here.

The reasoning change is specific: read the conclusions of one paper as
possible hypotheses for another argument, then identify the missing metric
premise. Here the missing premise is an extremal distance between translates;
prime progressions supply it, while the divisor expansion exposes a different
norm in which the same object is easy to approximate. Similar words such as
“rank” do not by themselves license a transfer.

## Scope and consumers

The new files are an ordinary proof and a reproducible experiment. The #249
and #269 Lean sources, papers, claim registry and unresolved irrationality
endpoints are unchanged. Promotion to a formal result or paper requires
meaning review, formalization if claimed, and a focused prior-art review.
The generic compactness lemma and the finite divisor-counting bound are
concrete next consumers; publication and public claim changes are deferred
to that review. This result supplies no irrationality certificate for either
Erdős problem.
