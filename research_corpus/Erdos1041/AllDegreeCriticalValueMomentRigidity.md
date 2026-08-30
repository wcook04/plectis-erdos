# Erdős 1041: low-mode critical-value moments and rigidity of the fully tight skeleton

Date: 2026-08-30. Exact symbolic replay:
`scripts/check_erdos1041_all_degree_critical_value_moment_rigidity.py`.
Consumes `AllDegreePhaseSturmReduction.md` and
`AllDegreeWallSheetSubharmonicReduction.md` only as downstream motivation;
the theorem below is an independent Newton-sum calculation.

## 1. Result

Let

```text
H(z)=z^n+sum_(1<=k<=K) b_k z^k,       n>=2,  0<=K<n,
```

and let `c_1,...,c_(n-1)` be the roots of `H'`, counted with
multiplicity.  Put `v_j=H(c_j)`.

> **Theorem CM (critical-value moment vanishing).**  If `r>=1` and
>
> ```text
>                    (r+1)K <= n-1,                         (CM1)
> ```
>
> then
>
> ```text
>                    sum_j v_j^r = 0.                       (CM2)
> ```

The case `r=1` recovers the trace identity in the exact range
`2K<=n-1`.  The new terminal consequence is the case `r=2`.

> **Corollary CR (collinear rigidity).**  If `3K<=n-1` and all critical
> values of `H` lie on one affine line in the value plane, then
>
> ```text
>                         H(z)=z^n.                          (CM3)
> ```

Thus, in this whole low-mode range, the fully tight terminal skeleton of the
phase/wall maximum-principle programme contains no nontrivial critically
collinear model.  It collapses to the pure-power equality stratum.

## 2. Newton gap at the critical multiset

Write `N=n-1`.  The monic critical polynomial is

```text
H'(z)/n=z^N+sum_(1<=k<=K) (k/n)b_k z^(k-1).          (CM4)
```

Every coefficient of degrees `K,...,N-1` is zero.  Newton's identities
therefore give

```text
sum_j c_j^m=0,             1<=m<=N-K=n-1-K.          (CM5)
```

At a critical point, multiplication of `H'(c)=0` by `c/n` eliminates the
leading term:

```text
H(c)=sum_(1<=k<=K) (1-k/n)b_k c^k.                   (CM6)
```

The right side has no constant term and degree at most `K`.  Its `r`-th power
is a linear combination of `c^m` with

```text
1<=m<=rK<=n-1-K,
```

where the last inequality is exactly (CM1).  Summing over the critical
multiset and applying (CM5) proves (CM2).

## 3. Collinearity becomes a sum of squares

Assume `3K<=n-1`.  The cases `r=1,2` of Theorem CM give

```text
sum_j v_j=0,                 sum_j v_j^2=0.           (CM7)
```

The first identity says that the mean of the critical values is zero.  If
they lie on an affine line, that line therefore contains zero, so for some
unit complex number `xi` there are real numbers `x_j` with

```text
v_j=xi x_j.
```

The second identity in (CM7) becomes

```text
xi^2 sum_j x_j^2=0.
```

Hence every `x_j=0`, and every critical value is zero.

It remains to identify the polynomial.  If a distinct critical point `a`
has multiplicity `m` as a zero of `H'`, then locally

```text
H(z)=H(a)+A(z-a)^(m+1)+higher terms,       A!=0.
```

Since `H(a)=0`, it is a zero of `H` of multiplicity exactly `m+1`.  If
there were `q>=2` distinct critical points, their forced zero
multiplicities would sum to

```text
sum_a (m_a+1)=(n-1)+q>n,
```

impossible for a degree-`n` polynomial.  Thus there is one critical point,
of multiplicity `n-1`, and `H=(z-a)^n`.  The missing `z^(n-1)` coefficient
forces `a=0`; the zero constant term then gives (CM3).

## 4. Sharp scope of the moment gap

The degree condition in Theorem CM is a structural sufficient range, not an
accidental checker cutoff.  Immediately beyond it the square trace can be
nonzero.  For

```text
H(z)=z^5+b_2 z^2+b_1 z,
```

Newton reduction gives the exact identity

```text
sum_(H'(c)=0) H(c)^2 = -(36/25)b_1 b_2^2.             (CM8)
```

Here `K=2` and `3K=6>4=n-1`.  Thus no square-trace rigidity is available on
the full maximal quintic two-mode core; its nontrivial fully tight orbit and
the compact double-tight analysis remain genuinely necessary.

## 5. Consequence and exact open boundary

Together with the degree-uniform phase and wall reductions, Corollary CR
removes the **final fully tight nondegenerate stratum** whenever
`3K<=n-1`: its only point is the pure-power equality model.  This is useful
for sparse coefficient faces and for inductive boundary strata whose top
modes have vanished.

It does **not** prove that successive wall reductions reach that stratum
without encountering a critical collision, a vanishing normalizing gap, or
a partially tight real residual.  It does not control the maximal near-Fekete
mode range `K=floor((n-1)/2)`, prove the model excess sign there, provide the
actual-polynomial transfer, or prove unrestricted Erdős 1041.

## 6. Replay

```bash
python3 research_corpus/Erdos1041/scripts/check_erdos1041_all_degree_critical_value_moment_rigidity.py
```
