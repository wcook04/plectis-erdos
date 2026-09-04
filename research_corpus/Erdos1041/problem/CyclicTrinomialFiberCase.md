# Erdős #1041 for every centred trinomial and its cyclic translations

Status: analytic case theorem proved, current 2026-08-27.  The arbitrary-exponent
spoke estimate is kernel-checked in `CyclicTrinomialFiberCase.lean`.  This is
an exact all-scale solution family, not a proof of unrestricted Erdős #1041,
and no literature-priority claim is made.

The authority anchors are [`trinomialRoot_spoke_factorization`](CyclicTrinomialFiberCase.lean#L44-L53),
the all-root strict estimate
[`trinomialRoot_spoke_norm_lt_one_of_norm_lt_one`](CyclicTrinomialFiberCase.lean#L100-L140),
and the fibre displacement budget
[`cyclicTrinomial_two_short_fiber_displacements`](CyclicTrinomialFiberCase.lean#L142-L147).
Replay the complete Lean module from the repository root with:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.CyclicTrinomialFiberCase
```

These declarations certify the spoke identity, strict unit-lemniscate
containment, and the two-segment length budget used by this case theorem.  They
do not extend the result to translated coprime-exponent trinomials or to
unrestricted polynomials.

## The theorem

Let `m>r>=1` and `a,c` be complex.

1. Every centred trinomial

   ```text
   f(z)=z^m+a z^r+c
   ```

   whose zeros lie in the open unit disk satisfies Erdős #1041.

2. More generally, let `q>=2` and `h` be arbitrary.  Every translated cyclic
   trinomial

   ```text
   f(z)=(z-h)^(qm)+a(z-h)^(qr)+c
   ```

   whose zeros lie in the open unit disk satisfies Erdős #1041.

In fact every root-to-origin spoke in (1), and every root-to-`h` spoke in (2),
lies in `{|f|<1}`.  Thus any two zero occurrences may be joined through the
displayed hub, with length strictly below `2`; for a squarefree polynomial the
endpoint locations are distinct.

This settles all centred monic trinomials, in every degree and at every
coefficient scale allowed by the root hypothesis.  It also settles arbitrary
translations whenever the two positive exponents have a common divisor at
least two.  It strictly subsumes the earlier even-symmetric theorem, the case
`(m,r)=(2,1)` of (2).

## 1. The root and constant-term budgets are automatic

Put `y=z-h`, `w=y^q`, and

```text
P(w)=w^m+a w^r+c.
```

List the `m` quotient roots `w_1,...,w_m` with multiplicity.  Vieta gives

```text
|c|=product_k |w_k|.                                  (1)
```

In the centred case `q=1,h=0`, the quotient roots are exactly the roots of
`f`, so `|w_k|<1` for every `k`.

In the translated cyclic case, choose `y_k^q=w_k` and a primitive `q`-th root
of unity `zeta`.  The complete fibre

```text
h+y_k, h+y_k zeta, ..., h+y_k zeta^(q-1)
```

consists of zeros of `f` and hence lies in the open unit disk.  Averaging the
squared moduli over the regular orbit gives

```text
(1/q) sum_l |h+y_k zeta^l|^2 = |h|^2+|y_k|^2 < 1.     (2)
```

Thus again `|y_k|<1` and `|w_k|=|y_k|^q<1` for every `k`.  In both cases (1)
then gives `|c|<1` (with `c=0` already strict).

## 2. Every spoke is safe

Fix any quotient root `w`, choose `y^q=w`, and travel along its spoke as
`h+t y`, `0<=t<=1`.  Set `u=t^q`.  Since `w^m+a w^r+c=0`, eliminating
`a w^r` gives the exact identity

```text
f(h+t y)
  = u^m w^m + a u^r w^r + c
  = (1-u^r)c - (u^r-u^m)w^m.                        (3)
```

On `[0,1]` the two displayed coefficients are nonnegative.  Since
`|c|<1` and `|w|^m<1`,

```text
|f(h+t y)|
 <= (1-u^r)|c|+(u^r-u^m)|w|^m
 <  (1-u^r)+(u^r-u^m)
 =  1-u^m
 <= 1.                                               (4)
```

At `u=1` the value is exactly zero; for `u<1`, the first coefficient is
positive, so the strict inequality in (4) is valid.  Therefore the complete
spoke lies in the open unit lemniscate.  The Lean module checks (3) and this
strict coefficient argument for arbitrary natural exponents.

The earlier proof selected one Vieta-small root with `|w|^m<=|c|`.  Equation
(4) shows that selection was unnecessary: the target threshold is one, so the
open-disk bounds on `w` and `c` make **every** spoke safe.

## 3. The metric conclusion

Choose any two zero occurrences with displacements `y_1,y_2` and join them by

```text
h+y_1  -->  h  -->  h+y_2.
```

Both segments satisfy (4), and (2), or the centred root hypothesis, gives

```text
length=|y_1|+|y_2|<2.                                (5)
```

Repeated roots cause no difficulty: equal occurrences may use the constant
path, while any two distinct locations use (5).  No separate degeneration is
needed when `c=0`; identity (3) and the strict root-radius bound still apply.

## 4. Why this is a genuine closure

The higher-tangent computation suggested negative first-order length defect
for many models `z^n+a z^j+c`.  The exact algebra reveals a substantially
stronger fact: for a centred trinomial the path is already a literal safe
two-spoke path, at every scale, and for every exponent pair.  No critical
point, perturbative limit, root separation, or numerical premise remains.

The reusable mechanism is the coefficient partition

```text
(1-u^r)+(u^r-u^m)=1-u^m,
```

whose two terms match the constant term and the selected root power in (3).
This is the analytic reason the entire three-term class is radially visible.

The remaining sparse boundary is now exact: arbitrary translations with
`gcd(n,j)=1` have neither the origin as the physical centre nor a nontrivial
cyclic fibre whose mean-square identity controls displacement from the
translation centre.

## Exact handoff

The Refinery should promote the centred-trinomial theorem as the headline
sparse-polynomial closure and preserve the even-symmetric theorem as its
historical quadratic-quotient specialization.  The Closure Engine should next
attack translated coprime-exponent trinomials or return this radial coefficient
partition to the unrestricted polynomial problem.
