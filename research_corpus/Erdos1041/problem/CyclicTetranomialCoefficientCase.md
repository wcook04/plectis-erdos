# Erdős #1041 for a coefficient-controlled cyclic tetranomial class

Status: analytic theorem proved, current 2026-08-27; the arbitrary-exponent
Abel identity and strict norm budget are formalized in
`CyclicTetranomialCoefficientCase.lean`.  This is an exact all-degree solution
class, not an unrestricted solution, and no literature-priority claim is made.

The authority anchors are [`tetranomialRoot_spoke_factorization`](CyclicTetranomialCoefficientCase.lean#L26-L36),
the root-dependent tail estimate
[`tetranomialRoot_spoke_norm_lt_one_of_rootBudget`](CyclicTetranomialCoefficientCase.lean#L143-L160),
and the coefficient-only case theorem
[`tetranomialRoot_spoke_norm_lt_one_of_lowCoeffBudget`](CyclicTetranomialCoefficientCase.lean#L162-L180).
Replay the complete Lean module from the repository root with:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.CyclicTetranomialCoefficientCase
```

These declarations certify the Abel decomposition and strict spoke estimate;
the quotient-root and cyclic-fibre hypotheses remain the ordinary analytic
steps recorded below.  The theorem does not extend to unrestricted
four-term polynomials or to unrestricted Erdős #1041.

## The theorem

Let

```text
g(w)=w^m+a w^r+b w^s+c,       m>r>s>=1.               (1)
```

Assume all roots of `g` lie in the open unit disk and order two smallest root
moduli as

```text
|w_1| <= |w_2| <= |w_j|.                               (2)
```

If

```text
|c|+|b| |w_2|^s < 1,                                  (3)
```

then the two spokes from `w_1,w_2` to the origin lie in `{|g|<1}` and their
broken line has length strictly below `2`.

Two convenient all-spoke corollaries are

```text
R=max_j |w_j|<1 and |c|+|b| R^s<1,                    (3a)
```

and the coefficient-only condition

```text
|b|+|c| <= 1,                                          (3b)
```

which implies (3a).

More generally, let `q>=2`, let `h` be complex, and put

```text
f(z)=g((z-h)^q).                                       (3)
```

If all listed roots of `f` lie in the open unit disk and the two-smallest-root
condition (3), or either simpler corollary, holds for the quotient roots, the
corresponding fibre spokes are contained in `{|f|<1}` and the selected listed
roots are joined through `h` with length strictly below `2`.  Thus Erdős #1041
holds for this family in every total degree `qm`.

The coefficient `a` is completely unrestricted.  The conditions control only
the new lower monomial and the constant term; when `b=0` it recovers the
unconditional centred-trinomial mechanism.

## 1. Abel summation along a root spoke

Fix a root `w` of `g` and put

```text
T = a w^r+w^m = -(c+b w^s).                            (4)
```

For `0<=u<=1`, direct use of `g(w)=0` gives

```text
g(uw)
 = (1-u^s)c -(u^s-u^r)T -(u^r-u^m)w^m.               (5)
```

This is the four-term instance of Abel summation.  Because
`m>r>s` and `u` lies in the unit interval, its three scalar coefficients are
nonnegative and add to

```text
(1-u^s)+(u^s-u^r)+(u^r-u^m)=1-u^m.                   (6)
```

The identity is the mechanism: it replaces an apparently uncontrolled
four-term polynomial value by a subconvex combination of three tail sums.

The same calculation gives a general Abel-tail criterion.  For exponents

```text
0<k_1<...<k_N=m,       g(w)=c+sum_j a_j w^(k_j),
T_i(w)=sum_{j=i}^N a_j w^(k_j),
```

the root equation says `T_1=-c`, and summation by parts gives

```text
g(uw)=(1-u^(k_1))c
      -sum_{i=2}^N (u^(k_(i-1))-u^(k_i)) T_i(w).       (6')
```

All coefficients are nonnegative and sum to `1-u^m`.  Therefore any root for
which `|c|<1` and every proper upper tail `|T_i(w)|<1` has a completely safe
spoke.  The tetranomial theorem is a solved, coefficient-visible instance of
this general criterion: it has only one nontrivial proper tail, and (4) makes
that tail depend on `b,c` but not on `a`.

## 2. The coefficient budget controls the new tail

The open-disk root hypothesis gives `|w|<1`.  Since `g` is monic and all its
roots lie in the open disk, Vieta also gives

```text
|c|=product_j |w_j|<1.                                (7)
```

For either selected root `w_i`, equation (4), the triangle inequality, and (3)
now yield

```text
|T| = |c+b w^s|
    <= |c|+|b| |w|^s
    <= |c|+|b| |w_2|^s
     < 1.                                              (8)
```

Under the coefficient-only condition (3b), the last inequality follows
because `|w_2|^s<1` when `b!=0`, while for `b=0` it is exactly (7).  Condition
(3a) is immediate from `|w_i|<=R`.  We also have `|w^m|<1`.  Applying the
triangle inequality to (5), using (6)--(8), gives

```text
|g(uw)| < 1-u^m <= 1.                                 (9)
```

At `u=1` the value is zero, so the strict conclusion holds on the complete
spoke.  This proves the centred theorem.

## 3. Cyclic lifting and the length budget

For (3), let `w` be a quotient root and choose `y` with `y^q=w`.  The complete
regular fibre

```text
h+y, h+y zeta, ..., h+y zeta^(q-1)
```

consists of listed roots of `f`.  Averaging their squared moduli gives

```text
|h|^2+|y|^2<1.                                        (10)
```

Hence `|y|<1` and `|w|=|y|^q<1`; Vieta again gives (7) for the quotient.
The segment `h+t y`, `0<=t<=1`, maps under (3) to the quotient spoke with
`u=t^q`, so (9) proves its containment.  Any two chosen fibre displacements
have total length below `2` by (10), and their two spokes meet at `h`.

## 4. Computation, proof authority, and boundary

A fixed-seed falsification probe sampled 1,707 admissible tetranomials through
degree ten, evaluating every accepted root spoke on a 401-point mesh.  It found
no violation; the largest sampled value was `0.9380688`.  That computation
revealed no exceptional exponent pattern, but it is not proof authority.
Equations (4)--(10) are the exact analytic proof, and the Lean companion checks
the load-bearing arbitrary-exponent identity and norm estimate.

A separate unrestricted probe, which did **not** assume (3), (3a), or (3b), accepted
6,348 configurations and never found fewer than two roots with
`|c+b w^s|<1`.  Adversarial coefficient hill-climbs across seven exponent
patterns also failed to push the second-smallest tail above one (the largest
observed value was about `0.94755`).  This is evidence for the next selector
conjecture only; it is not used in the theorem and is not reported as a proof.

A fresh 3,204-configuration coverage audit found that the proved
two-smallest-root condition (3) itself certified 3,173 cases (`99.03%`).  The
remaining 31 still had two tail-safe roots numerically, but they stay outside
the theorem until the selector residual is proved or refuted.

The unrestricted tetranomial problem without the two-root condition (3), and
unrestricted Erdős #1041, remain open.  The next analytic question is whether two roots must
satisfy the tail bound `|a w^r+w^m|<1` even when the coefficient budget fails;
that is a genuinely weaker selector problem, not an equivalent reformulation.

## Exact downstream handoff

After the exact Lean target passes, the Refinery should retain this as the
first multi-lower-term extension of the centred-trinomial theorem, attribute
the computation as discovery evidence only, and route the residual to a
two-root tail-sum selector or a counterexample search.  No novelty or priority
claim should be made before literature review.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_cyclic_tetranomial_coefficient.py
```
