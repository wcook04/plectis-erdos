<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# When does a product meet its error bound?

Suppose two functions are approximated by polynomials on $0<t\leq 3/10$:

$$
P(t)=\frac54t^2,\qquad Q(t)=2t^3,\qquad
|f(t)-P(t)|\leq\frac1{20}t^4,\qquad
|g(t)-Q(t)|\leq\frac1{10}t.
$$

You want to discard terms of degree three and higher in the product and
guarantee a remainder at most $(7/20)t^3$. The retained polynomial is zero,
since $PQ=(5/2)t^5$. **Do the supplied error bounds guarantee
$|fg|\leq (7/20)t^3$ throughout the interval?**

This is a worked application of `CKLaneA3X.Encl.mul`, from the
[Courtade–Kumar Lean project](https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TM.lean#L193),
using its [Formalpedia export and proof](https://github.com/prove2me/formalpedia/blob/2ce1f7ce2a5eec4c20eb25ac85f36e94db89779a/envs/0df444a/Solutions/Sol_CKLaneA3X_Encl_mul.lean).
The export credits the selected submission to `@marwahaha`. The theorem and
its proof are prior work; this note and the arithmetic checker were prepared
with Codex in Will Cook's research workflow. The
[source record](enclosure-product-use.sources.json) identifies the original
objects, revisions and file hashes.

You can answer the opening question with polynomial algebra. The formal
theorem is useful because it gives a reusable rule for multiplying many such
approximations. Try the question first, then compare the three conclusions
below.

## What the multiplication rule needs

An enclosure records a polynomial $P$, a nonnegative remainder $r_1$ and an
order $n_1$, meaning $|f-P|\leq r_1t^{n_1}$. Similarly,
$|g-Q|\leq r_2t^{n_2}$. Let $v_1$ and $v_2$ be orders below which the
coefficients of $P$ and $Q$ vanish. To retain only degrees below $n$, the
theorem requires

$$
v_1\leq n_1,\qquad n\leq v_1+n_2,\qquad n\leq v_2+n_1.
$$

There is no premise $v_2\leq n_2$. Here the orders are
$(n_1,n_2,v_1,v_2,n)=(4,1,2,3,3)$, which satisfy all three conditions,
even though $v_2>n_2$.

The source allows polynomial coefficients that depend on a second variable
$\rho$, with $0<\rho<1$. Its coefficient bounds hold uniformly in that
variable. Our coefficients and functions are independent of $\rho$, so the
same example works for every allowed $\rho$. The actual endpoint in the
pinned numeric definition is $T=3/10$; an inherited domain comment says
$7/50$, but that comment does not define the domain.

Write $\beta_i$ and $\gamma_j$ for nonnegative bounds on the absolute values
of the coefficients, and put

$$
B_1=\sum_{i\geq v_1}\beta_iT^{i-v_1},\qquad
B_2=\sum_{j\geq v_2}\gamma_jT^{j-v_2},\qquad
H=\sum_{i+j\geq n}\beta_i\gamma_jT^{i+j-n}.
$$

All sums are finite. The source computes $H$ recursively as `HB`; the checker
compares that recurrence with this double sum. If $R$ is $PQ$ truncated to
degrees below $n$, the theorem gives $|fg-R|\leq rt^n$ whenever

$$
H+(B_1+r_1T^{n_1-v_1})r_2T^{v_1+n_2-n}
  +B_2r_1T^{v_2+n_1-n}\leq r.
$$

The shape of the bound comes from one identity:

$$
fg-R=f(g-Q)+Q(f-P)+(PQ-R).
$$

The first term uses the bound on the whole function $f$, including its
remainder. This already accounts for the product of the two errors; adding
another cross-error term would count it twice. Bounding $f$ also explains
why the displayed hypotheses distinguish the two input orders.

## The sufficient test misses the requested target

For our polynomials, use coefficient bounds
$\beta=(0,0,5/4)$ and $\gamma=(0,0,0,2)$. Then $B_1=5/4$ and $B_2=2$.
The three terms in the rule are

$$
\frac9{40}+\frac{2509}{20000}+\frac{81}{100000}
=\frac{17563}{50000}=0.35126.
$$

The requested value is $7/20=0.35$, so the sufficient test fails.
That alone does **not** prove the requested estimate false: a sufficient
bound can be too generous. We need to look at what the given information
allows.

## A compatible pair really does exceed the target

Choose both errors positive and as large as permitted:

$$
f(t)=\frac54t^2+\frac1{20}t^4,\qquad
g(t)=2t^3+\frac1{10}t.
$$

These functions satisfy the supplied error bounds. Multiplying gives

$$
\frac{f(t)g(t)}{t^3}
=\frac18+\frac{501}{200}t^2+\frac1{10}t^4.
$$

All coefficients are nonnegative, so this expression is increasing for
positive $t$. Its maximum on our interval is attained at $t=3/10$, where
it is $17563/50000$. It exceeds the target by $63/50000$.
Thus the input certificates cannot guarantee the requested estimate for
every compatible pair of functions. This conclusion follows from a concrete
witness, not merely from the failure of the theorem's sufficient test.

## A particular pair can still meet the target

The exact polynomials $f=P$ and $g=Q$ also satisfy the same supplied
certificates, since their errors are zero. For that pair,

$$
\frac{|f(t)g(t)|}{t^3}=\frac52t^2\leq\frac9{40}<\frac7{20}.
$$

So the certificates leave room for both outcomes. To settle the requested
estimate for particular functions, one needs more information about those
functions. The worked example shows the difference between a failed
sufficient test, a counterexample to a uniform guarantee, and a successful
bound for one pair.

## Check the arithmetic

From a clone of this repository, run the self-contained standard-library
checker:

```sh
python3 computations/check_enclosure_product_use.py
```

It checks the three budget terms, expands the witness product, checks the
endpoint maximum and the exact-polynomial pair, and compares the recursive
tail formula with an independent double sum in 11,200 finite cases.
Those cases test the implementation; they are not a proof of the general
identity. The interval conclusion above uses ordinary algebra, rather than
sampling points in the interval.

The source inspection for this note used the pinned public files listed in
the source record. The exported theorem file contains a `sorry` placeholder;
the separate solution file supplies the proof being discussed. This release
does not replay that proof in Lean, claim a new theorem, or establish that
this explanation improves a reader's performance.

If you try it, a useful response is the step where you could or could not
distinguish those three conclusions. Send it through the existing
[research-progress form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml),
with a link to the edition you used.
