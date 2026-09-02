# Erdős #1041: the sharp elementary-symmetric tail hierarchy

Status: analytic theorem proved on 2026-08-24.  The sharp five-tail second
layer, its complex squared-norm specialization, and the exact primitive
quintic certificate are formalized in
`TetranomialElementarySymmetricSelector.lean`; canonical cached validation is
complete: the exact target passed on 2026-08-24.  This strictly enlarges the
proved tetranomial classes.  It is not an unrestricted solution of Erdős
#1041.

## Headline theorem

Let `x_1,...,x_m` be nonnegative.  If at most one `x_i` is below one, then
the `m-1` large entries alone give, for every `1<=k<=m-1`,

```text
e_k(x) >= binom(m-1,k).                                (ESH0)
```

Thus a strict reverse inequality forces two entries below one with no
resultant or product hypothesis.  There is also a sharp product bonus.  Let

```text
P = product_i x_i <= 1,
```

and write `e_k(x)` for their `k`th elementary symmetric polynomial.  Then

```text
e_k(x) >= binom(m-1,k) + P binom(m-1,k-1).             (ESH)
```

The bound is sharp: equality is attained by `(P,1,...,1)`.  Consequently,
for any one value of `k`, the strict reverse inequality forces two distinct
entries below one.

The original `m-1` L2 theorem is `(ESH0)` at `k=1`, and the tail-resultant
bonus is `(ESH)` at `k=1`.  The two formulas supply every higher
elementary-symmetric layer at once; these layers contain information that the
total energy and total product discard.

## Proof by monotone compression

Choose the possible exceptional entry `0<=y<=1` and one of the remaining
entries `z>=1`.  Replace the pair `(y,z)` by `(yz,1)`, leaving the other
variables `R` unchanged.  Because the full product is at most one and every
unabsorbed entry is at least one, every intermediate value of `y` stays at
most one.  The elementary-symmetric decomposition gives the exact drop

```text
e_k(y,z,R)-e_k(yz,1,R)
  = (y+z-yz-1)e_(k-1)(R)
  = (1-y)(z-1)e_(k-1)(R) >= 0.                         (1)
```

Absorb all `m-1` large entries.  The terminal vector is
`(P,1,...,1)`, and counting the terms that do or do not use `P` gives the
right side of (ESH).  This also proves sharpness and shows that no larger
threshold can follow from `m,k,P` alone.

For five entries and `k=2`, the selector is

```text
sum_(i<j) x_i x_j < 6       ==>  two x_i are below one, (2a)
sum_(i<j) x_i x_j < 6 + 4P  ==>  two x_i are below one. (2)
```

The first implication is unconditional; the second uses `P<=1` and is sharp
for fixed `P`.

The Lean module checks (1) at `k=2`, the four-step compression to
`(P,1,1,1,1)`, the ten-pair conclusion, and its specialization to five
complex squared norms.

## Tetranomial consequence

For

```text
g(w)=w^m+a w^r+b w^s+c,             m>r>s>=1,
t_i=c+b w_i^s,
x_i=|t_i|^2,
```

the Abel identity in `CyclicTetranomialCoefficientCase.md` says that every
root with `x_i<1` has a complete origin spoke in `{|g|<1}`.  Hence (ESH), at
any layer `k`, is a sufficient condition for two safe spokes and a broken
root-to-root path of length below two.  The product is still the explicit
tail resultant from `TetranomialTailProductSelector.md`; the new input is a
higher elementary-symmetric tail energy.

For a quintic the new pair energy is

```text
E_2 = sum_(i<j) |(c+bw_i)(c+bw_j)|^2.
```

Thus `E_2<6` settles the primitive sparse pattern `w^5+a w^4+bw+c` without
any resultant condition.  When `P<=1`, the larger threshold `6+4P` settles
still more cases.  Both work even when total tail energy lies above the sharp
first-layer threshold.

## Exact strict-extension witness

Put

```text
r=63/64,       u=41/100,       q=r^4,
g(z)=(z-u)(z^4+q)=z^5-u z^4+qz-uq.                    (3)
```

The five roots are `u` and the four numbers `r exp((2j+1)pi i/4)`.  They are
all strictly inside the unit disk, and (3) has the primitive exponent pattern
`(5,4,1)`.  Its Abel tails are `q(w-u)`.  Their squared norms are

```text
0, A, A, B, B,
A=q^2(r^2+u^2-sqrt(2)ru),
B=q^2(r^2+u^2+sqrt(2)ru).
```

The irrational terms cancel from both symmetric energies:

```text
E_1 = 2A+2B = 4q^2(r^2+u^2) > 4,
E_2 = A^2+B^2+4AB
    = q^4(6r^4+8r^2u^2+6u^4) < 6.                   (4)
```

Since `P=0`, the old sharp resultant threshold is `E_1<4` and therefore
fails, whereas the product-free new layer (2a) proves two safe tails.  This example also
lies beyond the other current certificates:

```text
q(1+u)>1,
min_(i!=j)|w_i-w_j|^2 > 5/9.                          (5)
```

For (5), quartic-fibre pairs have squared distance at least `2r^2`; the
closest pair involving `u` has squared distance
`r^2+u^2-sqrt(2)ru`.  The rational comparison `sqrt(2)<10/7` puts this
strictly above `5/9`.  Thus the coefficient `L1` selector and the refined
quintic close-pair certificate both fail.  The reciprocal-moment selector is
unavailable because `s=1`.  The Lean certificate checks every rational
inequality in (4)--(5), the pair-energy identity, and the square-root bound.

The factorization itself makes the two safe tails visible, but that is a
feature: it gives an exact, transparent witness that the new symmetric layer
occupies territory not covered by the previous selector bundle.

## Computation and the primitive survivor

The broader coefficient search that produced the first primitive survivor

```text
a=-0.10282689199401228-0.39533409823728954 i,
b= 0.5960303942777737 -0.3528626561472372 i,
c=-0.4461873563364148 -0.5382330830607761 i
```

gave tail squared norms approximately

```text
0.0228765, 0.383782, 0.407396, 1.658212, 1.684672.
```

Its first-layer data are `E_1=4.156938...` and `P=0.00999185...`, so
`E_1<4+P` fails.  The new pair energy is `E_2=5.689282...`, while
`6+4P=6.039967...`; already the product-free threshold `6` certifies it with
margin about `0.31072`, while the sharp product bonus increases the margin to
about `0.35068`.
This computation selected the right invariant.  The proof of (ESH), not the
floating-point sample, is authority.

The next coefficient bridge is already exact.  For the primitive pattern put

```text
S=sum_i w_i=-a,              Q=sum_i |w_i|^2,
U=sum_(i<j)|w_i|^2|w_j|^2,  M=sum_i |w_i|^2 w_i.
```

Using `e_2(w)=0`, direct expansion of the ten pair tails gives

```text
E_2 = 10|c|^4 + |bc|^2(3Q+|S|^2) + |b|^4 U
      + 8 Re(|c|^2 b conjugate(c) S)
      + 2 Re(|b|^2 b conjugate(c) (SQ-M)).              (6)
```

Indeed, the required pair identities are
`sum_(i<j)|w_i+w_j|^2=3Q+|S|^2` and
`sum_(i<j) conjugate(w_i+w_j)w_iw_j=SQ-M`; the nominal
`c^2 b^2` cross term vanishes with `e_2(w)`.  On the primitive survivor the
last two phase-sensitive terms are approximately `-0.76986` and `-0.82351`.
That is the information the absolute-value total-energy majorants erased.

## Boundary and downstream handoff

The selector hierarchy is complete as a finite extremal statement: every
threshold is sharp for fixed `m,k,P`.  What remains for unrestricted
tetranomials is to bound the three radial statistics in (6), while retaining
the two favourable signed correlations, from Schur stability and the missing
middle coefficients.  That is now a concrete analytic target rather than an
unspecified request for a sharper energy estimate.

The hierarchy is not claimed to be exhaustive.  A constrained adversarial
primitive-quintic replay with `P<=1` found tail energies

```text
0.201932, 0.322603, 0.634206, 4.798534, 5.041165.
```

There are three safe tails, but every sharp layer `k=1,2,3,4` lies on the
wrong side of (ESH); at `k=2` the defect is about `25.992`.  This is a useful
boundary, not a failure of the theorem: squared-modulus symmetric data alone
do not characterize the existence of two safe tails.  A complete primitive
proof must eventually use relations among the complex tail phases or a
different path mechanism.

The Refinery should place (ESH) after the tail-resultant theorem, explicitly
identify the latter as the `k=1` layer, retain (3) as the strict-extension
witness, and preserve both the unrestricted-open boundary and the explicit
non-exhaustiveness probe.
