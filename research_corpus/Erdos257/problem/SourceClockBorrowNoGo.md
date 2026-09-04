# Source-clock carry polynomials and an exact complementarity no-go

Status: exact deductions, 2026-08-20.  No statement below has been added to
Lean.  The note records the polynomial identity obtained from the complete
period-six defect recurrence and an all-depth Boolean counterfamily for the
rational source `1/21`.  The counterfamily is quotient-admissible and has the
stated divisor-count coefficients; it is not the actual greedy word.

## 1. The defect polynomial

Let

```text
a_n = 1 if n mod 6 is 0 or 5, and a_n = 0 otherwise,
f_b(n) = sum_(d|n) b_d,
T_N = floor(2^N/21),
Q_N = T_N - sum_(n<=N) f_b(n) 2^(N-n).
```

Thus `T_(N+1)=2T_N+a_(N+1)`, and hence

```text
Q_(N+1) = 2Q_N+a_(N+1)-f_b(N+1).                         (1)
```

For integers `N>=0` and `L>=1`, define

```text
A_(N,L)(x) = sum_(j=1..L) a_(N+j) x^(L-j),
F_(N,L)(x) = sum_(j=1..L) f_b(N+j) x^(L-j),
R_(N,L)(x) = sum_(j=0..L-1) Q_(N+j) x^(L-1-j).
```

Then (1) gives the polynomial identity

```text
Q_N x^L + A_(N,L)(x) - F_(N,L)(x) - Q_(N+L)
  = (x-2) R_(N,L)(x).                                    (2)
```

Indeed, the coefficient of `x^(L-j)` on the right is
`Q_(N+j)-2Q_(N+j-1)=a_(N+j)-f_b(N+j)`; the constant term is
`-2Q_(N+L-1)=a_(N+L)-f_b(N+L)-Q_(N+L)`.

At `x=2`, (2) is the iterated defect recurrence.  At `x=1`, it is the exact
unweighted carry law

```text
sum_(j=1..L) f_b(N+j) - sum_(j=1..L) a_(N+j)
  + Q_(N+L)-Q_N
  = sum_(j=0..L-1) Q_(N+j).                              (3)
```

Equation (3) is the literal amortised-borrow balance.  Its endpoint term
cannot be discarded.  Replacing every defect by

```text
Q_n' = Q_n + lambda 2^n
```

changes the cumulative term on the right by
`lambda 2^N(2^L-1)` and changes `Q_(N+L)-Q_N` on the left by the same
amount.  Thus the `x=1` law is exactly insensitive to the homogeneous flux.

## 2. The Boolean block and the old-divisor load

Suppose `1<=L<=N`, and write

```text
W_(N,L)(x) = sum_(j=1..L) b_(N+j) x^(L-j),
O_(N,L)(x) = sum_(j=1..L)
  (sum_(d<=N, d|(N+j)) b_d) x^(L-j).
```

Any divisor `d>N` of `N+j<=N+L<=2N` is equal to `N+j`.  Consequently

```text
F_(N,L)(x) = W_(N,L)(x)+O_(N,L)(x).                       (4)
```

Combining (2) and (4) gives two exact views of the same Boolean block:

```text
W_(N,L)(2)
  = 2^L Q_N + A_(N,L)(2)-O_(N,L)(2)-Q_(N+L),             (5)

W_(N,L)(1)
  = A_(N,L)(1)-O_(N,L)(1)+Q_N-Q_(N+L)
      +sum_(j=0..L-1) Q_(N+j).                           (6)
```

Here `W(2)` is the binary numeral of the next Boolean block, whereas `W(1)`
is its Hamming weight.  For `L=6`, `A_(N,6)(1)=2` and
`A_(N,6)(2)=3(2^N mod 21)`.  Equation (5) is therefore the existing six-step
repair-load recurrence after separating the six self-pulses from the older
divisor pulses.  Equation (6) is its exact digit-sum companion.

This exposes the obstruction to a linear digit-sum proof.  The passage from
the weighted load in (5) to the Hamming weight in (6) introduces the
cumulative defect, but the combination

```text
Q_N-Q_(N+L)+sum_(j=0..L-1)Q_(N+j)
```

annihilates every homogeneous orbit `lambda 2^n`.  An additional inequality
must therefore use the actual greedy decision; neither endpoint evaluation
of the block polynomial detects positive flux.

## 3. An all-depth counterfamily with the exact `1/21` source

For `M>=6`, let

```text
b_n^(M) = 1 if n>=M, and b_n^(M)=0 otherwise.
```

This is a Boolean support, so `f_M(n)=sum_(d|n)b_d^(M)` has Boolean Mobius
inverse.  Its complete Lambert value satisfies

```text
sum_(n>=1) f_M(n)2^-n
  = sum_(d>=M) 1/(2^d-1)
  <= (64/63) sum_(d>=M)2^-d
  <= 2/63.                                                (7)
```

Let `Q_N^(M)` be the defect defined above using the period-six digits of
`1/21`.  For `N>=6`,

```text
T_N/2^N > 1/21-2^-N
          >= 1/21-1/64
          = 43/1344
          > 2/63.
```

The coefficient prefix is at most the complete series in (7), so
`Q_N^(M)>0` for every `N>=6`.  For `N<6` its coefficient prefix is zero and
`Q_N^(M)=T_N>=0`.  Hence this cofinite Boolean word is quotient-admissible at
every depth for the exact rational source `1/21`.  Absolute convergence also
gives

```text
lim_(N to infinity) Q_N^(M)/2^N
  = 1/21-sum_(d>=M)1/(2^d-1) >= 1/63 > 0.                (8)
```

It also violates the proposed delayed-doubling density inequality.  At
`K=2M-1`,

```text
B_M(K)=M,
B_M(floor(K/2))=B_M(M-1)=0,
M > floor((2M-1)/3)+2                                    (9)
```

because `M>=6`.  The first member, `M=6`, has support
`{6,7,8,...}`.  Through rank `11`, one has

```text
Q_N = floor(2^N/21)-(2^(N-5)-1)  (6<=N<=11),
Q_11 = 97-63 = 34,
```

while all six ranks `6,...,11` are selected.

The counterfamily is not the actual greedy orbit.  Ranks `1,...,4` are
unaffordable from `1/21`, but at rank `5` the residual is still `1/21` and

```text
1/(2^5-1)=1/31 < 1/21.
```

The actual greedy word must therefore select rank `5`, whereas every
`b^(M)` with `M>=6` skips it.

## 4. What the polynomial identities cannot imply

Equations (2)--(6) use the period-six source, every divisor-count coefficient,
the six self-pulses, and every intermediate defect in the block.  The family
in Section 3 also satisfies Boolean Mobius inversion and nonnegative defect at
every depth, yet it has an all-selected tail and violates the delayed-doubling
density bound.  Therefore those hypotheses do not imply the density bound.

The missing input is not another evaluation of the carry polynomial.  It is
a quantitative use of the actual greedy comparison

```text
b_n=1 iff 1/(2^n-1) is at most the real residual before rank n.
```

In particular, an amortised-borrow argument must charge a quotient-admissible
word for skipped affordable ranks such as `5`.  Without such a
complementarity charge, the endpoint defect absorbs the complete period and
divisor load while the positive homogeneous mode remains legal.
