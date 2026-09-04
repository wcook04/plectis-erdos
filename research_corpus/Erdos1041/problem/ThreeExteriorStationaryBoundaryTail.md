# Erdős 1041: analytic closure of the stationary `w -> 1` tail

Put

```text
u = r s w,  v = s w,
A(x) = 1+x+x^2,  D_t(x) = 1+t x+t^2 x^2,
L_t(x) = (1-x^2)/A(x)^2 + t(1-t^2 x^2)/D_t(x)^2.
```

On the ordered chart

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 31/32<=w<1,
```

the stationary surplus is strictly positive. Consequently, together with the
adjoining interval certificates, it is positive on the whole half-open prism

```text
0<=t<=1, 0<=r<=1/8, 1/4<=s<=3/8, 1/4<=w<1.
```

## Proof

Write `ell(x)=(1-x^2)/A(x)^2`. Its derivative is

```text
ell'(x) = 2(x^3-3x-1)/(1+x+x^2)^3 < 0       (0<=x<=1),
```

because `x^3<=x`. Also `ell(x)<=L_t(x)<=2`. Since

```text
u<=3/64,  v<=3/8,
```

we therefore have

```text
L_t(u) >= lu = ell(3/64) = 16740352/18464209,
L_t(v) >= lv = ell(3/8)  = 3520/9409.
```

Use the exact stationary formula replayed by the compact-block interval engine.
All three self terms are nonnegative, and the `w` self term contributes at
least

```text
w/(1-w) >= 31.
```

For each ordered pair `(a,b)`, discard its positive summand and use

```text
t a b(t b+1/2)/D_t(b) <= (3/2)ab.
```

The total ordered-pair loss is thus at most

```text
3(uv+uw+vw) <= 675/512.
```

Furthermore, with `p=uvw` and `Sigma=u+v+w`,

```text
p<=9/512,  Sigma<=91/64,
3 Sigma/(1-p) <= 2184/503,
3 t^3 Sigma p/(1-t^3 p) <= 2457/32192.
```

The positive half of the tangent correction may be discarded. In each of its
three negative quotients, the numerator is at most `4*4=16`. The denominators
are respectively at least `lv`, `lu`, and `lu+lv`. Hence its total negative
part is at most

```text
Ccorr = 8[(3/64)^2/lv + (3/8)^2/lu + 1/(lu+lv)]
      = 96467582307569032337/12803983069044654080.
```

Combining the losses gives

```text
C = Ccorr + 675/512 + 2184/503 + 2457/32192
  = 85469412147568185075271/6440403483729461002240
  < 31.
```

Therefore the stationary surplus is at least

```text
31-C
= 114183095848045105994169/6440403483729461002240
> 0.
```

The checker below replays every rational identity and comparison exactly.

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_stationary_boundary_tail.py
```

This theorem closes only the high-`w` tail of the stated `r,s` strip. It does
not cover the ordered-cone complement, prove GP3, or prove Erdős 1041.
