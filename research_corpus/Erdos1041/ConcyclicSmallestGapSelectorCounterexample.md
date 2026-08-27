# Erdős #1041: the smallest-gap Form-A selector is false

Status, 2026-08-25: complete exact counterexample, symbolic rational checker,
and Lean-checked algebraic core. This refutes the deterministic rule “choose
the smallest angular gap and optimize only its common radius.” It does **not**
refute Form A-cut, the concyclic case, or Erdős #1041.

## 1. The selector

For distinct unit points `w_0,...,w_4`, let

```text
g(z) = product_j (z-w_j).
```

The smallest-gap selector chooses the adjacent pair with least angular
separation, then searches common radii `s` for which both outer spoke pieces
and the chord `[s w_i,s w_(i+1)]` lie in `{|g|<=1}`. This is attractive because
the previous exact counterexample to concentric alternation was rescued by its
smallest gap with substantial slack.

The rule is false.

## 2. Exact pentagon

Take the unit points obtained from the rational half-angle parameters

```text
q = (1/1200, 8/11, 40/13, -83/27, -8/11),
w(q) = ((1-q^2)+2qi)/(1+q^2).
```

Thus

```text
w_0 = 1439999/1440001 + (2400/1440001)i,
w_1 = 57/185 + (176/185)i,
w_2 = -1431/1769 + (1040/1769)i,
w_3 = -3080/3809 - (2241/3809)i,
w_4 = 57/185 - (176/185)i.
```

All five squared moduli equal one. Every consecutive cross product is
positive, so the displayed cyclic gaps lie in `(0,pi)`. Exact squared chord
comparisons give

```text
|w_3-w_4|^2 = 971618/704665 = 1.3788367522...,
```

and the other adjacent squared chords exceed it respectively by

```text
0.0017767185, 0.0010358281, 0.0047183962, 0.0081190564.
```

Because `2 sin(delta/2)` is strictly increasing for `0<delta<pi`, the
`w_3,w_4` gap is uniquely smallest.

## 3. Radius zero is inadmissible

The selected pair cannot use the degenerate radius `s=0`. On the full spoke to
`w_4`, the exact waypoint `w_4/10` satisfies

```text
|g(w_4/10)|^2 - 1
 = 148116977372167593862092797
   / 517567344770831203690000000000
 > 0.
```

Thus the outer arm `[0,w_4]` leaves the unit sublevel.

## 4. Every positive radius has an unsafe chord

Let

```text
m = (w_3+w_4)/2
  = -352687/1409330 - (1084969/1409330)i.
```

Exact expansion gives

```text
|g(sm)|^2 - 1 = s * (961/D) * A(s),
D = 2620148092600599198725979487928148264500000,
```

where `A` has degree nine. The apparent mixed signs in its power basis conceal
the decisive structure: after degree elevation to the degree-ten Bernstein
basis,

```text
1260 A(s) = sum_(k=0)^10 c_k binom(10,k) s^k (1-s)^(10-k),
```

and every integer `c_k` is strictly positive. The smallest coefficient is

```text
c_3 = 27757623193676369552937738274125305640 > 0.
```

Consequently `A(s)>0` for `0<s<=1`, hence

```text
|g(sm)| > 1                         for every 0<s<=1.
```

The point `sm` is the midpoint of `[s w_3,s w_4]`, so the selected chord is
unsafe at every positive common radius. Combined with the unsafe full spoke at
`s=0`, no common radius works for the uniquely smallest gap.

## 5. Boundary and lesson

This is a selector counterexample, not a Form-A counterexample. Another
adjacent pair may still work. The theorem shows that angular crowding alone is
not the missing selection law, even arbitrarily near the regular pentagon. A
proof of Form A must use potential/spoke information jointly with gap geometry;
neither the prescribed-radius regular comparator nor the smallest gap encodes
enough of the configuration.

## Verification

The checker uses `Fraction` and SymPy exact arithmetic to verify the unit-circle
identities, cyclic order, chord comparisons, unsafe spoke waypoint, product
factorization, Bernstein conversion, and positivity of every coefficient.
Lean checks the same rational core and proves the uniform real statement for
all `0<s<=1`.

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_smallest_gap_selector_counterexample.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample
```
