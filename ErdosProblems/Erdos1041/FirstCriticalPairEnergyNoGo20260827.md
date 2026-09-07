# Erdős 1041: exact cubic no-go for the first-critical pair-energy cone

Status, 2026-08-27: exact Gaussian-rational counterexample with a deterministic
Rouché/root-location certificate. This refutes one returned pointwise producer;
it does **not** refute the descending inverse-branch route or Erdős 1041.

## 1. The returned producer

At a simple minimum-modulus critical point `c`, put `v=p(c)` and choose the two
local inverse branches by

```text
p(z_+(s)) = p(z_-(s)) = v(1-s^2),
z_+(0)=z_-(0)=c.
```

The return defines

```text
M=(z_++z_-)/2,  D=(z_+-z_-)/2,  E=|M|^2+|D|^2
```

and proposes

```text
E' >= 0,
E'^2 >= 4(E-|c|^2)(|M'|^2+|D'|^2).                 (PEC)
```

The second inequality is false even for a cubic with all roots strictly inside
the unit disk.

## 2. Exact polynomial

Work in local coordinates `w=z-c` and set

```text
c = -1/2 - i/100,
a = -1/16 - 5i/6,
v = -1/32 + i/160,
p(c+w) = v + a w^2 + w^3.                            (1)
```

This is a monic cubic. Its critical points are exactly

```text
c,
d = c-2a/3 = -11/24 + 491i/900.
```

Their squared critical-value moduli are

```text
|p(c)|^2 = 13/12800,
|p(d)|^2 = 116200133809/13931406950400,
```

and the first is strictly smaller. Thus `c` is the unique
minimum-modulus critical point required by the returned lemma.

## 3. Exact open-unit-disk root certificate

Take radius `R=1/1000` and the Gaussian-rational centres

```text
q_1 = -313839/500000 -  68713 i/500000,
q_2 =  -19283/40000  + 415143 i/500000,
q_3 = -327747/1000000 + 110473 i/1000000.
```

For each centre the checker verifies, entirely in rational arithmetic,

```text
|p'(q_j)| R
  > |p(q_j)| + |p''(q_j)| R^2/2 + R^3.               (2)
```

It uses the conservative exact bounds

```text
max(|Re x|,|Im x|) <= |x| <= |Re x|+|Im x|.
```

On the circle `|z-q_j|=R`, (2) lets Rouché compare `p` with its linear
Taylor term, so each disk contains exactly one root. The three disks are
pairwise disjoint and satisfy `|q_j|+R<1`. Since the polynomial is cubic, all
three roots lie in the open unit disk.

## 4. The local obstruction

The two inverse branches have convergent expansions

```text
z_+(s)-c =  kappa s + lambda s^2 + O(s^3),
z_-(s)-c = -kappa s + lambda s^2 + O(s^3),
kappa^2 = -v/a,
lambda  =  v/(2a^2).
```

Write

```text
K = |kappa|^2 = |v/a|,
C = 2 Re(conj(c) lambda) = Re(conj(c) v/a^2),
A = K+C.
```

For (1), exact Gaussian-rational simplification gives

```text
K^2 = 117/80450,
C   = -7368462/323610125.
```

The checker proves `K^2>C^2`; since `C<0`, this is exactly

```text
0 < A=K+C < K.                                       (3)
```

Branch symmetry makes `M` even and `D` odd, hence

```text
E-|c|^2 = A s^2 + O(s^4),
E'       = 2A s + O(s^3),
|M'|^2+|D'|^2 = K + O(s^2).
```

Therefore the difference between the two sides of `(PEC)` is

```text
E'^2 - 4(E-|c|^2)(|M'|^2+|D'|^2)
  = 4A(A-K)s^2 + O(s^4)
  = 4AC s^2 + O(s^4) < 0
```

for every sufficiently small positive `s`. This exactly refutes `(PEC)`.
Notice that `A>0`, so the returned monotonicity `E'>=0` survives locally on
this witness; it is the reverse-Cauchy cone inequality that fails.

## 5. Consequence

The return's conditional length derivation after `(PEC)` is algebraically
correct, but its producer is unavailable. Numerical tests that sampled away
from the critical endpoint can miss this failure because the negative term is
quadratic in `s`.

The canonical descending branch pair remains an admissible curve, and the
source-current global route remains to bound some such pair by another
mechanism (combined charge, COVER, or an exact equivalent). The declared Erdős
1041 target is unchanged and open.

## 6. Exact replay and evidence boundary

The finite certificate is reproducible from the repository root:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_first_critical_pair_energy_no_go.py
```

The terminal result is `status=exact_first_critical_pair_energy_no_go_verified`.
In exact rational arithmetic it records the three Rouché margins for the
radius `1/1000` root disks, the strict critical-value ordering
`13/12800 < 116200133809/13931406950400`, and
`C < 0`, `K > -C`, `0 < A=K+C < K`. These are the decisive finite checks
behind the local coefficient `4*A*C*s^2+O(s^4) < 0`.

This checker is an exact arithmetic certificate for the displayed witness,
not a formal proof of the asymptotic expansion and not an evaluation of the
unrestricted Erdős problem. The only retired claim is `(PEC)`. The unrestricted
problem, the descending inverse-branch route, the combined-charge and COVER
producers, and the target obligations remain open.
