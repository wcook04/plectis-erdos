# Erdős 1041: the phase-Sturm reduction is degree-uniform

Date: 2026-08-30.  Checker:
`scripts/check_erdos1041_all_degree_phase_sturm.py`.  This note extracts the
degree-free content of `PhiConvexitySturmBound.md` and combines it with the
all-degree terminal normalizer in `QuinticChamberWallReduction.md`.  It is a
model-metric reduction, not a proof of the wall inequality or of Erdős 1041.

## 1. Setting and theorem

Let `n >= 2` and let

```text
F(x) = (1+x)^n + R(x),        deg R <= n-2,
F(0)=F'(0)=0,
```

where `0` is a simple critical point.  (The harmless constant convention in
the low-mode model is absorbed into `R`.)  Fix a phase `phi` for which the two
inverse arms born at `0` continue without meeting another critical point:

```text
F(x_a(s,phi)) = exp(-i phi) s,       s > 0,       a in {+,-}.
```

Write

```text
omega = F/F',       Phi = omega' = 1 - F F''/(F')^2,
e_a = lim_{S->infinity} [ int_0^S |x_a'(s)| ds - |1+x_a(S)| ],
E = e_+ + e_-,
sigma_a = int_{Gamma_a} (|Phi|-1/n)|dx|,
K = sum_a int_{Gamma_a} (n^2 |Phi|^2-1)|dx|.
```

The low-mode blow-ups of `QuinticStarKernelMechanics.md` have exactly this
form: their correction has degree at most `floor((n-1)/2) <= n-2`.

> **All-degree phase-Sturm theorem.**  On every open phase interval on which
> the two arms continue,
>
> ```text
> (A)  n^2 E_{phiphi} = E + K;
> (B)  n sigma_a + e_a >= 0                         (each arm);
> (C)  E_{phiphi} + E/n^2 >= 0.
> ```
>
> Consequently, if `[alpha,beta]` is a closed continuation arc of length
> `D < n pi`, then
>
> ```text
> E(phi) <= [ sin((beta-phi)/n) E(alpha)
>            + sin((phi-alpha)/n) E(beta) ] / sin(D/n).       (S)
> ```
>
> In particular, whenever there is a nonzero foreign critical-value gap,
> every trace-max allowed phase arc has `D <= pi < n pi`, and endpoint
> nonpositivity implies `E <= max(E(alpha),E(beta)) <= 0` throughout the arc.
> The no-foreign-gap monomial case has no wall and is elementary separately.

Thus the phase-interior part of the low-mode model metric problem is absent
at **every degree**.  For fixed coefficient data it is enough to prove the
pair-excess inequality at the boundary phases, where a foreign critical
value lies on the supporting line, together with any genuine degenerate-hub
strata.

## 2. Exact arm calculus

Put `q=exp(-i phi)s`, `y=x_s`, and `rho=|y|`.  Implicit differentiation gives

```text
y = exp(-i phi)/F'(x),       x_phi = -i omega = -i s y,
y_phi/y = -i Phi.
```

Since `omega=s y`, differentiation in `s` gives

```text
s y_s = (Phi-1)y,       s rho_s = (Re Phi-1)rho.
```

Writing `Phi=p+i q_1`, one further phase derivative yields

```text
rho_phiphi = rho(q_1^2-s p_s)
            = rho |Phi|^2 - d/ds [s rho Re Phi].              (1)
```

The second equality is exact: differentiate the bracket and use
`s rho_s=(p-1)rho`.  Hence the truncated length `L_S=int_0^S rho ds`
satisfies

```text
(L_S)_{phiphi}
  = int_0^S |Phi|^2 |dx| - |omega(S)| Re Phi(S).              (2)
```

The lower endpoint contributes zero because `omega -> 0` at the simple
critical hub.

## 3. Terminal passage and identity (A)

The degree gap `deg R <= n-2` gives, uniformly on compact coefficient and
phase sets inside a continuation chamber,

```text
n omega(x) = 1+x+O(1/x),       Phi(x)=1/n+O(1/x^2),
|1+x(S)| = S^(1/n)+O(S^(-1/n)).                              (3)
```

The same expansions after phase differentiation give
`d_phi^2 |1+x(S)| -> 0`.  If `r_S=|1+x(S)|`, then (3) also gives

```text
r_S - n^2[ |omega(S)| Re Phi(S) + (r_S)_{phiphi} ] -> 0.      (4)
```

For the truncated quantities

```text
E_S=L_S-r_S,       K_S=int_0^S (n^2|Phi|^2-1)|dx|,
```

(2) has the exact rearrangement

```text
n^2(E_S)_{phiphi}-E_S-K_S
 = r_S-n^2[|omega(S)| Re Phi(S)+(r_S)_{phiphi}].              (5)
```

The right side tends to zero by (4).  The integrands defining the excess
and `K` are integrable at infinity by (3), and the expansions are locally
uniform, so phase differentiation passes through the limit on compact
subarcs.  Taking `S->infinity` in (5) proves (A).  This is the same tail
interchange used in the quintic theorem, now with `5` replaced by `n`.

## 4. Total variation and the signed integrated budget

Along one arm, `d omega = Phi dx`, so

```text
int_{Gamma_a[0,S]} |Phi||dx| = TV(omega[0,S]) >= |omega(S)|.
```

Therefore

```text
n sigma_a(S)+e_a(S)
 = n int |Phi||dx| - |1+x(S)|
 >= n|omega(S)|-|1+x(S)| -> 0,                               (6)
```

which proves (B).  Pointwise positivity is neither asserted nor needed:

```text
n^2|Phi|^2-1 = (n|Phi|-1)^2 + 2(n|Phi|-1).
```

After integration, `K >= 2n sum_a sigma_a >= -2E`.  Identity (A) now
gives `n^2E_{phiphi}=E+K >= -E`, which is (C).

## 5. Sturm endpoint domination

Let `h` be the solution of `h''+h/n^2=0` taking the endpoint values of
`E`; it is the right side of (S).  Then `v=E-h` has zero endpoints and
`v''+v/n^2>=0`.  On any component where `v_+` is positive, integration
against `v_+` and the Dirichlet Poincaré inequality give

```text
0 <= -int |v_+'|^2 + (1/n^2)int v_+^2
   <= [1/n^2-(pi/D)^2] int v_+^2 < 0,
```

a contradiction.  Thus `v<=0`, proving (S).

For `0<=phi-alpha<=D<=pi` and `n>=2`, the two sine weights are positive
and their sum is

```text
cos((D-2(phi-alpha))/(2n)) / cos(D/(2n)) >= 1.
```

Hence, when both endpoint values are nonpositive, the sine interpolant is
at most their maximum.  When at least one foreign gap is nonzero, a
trace-max allowed arc is an intersection of closed semicircles
`Re(exp(i phi) g_j)>=0`; every nontrivial connected component therefore
has length at most `pi`, and its endpoints are wall phases.

## 6. Exact boundary of the result

This theorem removes phase interiors only.  It does **not** prove any of:

- the boundary/wall inequality `E<=0`;
- a uniform choice of two arms through coefficient-wall collisions;
- transfer from the low-mode model to an actual polynomial away from an
  already controlled perturbative regime;
- the unrestricted all-degree Erdős 1041 assertion.

The surviving metric producer is now more sharply localized: prove the
pair-excess sign on coefficient/critical-value walls (and degenerate hub
strata).  The quintic compact double-tight atlas is one degree-five
instance of exactly that boundary problem.

## 7. Replay

```bash
python3 research_corpus/Erdos1041/scripts/check_erdos1041_all_degree_phase_sturm.py
```

The checker verifies the exact local differential identity, the truncated
boundary rearrangement, the square completion, the sine-weight identity,
and the required terminal asymptotics for explicit rational low-mode
polynomials in every degree `3<=n<=12`.
