# Erdős 68: prime-pole survival inside the lower cylinder

## Claim boundary

The finite prime-pole numerator formula is kernel-checked in
`PrimePoleCriterion.lean`. A local exact scan
through prime 3000 reproduces the two returned cancellation witnesses. Neither
result proves a cofinal lower-cylinder escape, and Erdős #68 remains open.

## Exact finite theorem

For prime `q`, endpoint `M`, and the largest positive exponent

```text
e = max_{2≤n≤M} v_q(n!−1),
```

write `L_M = lcm_{2≤n≤M}(n!−1)` and

```text
B_M = Σ_{2≤n≤M} L_M/(n!−1).
```

At every maximal hit write `n!−1=q^e u_n`. Define

```text
C_(q,M) = Σ_(v_q(n!−1)=e) u_n⁻¹  (mod q).
```

The Lean theorem states

```text
B_M ≡ (L_M/q^e) C_(q,M)  (mod q).
```

The LCM cofactor is nonzero mod `q`. Hence the theorem certifies that the complete `q^e` visible in the literal
denominators survives common-denominator reduction exactly when
`C_(q,M) ≠ 0`. This is the finite legitimate use of the prime: no value is
assigned to the infinite real tail.

## Endpoint cancellations

Wilson supplies the endpoint hit `n=q−2` at `M=q−1`, but that hit need not
survive reduction because all maximal hits contribute.

The exact scanner through `q≤3000` finds only:

| `q` | maximal hits | lifted cofactors mod `q` | inverse sum |
|---:|---|---|---:|
| 139 | 69, 122, 137 | 6, 49, 73 | `116+122+40=0` |
| 2593 | 349, 2243, 2591 | 1508, 1566, 1678 | `1367+356+870=0` |

The two inverse-sum equalities are present as native-decision checks in the
Lean module. The returned C++ scan
claims these remain the only cancellations through 200,000; that larger horizon
has not been locally regenerated in this wave and remains returned evidence.

## Target-facing residue

At `M=p−1`, write the scaled prefix in lowest terms as

```text
Q_p = (p−1)! P_(p−1) = a/(p^e w),  p∤w,
Δ_p = ceil(Q_p)−Q_p = u/(p^e w).
```

When `C_p≠0`, Wilson's congruence transports the principal residue to the gap:

```text
u w⁻¹ ≡ C_p  (mod p).
```

Putting `h=p^(e−1)w` and `u=h+t`, a dangerous lower-cylinder hit forces

```text
ε_p h < t ≤ (ε_p+R_p)h
```

and

```text
t w⁻¹ ≡ C_p−1 (mod p),  e=1,
t w⁻¹ ≡ C_p   (mod p),  e≥2.
```

This identifies the exact remaining mismatch problem: the prescribed residue
class must miss a short Archimedean interval. Nonvanishing of `C_p` alone is
insufficient when the cofactor `w` makes the interval contain many
representatives.

The next useful computation is therefore not another unit-carry count. It is a
joint census of `(C_p,w,t)` and the least positive representative of the
prescribed class, looking for a stable scale law that can be promoted to a
cofinal theorem.

## Replay

```sh
./repo-python formal_math/probes/erdos68_prime_pole_scan.py --max-prime 3000
```

The probe exits nonzero unless both returned cancellation witnesses, their hit
sets, and their lifted cofactors are reproduced exactly.

Focused replay: `lean_fast_build.py --jobs 2
ErdosProblems.Erdos68.PrimePoleCriterion`, exit `0` on 2026-08-24.
