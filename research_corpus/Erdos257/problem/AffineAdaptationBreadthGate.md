# Affine-adaptation breadth gate

- Script: `formal_math/erdos257_period_noncollapse/scripts/affine_lambert_adaptation_probe.py`
- Receipt: `state/formal_math/erdos257_period_noncollapse/affine_lambert_adaptation_receipt.json`
- Trigger: iteration 10's proposed search for a third semigroup adaptation, specifically
  `n -> an+b` and finite substitutions on `k`-adic chains.

## Result

Those two examples do not open a third mechanism.

Write the Lambert atom as

    K_n(x) = x^n/(1-x^n),       Y_A(x) = sum_(n in A) K_n(x).

Mahler substitution acts on the index without loss:

    K_n(x^a) = K_(an)(x).                                      (1)

That is why multiplication by a base can generate a functional equation. A
translation is different. For `b != 0`, `K_(an+b)` has poles at primitive
`(an+b)`-th roots of unity. A fixed finite tower

    K_n(x), K_n(x^a), ..., K_n(x^(a^J))

has poles only at roots whose orders divide one of `n, an, ..., a^J n`.
Choose `n` coprime to `b` and large enough that `an+b > a^J`. Then
`gcd(n,an+b)=1`, so `an+b` divides none of `a^j n`, `0 <= j <= J`.
Polynomial coefficients cannot create the missing primitive pole. Therefore no
fixed finite Mahler-tower intertwiner can turn `n` into `an+b` for all `n`.

The executable audit checks (1) exactly at `x=1/2` for `2 <= a <= 12` and
`1 <= n <= 64`. For every one of the 66 translated pairs
`2 <= a <= 12`, `1 <= b < a`, it emits an explicit cyclotomic pole-order
witness through Mahler height four. All controls and all witnesses pass.

## The sparse branch is already settled

A forward affine orbit

    u_(t+1) = a u_t + b,       a >= 2, b >= 0,

obeys `u_t >= a^t u_0`. Hence

    sum_t 1/u_t <= a/((a-1)u_0) < infinity.                    (2)

Every finite union of such orbits is reciprocal-summable. The repository's
machine-checked theorem
`irrational_erdosSupportSeries_two_of_summable_reciprocal` already proves that
its Mersenne subseries is irrational. It cannot be a new positive-density lane:
a union of `s` forward orbits has only `O(s log X)` elements through `X`.

To obtain positive density one must introduce infinitely many roots or a
finite-state rule over base-`a` digits. The former loses the finite recursive
functional equation. The latter is still using the action `x -> x^a`; if it
produces a Mahler equation for `Y_A`, it belongs to the already named base-`a`
adaptation mechanism. Calling it a substitution on `a`-adic chains does not
make the index action new.

## Mechanism decision

The specific iteration-11 examples are eliminated as distinct mechanisms:

- finite affine-orbit support: reciprocal-summable, already solved;
- translated affine action with `b != 0`: incompatible with a fixed finite
  Mahler tower at the Lambert-kernel level;
- finite `k`-adic substitution: existing base-`k` action if it yields Mahler.

This is a breadth gate, not a classification of every possible semigroup action.
An actual third adaptation would need a different operator on the Lambert kernel,
not a renamed multiplication action or a translated sparse orbit.
