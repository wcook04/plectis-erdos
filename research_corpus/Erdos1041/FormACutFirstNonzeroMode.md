# Erdős #1041: every first Fourier mode supplies two safe model spokes

Status: exact all-mode theorem for the homogeneous near-Fekete model, an
ordinary proof of its phase count, a Lean-checked analytic and arithmetic core,
and a fail-closed finite audit. 2026-08-25. **This is not the unrestricted
solution of Erdős #1041.** It closes the `E_1 = 0` hole in the leading model;
the uniform remainder and the regime away from the regular polygon remain open.

## 1. The hole

[FormACutAdjacentSelector.md](FormACutAdjacentSelector.md) uses

```text
log|f(z)| = Re E_0 + Re(E_1 z) - Re(z^n) + R
```

and calls a root ray good when `Re(E_1 omega^j) <= 0`.  Its adjacent-pair proof
used strict negativity on the part of the chord where `Re(z^n) < 0`.  When
`E_1 = 0`, every displayed linear term is zero, so that proof does not apply.
Calling every ray good does not repair the strict implication.

The correct coordinate is the **first nonzero mode**, not always mode one.

## 2. Exact homogeneous model

Fix `n > m >= 1`, `A in C`, and

```text
H(z) = Re(A z^m - z^n),       omega = exp(2 pi i/n).
```

On the `j`-th root ray, `z=t omega^j`, the identity `omega^(nj)=1` gives

```text
H(t omega^j) = t^m Re(A omega^(mj)) - t^n.                 (M)
```

Hence any index satisfying `Re(A omega^(mj)) <= 0` carries an entire strict
model spoke:

```text
H(t omega^j) < 0                    for every t > 0.
```

No adjacent chord and no optimization are needed in the first-mode model: two
such rays give the origin two-spoke path directly.

## 3. There are always two rays, exactly from degree four

Put

```text
d = gcd(n,m),       q = n/d.
```

As `j` runs through `0,...,n-1`, the phases `omega^(mj)` are precisely the
`q`-th roots of unity, each repeated `d` times.  Any closed half-plane through
the origin contains at least `floor(q/2)` of the `q` equally spaced points.
Therefore

```text
#{j : Re(A omega^(mj)) <= 0} >= d floor(q/2).              (C)
```

For `n >= 4` this lower bound is at least two.  Indeed:

* if `q >= 4`, then `floor(q/2) >= 2`;
* if `q = 2` or `q = 3`, the factorization `n=dq >= 4` forces `d >= 2`.

At `n=3`, `m=1` and a generic phase, a closed half-plane can contain only one
of the three phases.  Thus the degree threshold is sharp and agrees with the
independent cubic theorem already in the corpus.

Combining (M) and (C) proves:

> **Theorem (first-nonzero-mode two-spoke theorem).** Let `n >= 4`,
> `1 <= m < n`, and `A in C`.  In the homogeneous model
> `H(z)=Re(Az^m-z^n)`, two distinct `n`-th-root directions carry complete
> spokes contained in `{H <= 0}`, strictly away from the origin.

This includes `A=0`: then every ray has `H(t omega^j)=-t^n<0`.  In particular,
the theorem does not divide by `|E_m|` and remains valid on further-degenerate
strata.

## 4. Why this is the right repair near Fekete

For roots `a_k=omega^k(1+e_k)`, the expansion used by the adjacent-selector
note is

```text
log|f(z)| = Re E_0 + sum_{r>=1} Re(E_r z^r) - Re(z^n) + higher order.
```

If `E_1=...=E_{m-1}=0` and `E_m != 0`, the scale
`|z| asymp |E_m|^(1/(n-m))` makes `Re(E_m z^m)` and `-Re(z^n)` comparable.
After rescaling, their exact leading model is the `H` above.  The theorem
selects two root directions at **every** first mode `m`; the mode-one
half-plane is not a special source of supply.

For tangent perturbations of the unit-circle equality family, Fourier modes
pair as `m` and `n-m`.  The smaller exponent dominates unless `n` is even and
`m=n/2`.  In that Nyquist case the pure alternating angular family factors
exactly as

```text
(z^(n/2)-e^(i n delta/2))(z^(n/2)+e^(-i n delta/2)),
```

and on every root ray its modulus is at most
`(1-t^(n/2))(1+t^(n/2))=1-t^n`; all spokes are safe.  Thus the mode count has
the correct behavior on the sole self-paired tangent frequency as well.

## 5. Exact boundary

What is now proved:

* the earlier `E_1=0` inference was invalid and is corrected at its source;
* every possible first Fourier mode has two safe spokes in the exact
  homogeneous model for every `n>=4`;
* degree three is the unique degree where the phase count can supply only one;
* the analytic ray inequality and the arithmetic lower bound are Lean-checked
  in [FormACutFirstNonzeroMode.lean](FormACutFirstNonzeroMode.lean).

What is not proved:

* a uniform bound absorbing all higher modes and the remainder on the entire
  spoke, with an explicit neighborhood of the regular polygon;
* any statement for configurations bounded away from that neighborhood;
* the unrestricted Erdős #1041 conclusion.

The next analytic step is no longer a selector problem.  It is a stratified
remainder estimate: at the first nonzero mode, use the strict model margin on
the two selected rays near the origin, the fixed negative baseline
`log|1-z^n|` away from the origin, and compactness between the two ranges.

## 6. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_form_a_cut_first_nonzero_mode.py
```

The checker enumerates all mode quotients through degree 80, audits every
half-plane event and intervening phase cell, verifies (M) on a deterministic
grid, and includes `n=3,m=1` as the required negative control.

