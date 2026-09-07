# Primitive-prime projective trapping fails for rational greedy numerators

## Status

This is an exact finite mechanism elimination from source-reachable greedy
prefixes.  It does **not** prove that any tested rational belongs to the
Mersenne achievement set, construct an infinite support, or settle Erdős 257.

The probe was selected only after two other computational directions were
rejected as saturated:

- the `4/9` selected-small-margin route already has an exact reduction and an
  empty finite census through rank `146,794`; extending that horizon would not
  distinguish a new mechanism;
- the modulus-120 seven-column repair law has already been tested on `1,557`
  unrelated certified survivors (`12,456` rows), so a new cross-target census
  would duplicate `RecordCofinitenessBoundary.md`.

The remaining fresh object named in the computational exhaustion map was the
exact residual numerator orbit.

## Exact coordinate

For a rational target `y`, let its exact greedy prefix through rank `N` leave

\[
 r_N=y-\sum_{\substack{k\le N\\b_k=1}}\frac1{2^k-1}
     =\frac{a_N}{D_N}
\]

in lowest terms.  Suppose a selected rank `k` has a primitive prime divisor
`p` of `2^k-1`.  Then `ord_p(2)=k`, so the dyadic subgroup

\[
 H_k=\langle2\rangle\subset\mathbf F_p^*
\]

has order `k`.  The map `x -> x^k` has kernel of order `k`; consequently

\[
 a_MH_k=a_NH_k\quad\Longleftrightarrow\quad
 a_M^k\equiv a_N^k\pmod p.                     \tag{1}
\]

Thus `(a_N mod p)^k` is an exact projective coordinate.  If the strong serial
correlation previously measured in the affine numerator recurrence came from
a one-channel dyadic trap, this coordinate would be constant while `p` remains
in the reduced residual denominator.

## A concrete source-reachable escape

The `1/21` greedy prefix selects rank `k=5`; the primitive prime is `p=31`.
The exact residuals give

\[
 r_5=r_6=\frac{10}{651},\qquad
 r_7=\frac{619}{82677}.
\]

Their reduced numerators satisfy

\[
 10^5\equiv25\pmod{31},\qquad
 619^5\equiv30\pmod{31}.
\]

By (1), the numerator has left its initial coset of `H_5` by rank `7`.
This is an exact counterexample to universal single-dyadic-coset trapping on
the actual `1/21` prefix, not a random or relaxed orbit.

## Census

The producer checked the exact greedy prefixes of

```text
1/2, 1/21, 4/9, 1/465, 3/7
```

through rank `180`, using every selected primitive-prime channel with selected
period at most `60`.

```text
primitive channels                              138
nontrivial quotient channels                    117
channels escaping their initial dyadic coset    117 / 117
median distinct dyadic cosets                     16
maximum distinct dyadic cosets                    74
```

The widest channel is the `1/465` prefix at selected period `17`, with
primitive prime `131071`: it visits `74` distinct cosets among `164` active
horizons and changes coset `73` times.  Every tested channel whose quotient
`F_p^*/H_k` has more than one element escapes its first coset.

## Consequence and boundary

This kills the simplest algebraic interpretation of the numerator's serial
correlation: the source-reachable orbit is not confined to one projective
class modulo each selected primitive prime.  More generally, the observed
projective state is not a tiny exceptional set: its median tested channel
already occupies sixteen dyadic cosets.

The result does **not** kill a genuinely global adelic relation coupling many
primitive channels at once, nor does finite computation prove unbounded coset
proliferation.  A future numerator route must therefore use simultaneous
cross-prime compatibility or a source-specific boundary condition.  Treating
one primitive channel as a finite-state/projective trap is eliminated.

## Reproduction

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/\
  rational_residual_numerator_residue_probe.py \
  --depth 180 --max-period 60 \
  --check-receipt state/formal_math/erdos257_period_noncollapse/\
  rational_residual_numerator_residue_probe_receipt.json
```

The machine-readable receipt records every channel summary and a digest of
its ordered projective signature stream.  The exact engine is the existing
fixed-point `Engine` in `cantor_staircase_run_length_lab.py`; no floating-point
comparison chooses a greedy bit.
