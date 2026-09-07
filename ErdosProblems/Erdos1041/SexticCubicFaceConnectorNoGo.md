# The pure cubic sextic face forces a radius-zero stratum

## The theorem

Consider the normalized sextic model

\[
H(z)=\operatorname{Re}(z^3-z^6)
\]

and the six directions

\[
\omega^j,\qquad \omega=e^{\pi i/3},\qquad 0\le j<6.
\]

Fix any radius \(r>0\). No pair of non-antipodal sixth-root directions gives
an equal-radius truncated-spoke connector contained in \(\{H\le0\}\).
Indeed, the joining chord always contains an explicit point where \(H>0\).
Antipodal pairs have length exactly \(2\), so they cannot supply the strict
metric conclusion either.

Consequently the tempting global homogeneous assertion

\[
\operatorname{Re}(Az+Bz^2+Cz^3-z^6),\qquad
\max(|A|,|B|,|C|)=1,
\]

does not admit one uniform positive-radius root-direction connector atlas.
The face \((A,B,C)=(0,0,1)\) must be treated as a radius-zero stratum.

## The half-step obstruction

Every non-antipodal pair has angular gap \(\pi/3\) or \(2\pi/3\), after
choosing the shorter orientation.

For the adjacent pair \((\omega^j,\omega^{j+1})\), take the chord midpoint:

\[
z={r\over2}(\omega^j+\omega^{j+1}).
\]

Its argument is \((2j+1)\pi/6\), and direct algebra gives

\[
z^3=i(-1)^j{3\sqrt3\over8}r^3.
\]

For the gap-two pair \((\omega^j,\omega^{j+2})\), take the point one third of
the way along the chord:

\[
z=r\left({2\over3}\omega^j+{1\over3}\omega^{j+2}\right).
\]

Again its argument is \((2j+1)\pi/6\), now with

\[
z^3=i(-1)^j{\sqrt3\over9}r^3.
\]

Thus in either case \(z^3=ix\) for a nonzero real \(x\). Since
\(z^6=(z^3)^2=-x^2\),

\[
H(z)=\operatorname{Re}(ix+x^2)=x^2>0.
\]

The obstruction is exact, occurs at an interior rational chord parameter,
and is independent of the radius.

## Why this is useful rather than merely negative

The computation that found this face did not produce a robust positive
minimum. Instead it drove the best radius to zero and the score to zero from
above. The analytic calculation explains that behavior exactly.

At radius zero, three odd sixth-root rays satisfy

\[
H(t\omega^{2k+1})=-t^3-t^6\le0.
\]

So the correct connector on the pure cubic face is the two-arm path through
the origin. This agrees with the already-proved cyclic-trinomial fiber
theorem: the face is solvable, but by a degenerate-radius mechanism that a
strict positive-radius atlas cannot represent.

The degree-six near-Fekete proof must therefore be stratified:

1. use the origin connector on the exact cubic-mode face;
2. prove a quantitative radius-zero stability cone for perturbations of that
   face;
3. use positive-radius finite atlases only after normalizing away from that
   cone;
4. retain the already-closed square-contact/null box as the other exceptional
   stratum.

This is a genuine no-go theorem for the naive atlas architecture, not a
counterexample to Erdős #1041. It removes an impossible proof obligation and
identifies the next analytic producer: a stable origin cone around the cubic
face.

## Verification

The exact checker enumerates all twelve non-antipodal ordered gap
representatives, verifies the rational chord parameters, reconstructs the
purely imaginary cubes in \(\mathbb Q(\sqrt3)\), and proves that the escape
value is the corresponding positive square. Its terminal output is
`PASS: every positive-radius non-antipodal sixth-root chord has an exact
escape point`.

The load-bearing formal evidence is the local
[Lean core](./SexticCubicFaceConnectorNoGo.lean):
[`cubicFaceValue_pos_of_cube_eq_mul_I`](./SexticCubicFaceConnectorNoGo.lean#L31-L37),
[`adjacentMidpoint_cube`](./SexticCubicFaceConnectorNoGo.lean#L39-L46),
[`adjacentMidpoint_cubicFaceValue_pos`](./SexticCubicFaceConnectorNoGo.lean#L48-L57),
and [`not_all_nonpos_of_halfStep_mem`](./SexticCubicFaceConnectorNoGo.lean#L59-L67).
The exact symbolic replay is

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_sextic_cubic_face_connector_no_go.py
```

The checker and Lean declarations establish this source-specific obstruction
only. They do not prove a radius-zero stability cone, extend the result to the
full sextic model, or refute Erdős #1041; no priority, novelty, or peer-review
claim is made.
