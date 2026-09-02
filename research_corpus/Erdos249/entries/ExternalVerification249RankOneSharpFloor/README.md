# Erdős #249: sharp positive rank-one floor

This package exposes the complete checked endpoint family for the positive
rank-one Möbius--Mersenne cone used in the Erdős #249 programme.

For admissible `e ≥ 1`, `Y ≥ 4`, define

\[
Q(e,Y)=\frac{t_Y(e+2)^2}{t_Y(2e+2)},\qquad
t_Y(r)=\sum_{d=1}^{Y}\frac{\mu(d)}{(2^d-1)^r},
\]

and let `Θ₂` be the corresponding infinite Möbius--Mersenne sum.  The six
compared declarations prove that:

- `(e,Y)=(1,5)` is the unique minimizer;
- every admissible quotient satisfies `Q(e,Y)-Θ₂ > 21/320`;
- `1/16` is therefore a valid uniform unit-fraction floor;
- `1/15` fails already at the unique minimizer;
- every nonempty finite positive weighted mixture retains the `21/320` floor;
- every rational representation `Q(e,Y)=p/q` gives the explicit strict
  linear-form bound `q(21/320) < |qΘ₂-p|`.

The primitive-form theorem is a useful arithmetic presentation of the same
floor, not a separate mechanism.  The positive-mixture theorem shows that
adding positive rank-one blocks cannot close the gap.  Signed combinations
and genuinely coupled higher-rank kernels are outside the theorem, so Erdős
#249 remains open.

`Challenge.lean` imports only Mathlib.  `Solution.lean` transports all six
source-current declarations from
`ErdosProblems/Erdos249/RankOneSharpFloor.lean`.  The deliberate negative
contains only the unique-minimizer declaration, forcing rejection of a
solution that omits the quantitative and closure content.

## Verification

From `formal_math/erdos257_period_noncollapse`:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification249RankOneSharpFloor/Challenge.lean \
  ExternalVerification249RankOneSharpFloor/Solution.lean \
  ExternalVerification249RankOneSharpFloor/NegativeSolution.lean \
  ExternalVerification249RankOneSharpFloor/AxiomAudit.lean
```

Exit `75` is an environment-capacity receipt, not a theorem failure.  The
positive and deliberate-negative Comparator runs remain separate terminal
gates on a supported Linux runner.

## Palomar disposition

This is a first-wave Palomar candidate: a sharp minimizer theorem, a strict
explicit floor, an optimal unit-fraction boundary, and closure under arbitrary
finite positive mixing form one coherent and nontrivial no-go result.  The
open parent problem is the theorem boundary, not a reason to hide the result.

Submission still requires a public repository at a pinned full commit SHA,
terminal positive acceptance, deliberate-negative rejection, and
source-current metadata.  These local files are not a Palomar verdict,
registry entry, novelty ruling, or peer review.
