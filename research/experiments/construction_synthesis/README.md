<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Recovering a useful coordinate from the equations it simplifies

An exact symbolic search recovers the centered state used in the #243
research, up to sign, from three integer update rules:

```
a' = a² − a + 1,    D' = aD,    C' = aC − D.
```

The search finds `F = (a−1)C−D` and the identity `F' = a²F`, together
with `D' = aD` and `(a−1)' = a(a−1)`. Pairing quantities with the same
multiplier produces rational coordinates that stay constant. The generated
Lean file states the identities and the necessary nonzero denominator guards.
A separate validator checks these certificates against the imported corpus.
Its receipt, rather than this description, records whether checking succeeded.

This is a **reconstruction control**, not new mathematics or a chosen
ninth-paper architecture. The existing paper already uses this coordinate.
The person selecting the example knew the construction. The deterministic
search receives only the exported update rules, a polynomial degree bound,
and a finite list of possible multipliers. It receives neither the target
coordinate nor its proof nor the paper narrative. The result tests that a
small generator can construct the missing expression instead of being handed
an adapter. It does not test whether the system can choose a valuable problem
or discover a new method.

## Run

From the repository root, create the same explicit computation environment
used by the other optional research experiments, install the pinned
dependency, and use that interpreter for every step:

```sh
python3 -m venv ../.venv-plectis-computations
../.venv-plectis-computations/bin/python -m pip install \
  -r research/experiments/construction_synthesis/requirements.txt
../.venv-plectis-computations/bin/python \
  research/experiments/construction_synthesis/export_inputs.py
../.venv-plectis-computations/bin/python \
  research/experiments/construction_synthesis/search.py \
  --input research/experiments/construction_synthesis/input.json \
  --output research/experiments/construction_synthesis/results
../.venv-plectis-computations/bin/python \
  research/experiments/construction_synthesis/verify.py
../.venv-plectis-computations/bin/python -m unittest discover \
  -s research/experiments/construction_synthesis -p 'test_*.py'
```

The repository interpreter used by a maintainer may also satisfy the pinned
dependency, but that is not the independent public reproduction contract.

The exporter selects three explicit definitions from
`Erdos243/ReciprocalTailRigidity.lean`. The search is a separate process whose
only corpus input is `input.json`. It solves exact linear systems over the
rationals for all polynomials of total degree at most two satisfying
`F(next state) = a^k F(state)`, with `0 ≤ k ≤ 4`. It does not use numerical
fitting or a language model. Source definitions, locations and hashes are
recorded. Unsupported source syntax fails explicitly. The resulting formulas
are proposals until the generated Lean proof is accepted.

The same search is applied without adapters to all 25 coefficient pairs
`−2 ≤ b,c ≤ 2` in `a' = a² + ba + c`, keeping the other updates fixed.
Only `b=−1,c=1` yields a discovered coordinate involving `C`. This is an
exhaustive statement about that degree bound and multiplier list, **not** an
impossibility theorem about other coordinates or other methods.

`results/search.json` records the exact computation. `results/Generated.lean`
is the generated certificate. `results/lean.json` records the verifier's exit
code, output, proof hash, toolchain, manifest hash and imported module hash.
The verifier joins the shared host lock and does not rebuild the corpus.
Its proofs refer to the imported compiled module; source-to-import checks are
included in the generated certificate. A release requires the ordinary
source build workflow as well.

## Research decision

The desired capability is the synthesis of useful intermediate mathematical
objects, followed by proof reconstruction and reuse. This small probe supplies
one positive control. A credible next experiment must use a construction and
mathematical setting not selected because its answer was already known to the
designer, and must show that the construction enables a consequential argument.
Recovering more familiar formulas is not by itself the project.

The short papers identify mathematical significance; the long papers explain
why constructions work; Lean supplies exact semantics and an executable
check. None of those roles can be replaced by a declaration count or a
compression score. Learning from all three is the larger research hypothesis,
not an implemented capability of this script.

## Prior art

The numerical-algebra component is classical polynomial invariant synthesis.
In particular, the equation searched here is the defining form of a discrete
Darboux polynomial; see Celledoni et al.,
[Using discrete Darboux polynomials to detect and determine preserved measures
and integrals of rational maps](https://arxiv.org/abs/1902.04715).
We claim no invention of this technique.

For the broader idea of learning an executable vocabulary from solved tasks,
[DreamCoder](https://people.csail.mit.edu/asolar/papers/EllisWNSMHCST21.pdf)
is direct prior art. For automatic generalization of existing Lean proofs,
see Gandhi, Tadipatri and Gowers,
[Automatically Generalizing Proofs and Statements](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.12).
A corpus-specific implementation does not establish novelty on its own.

An earlier local proof-generalization probe succeeded, but was discarded as
the ninth-paper direction because it reproduced an established capability.
A proposed adversarial-counterexample direction was rejected by the operator
before implementation. Neither is the objective of this experiment.
