<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Proof cockpit

The proof cockpit is the public Lean repository's cold-clone control card. It
composes facts that already belong to this checkout: Git identity, pinned Lean
release identity, corpus scale, exact open propositions, per-problem
obligations, and committed workbench sessions.

```sh
python3 scripts/proof_cockpit.py
python3 scripts/proof_cockpit.py --problem 257
python3 scripts/proof_cockpit.py --format json
python3 scripts/proof_cockpit.py --check
```

The default card is cheap and read-only. `--problem` focuses one of the eight
indexed Erdős programmes without pretending that declaration volume measures
progress. `--check` explicitly runs the fast public floor: the claim registry,
cold-clone comprehension, and generated-orientation freshness checks. It does
not run Lean; the card always names `python3 scripts/lean_fast_build.py --jobs
2` as the proof-authority gate.

This is deliberately native to the public Lean project. It does not export the
private Station UI, phases, Task or Work Ledger state, provider traces, agent
memory, or operator state. The closest public equivalents are mathematical:

- checkout and pinned-toolchain identity instead of private runtime identity;
- exact open propositions and problem obligations instead of a private task queue;
- workbench ledgers and kernel probe receipts instead of model-authored status;
- typed corpus and proof-plan commands instead of hidden routing state;
- the Lean build as the only formal-truth gate.

The cockpit is navigation and runtime observation, not proof authority. A
clean card does not prove a theorem, settle a problem, establish novelty, or
change `docs/claims.json`.
