# Developmental relation benchmark

A [frozen round-7 bank with its local replay evidence](../rounds/round7/evidence/README.md)
is available for inspection. Its eight disclosed examples were checked at the
commit named in that record. The commands below build from the current checkout;
the historical receipt must not be used to certify changed source inputs.

Run from a cold public clone without private files or a Lean build:

```sh
python3 scripts/build_restatement_benchmark.py --out restatement-development
```

The builder reads the authored relation registry, invokes the native
`relation_binding.emit` owner, and checks the current registry and certificate
source bytes against that owner's snapshot. It writes eight tasks across five
problem families. Four ask about scoped equivalence, two about conditional
endpoint routes, one about a local refutation, and one about feasibility.
These are disclosed **development** examples, not eight independent theorem
families or a confirmatory test bank.

Only `participant/prompts.json` belongs in a reader's material. Keep
`control/answer_key.json` and `control/manifest.json` outside the reader's
mount. Each key row names the exact certificate declaration and source line,
the complete context, and the row/source hashes. The prompts contain the
scoped expressions without their relation labels or certificate names.
The source registry and Lean files in a full clone do reveal the answers, so
file separation alone does not establish blind execution or prevent leakage.

An ordinary build states `development_unverified`: exact obligations were
generated but not Lean-replayed. A maintainer may supply a locally trusted
`relation_binding replay` JSON result with `--binding-receipt PATH
--trusted-local-replay`. The builder rechecks every obligation, source hash,
native success field and per-binding permitted-axiom list. This changes the
state to `development_binding_replay_checked` in the invoked environment.
The explicit trust assertion is necessary because JSON hashes bind bytes but
cannot authenticate who ran Lean. A clean source-bound build and independent
meaning review remain separate. `--seal-confirmatory` is refused even with a
replay: these known examples cannot become unseen gold.

Use the tasks to test whether a reader keeps relation, context, direction,
open premise and supplied-result status distinct. A recognized restatement is
not a new theorem. A one-way route does not discharge its open input. Correct
answers on this bank support no measured performance, novelty, independent
result count or prospective discovery claim. The controlled reader protocol is
in [READER_STUDY.md](READER_STUDY.md); new confirmatory families require a
separately frozen, independently adjudicated bank.

## Historical Round 8 candidate bank

[Round 8 disclosed candidate questions](round8_candidate_development/README.md)
add 12 source-excerpt-bound examples across four dependent problem clusters at
historical commit `0268dd8bfb2a556a0c93078337d42c6d07138fa2`.
Use `python3 scripts/benchmark_semantic_reasoning.py restatement candidate
validate` to inspect their custody state, or the `candidate` subcommands for
response parsing and byte-bound label-free review export. The author proposals
stay separate and are not mathematical gold. This addition does not replace
the eight-row current-source calibration above or claim a new Lean replay.
