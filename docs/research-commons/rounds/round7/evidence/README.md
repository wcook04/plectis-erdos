# Frozen round-7 replay and development examples

The [manifest](MANIFEST.json) pins these records to public source commit
`0d0129c69ad1d6f48b7afbb2ae34681cc210c9fe`. The local replay completed on
29 September 2026: eight exact relation obligations and four diagnostic probes
passed, with all requested axiom reports present and only the permitted standard
axioms. [Kernel summary](kernel-summary.json),
[binding receipt](relation-bindings.json), and
[generated binding source](RelationBindings.lean) preserve the checked material.
The local build summary records the prerequisite target's native build result.

The [development prompts](restatement-development/participant/prompts.json),
[answer key](restatement-development/control/answer_key.json), and
[control manifest](restatement-development/control/manifest.json) contain eight
disclosed tasks across five problem families. The native benchmark builder
checked the local binding receipt against its complete source snapshot before
these files were frozen. This records `development_binding_replay_checked`,
not an unseen test set, independent semantic adjudication, a model score, or a
new mathematical result. Keep the control directory outside a reader's mount;
the full repository still reveals the answers.

To reproduce the binding on the named source commit in a separate checkout,
provision the pinned Lean environment, then use the public owners:

```sh
python3 scripts/lean_fast_build.py --jobs 2 ErdosProblems.ArgumentGraph.Results.RelationCertificates
python3 scripts/relation_binding.py replay > relation-replay.json
python3 scripts/build_restatement_benchmark.py --binding-receipt relation-replay.json --trusted-local-replay --out development-bank
```

The receipt contains the hashes of 2,248 source inputs. Its random temporary
probe pathname is an invocation label; the generated source bytes are retained
here and their hash is checked. The JSON is a maintainer-supplied record, not
cryptographic authentication of who invoked Lean or proof of a clean-room
build. Subsequent journal and publication changes intentionally make this a
historical snapshot: replay against the newer checkout to obtain a current
receipt. Release validation and CI remain separate evidence.
