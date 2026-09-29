# Comparing research readers

This is an executable preparation and analysis protocol. No controlled model
comparison is reported here. The six historical pilot runs remain development
observations; they cannot estimate a general research advantage.

The primary question is whether a frozen corpus view helps a reader identify
the current frontier, classify a relation, preserve a claim's evidence class,
or recognize an existing transfer. Discovery of useful new mathematics is a
separate prospective question. The development restatement benchmark in this
directory supplies [source-bound examples](RESTATEMENT_DEVELOPMENT.md) for
testing the measurement process.

## Prepare a study

Use the existing benchmark entry point:

```sh
python3 scripts/benchmark_semantic_reasoning.py study prepare \
  --spec reviewed-study.json --source-root frozen-material --out sealed-study
```

The specification has schema `plectis-reader-study/1`, mode `development` or
`confirmatory`, an integer randomization seed, an exact model snapshot, positive
integer resource limits, and a nonempty task list. Each task names a unique
task and semantic family, a prompt, a frozen gold SHA-256, a kind (`frontier`,
`restatement`, `status`, or `transfer`), and an explicit file/hash allowlist for
each selected arm. Confirmatory tasks require `split: sealed_confirmatory`.
Confirmatory preparation also requires both P and F arms and this explicit
`analysis_plan` in the reviewed specification:

```json
{
  "primary": {"baseline": "P", "treatment": "F"},
  "minimum_useful_difference": 0.1,
  "primary_test": "two_sided_exact_mcnemar",
  "secondary_policy": "descriptive_without_preregistered_multiplicity_plan"
}
```

The preparer copies that fixed plan into the private control manifest before
any job runs. A control manifest is a frozen local plan, not external
preregistration. Development analyses and secondary arm contrasts report
paired estimates and diagnostic intervals with `analysis_role` marked
descriptive; their exact-test p-value and automatic ten-point conclusion are
null. The F–P contrast receives those inferential fields only in confirmatory
mode with the fixed plan present.

Supported arms are P (papers), R (repository), F (compiled corpus view), and A
(content-matched ablation). Their names do not establish information matching:
review each actual allowlist and record differences in available facts, prose,
tool access and budget. Repeated prompts, aliases and seeds from one theorem
family do not become independent examples. Keep previously inspected families
out of the confirmatory cohort.

The preparer refuses changed inputs, unsafe paths, empty tasks and overwritten
study directories. It randomizes jobs and separates their material from the
private arm mapping and gold identities. This protects byte identity; it does
not prove that the supplied material lacks semantic answer leakage.

## Execute and capture with a trusted bridge

`study verify-job JOB --expected-spec-sha256 DIGEST` checks the exact mounted
material inventory and all bytes. It refuses unlisted files, links and special
files as well as changed allowed files.

The native `study execute` subcommand runs one job through an operator-supplied
provider bridge. It requires an externally retained SHA-256 for both the study
specification and private control manifest, the exact job ID and deployment
file, and a fresh output directory. Real runs additionally require a reviewed,
model-matched deployment bound by the study specification and the explicit
`--authorize-provider-run` flag. The bridge receives one JSON request per
exchange and must enforce the remaining token cap before a paid call. Only
list/read/literal-search tools over the frozen material allowlist are exposed
by the native broker. A fresh provider session, no-network boundary, output
custody, and honest bridge usage reporting remain operator responsibilities;
this Python controller is not an OS sandbox or provider attestation.

`study capture` takes an index of controller receipt paths and externally
retained receipt hashes. It checks the complete cohort, job/source/model/control
identity, exact trace bytes, start/stop events, ordered request/response/assistant
identities, usage totals and accepted final against the bridge output, and
nonreuse of traces and receipts. It refuses empty control cohorts. A bare
structured-output attachment is not an execution receipt. The output is an
execution array for `study blind`; mathematical correctness and grader
independence remain unverified. `scripts/reader_trace_adapter.py` supplies
trace normalization, with unknown costs retained as null.

The proposed historical 0268 materials are separately documented in
[round8_reader_pilot/README.md](round8_reader_pilot/README.md). They are
provider-unbound development candidates and have not been executed.

## Grade and analyze

Create an execution array with `job_id`, `status`, `trace_sha256`, and an
`answer` for each completed run. Status is `completed`, `timeout`,
`budget_exhausted`, `invalid_output`, or `not_run`. Preserve actual trace bytes.

```sh
python3 scripts/benchmark_semantic_reasoning.py study blind \
  --control sealed-study/private_control.json --executions executions.json
python3 scripts/benchmark_semantic_reasoning.py study analyze \
  --control sealed-study/private_control.json --executions executions.json \
  --grades adjudicated-grades.json --baseline P --treatment F
```

Give graders only `grading_packets` and identical gold access. Citations can
still reveal treatment, so describe blinding as partial. Final grades bind the
gold and trace hashes and include binary correctness and severe-error fields,
at least two distinct rater identities, and a review digest. Stored identities
do not prove reviewer independence; retain original reviews and adjudication.

The analyzer retains issued failures as zero, refuses incomplete cohorts and
pending grades, and reports paired accuracy differences and intervals. It
reports the exact McNemar test for the frozen confirmatory F–P primary contrast.
The conservative interval prevents a small all-tied sample from claiming to
exclude a useful effect. Family independence remains a scientific assumption.
Publish unfavorable results and deviations with the primary analysis.

```sh
python3 scripts/benchmark_semantic_reasoning.py study power \
  --n 352 --delta .10 --discordance .40
```

This is a planning calculation under the stated discordance and independence
assumptions, not an observed effect or an obligation to run 352 trials. First
establish task feasibility, grading effort and a budget. No sample-size choice
turns a development dataset into independent confirmation.

`scripts/research_evidence.py` provides journal and attempt accounting. It
keeps artifact, component and attempt identities distinct, retains missing
reviews and costs, and rejects insertion time as a substitute for occurrence
time. Reader-task success does not establish novelty, prospective transfer,
human usability or external replication.
