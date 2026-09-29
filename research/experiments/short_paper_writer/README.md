# Source-bound short-paper demonstration

This is an authored `dossier/1` example for #269, not a general corpus extractor.
The `extensions.short_paper_v1` proposal supplies the narrative roles absent from
the base round-10 interface. The companion `claim_evidence/1` transport records
source-reported ordinary AI review; it does not assert a new human, Lean or
Comparator check.

Read `docs/papers/SHORT_PAPER_CONTRACT.md` first. From the repository root:

```sh
python3 scripts/test_short_paper_writer.py
python3 -O scripts/test_short_paper_writer.py
python3 scripts/short_paper_writer.py audit --output /tmp/short-paper-audit.json
python3 scripts/short_paper_writer.py draft \
  --dossier research/experiments/short_paper_writer/dossier269.json \
  --evidence research/experiments/short_paper_writer/claim_evidence269.json \
  --output-dir /tmp/new-short-paper-draft
python3 scripts/short_paper_writer.py check-draft \
  --dossier research/experiments/short_paper_writer/dossier269.json \
  --evidence research/experiments/short_paper_writer/claim_evidence269.json \
  --output-dir /tmp/new-short-paper-draft
```

Use a new output directory for `draft`; overwrite is refused. To rebuild the
authored fixture from its pinned native source, use
`python3 scripts/build_short_paper_demo.py --output-dir <new-directory>`.
This builder copies the selected source statements and recomputes span hashes;
it does not choose new mathematics or independently verify the ordinary proof.

Audit exit zero means no hard structural findings, not publication readiness.
The `plectis-public-system` alternative systems-paper selection has expected
house-style findings at the supplied source cut. Narrative quality remains
unassessed by this checker. A deliberately false paraphrase can pass structural
validation even with the original theorem and exact source spans retained:
semantic review and cold-reader evidence are separate obligations.
