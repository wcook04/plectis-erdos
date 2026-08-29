# Erdős 1041 research corpus

This directory is the complete public-safe committed research corpus for
Erdős Problem 1041 at source checkpoint `6658deca35adde05f60bd2a19c76da996698bc9a`. The unrestricted
problem remains open; these files contain proved conditional reductions,
Lean-checked statements, exact computations, counterexamples, no-go results,
assimilation records, and live proof-frontier notes. No navigation label or
experimental receipt upgrades a statement beyond its own hypotheses.

Start with [`FRONTIER.md`](FRONTIER.md). It is the dated current state: what
was refuted and must not be rebuilt, which carriers survive, the new proved
tools, and the exact open gaps. Read it before
[`STRONGEST_RESULTS.json`](STRONGEST_RESULTS.json), which is generated from
the activation lists and can lag the frontier notes by a dated delta.

`STRONGEST_RESULTS.json` states the strongest activated premises and
falsifiers, what weaker work they dominate, their exact hypotheses, their
consumers, and their public file locations. Then use
[`CORPUS_MANIFEST.json`](CORPUS_MANIFEST.json) for every published file and
its digest. Route choice is deliberately unrestricted: the map is a premise
floor, not a prescribed proof strategy.

Publication relation: committed source files are copied exactly unless they
contain a local absolute path. Such paths are replaced by a stable
`public-source-redacted://` locator; both source and public digests and the
replacement count are recorded in the corpus manifest. Cache bytecode and
binary files are excluded.
