# Erdős 1041 research corpus

This directory is the complete public-safe committed research corpus for
Erdős Problem 1041 at source checkpoint `867638684907b4ebd4ab2ef7b5de22dafda71e36`. The unrestricted
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
contain private authoring coordinates. Paths for files published here become
public `research_corpus/Erdos1041/...` paths. Unpublished source evidence uses
an explicit `source-provenance://` locator and is not an executable public
interface. Both source and public digests and the replacement count are
recorded in the corpus manifest. Cache bytecode and binary files are excluded.
