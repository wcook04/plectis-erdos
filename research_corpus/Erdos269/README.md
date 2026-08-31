# Erdős 269 research corpus

This directory is the complete public-safe committed research corpus for the
three-prime case of Erdős Problem 269 at source checkpoint `832ab7f5d3ffd88eb7bbac065be2c4de2a08b266`.
The problem — irrationality of `S = sum over {2,3,5}-smooth s of 1/H(s)`,
with `H` the running LCM of the smooth prefix — remains OPEN; these files
contain proved reductions, Lean-checked statements, exact computations,
countermodels, no-go results, retired-route labs, and the live research
packet. No navigation label or experimental receipt upgrades a statement
beyond its own hypotheses.

Start with [`STRONGEST_RESULTS.json`](STRONGEST_RESULTS.json): the strongest
activated premises and falsifiers, what weaker work they dominate, their exact
hypotheses, their consumers, and their public file locations. Then read
[`research_packet.json`](research_packet.json) — the non-claims ledger with
the exact open producers, the 27-row negative-result bank, and the claim
ceiling — and the three live labs:
[`TorusCocycleAndDiophantineTypeLab.md`](TorusCocycleAndDiophantineTypeLab.md),
[`PurePowerIrrationalityNote.md`](PurePowerIrrationalityNote.md), and
[`IntegralTailStructureLab.md`](IntegralTailStructureLab.md). Use
[`CORPUS_MANIFEST.json`](CORPUS_MANIFEST.json) for every published file and
its digest. Route choice is deliberately unrestricted: the map is a premise
floor, not a prescribed proof strategy.

Publication relation: committed source files are copied exactly unless they
contain private authoring coordinates. Paths for files published here become
public `research_corpus/Erdos269/...` paths. Unpublished source evidence uses
an explicit `source-provenance://` locator and is not an executable public
interface. Both source and public digests and the replacement count are
recorded in the corpus manifest. Cache bytecode and binary files are excluded.
