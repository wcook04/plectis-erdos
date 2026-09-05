# Agent related-work check

This pass checked three existing comparisons in the systems and strategy papers
against the authors' arXiv HTML papers on 5 September 2026. It is a bounded
source check, not an exhaustive literature search or a reproduction of results.

- [LeanMarathon, sections 1.1, 2.1 and 3.3](https://arxiv.org/html/2606.05400v1)
  describes an evolving blueprint, scoped agents and CI checks. It also stores
  prose alongside formal types and compares cited proof dependencies with Lean's
  elaborated dependencies. Both Plectis papers now acknowledge this explanatory
  overlap explicitly. Graph agreement is the concrete check being compared.
- [Agent Hunt, section 3](https://arxiv.org/html/2603.06737v1) describes simulated
  bounties, theorem locks, ownership rules and local guard scripts. This supports
  the existing coordination comparison; it does not establish that the two
  systems use the same concurrency mechanism.
- [OpenProver, sections 2.1–2.2](https://arxiv.org/html/2607.09217v1) describes
  planner, worker and verifier roles, a compact whiteboard that records failed
  attempts, and a larger repository. The existing memory comparison is retained.

The native arXiv metadata API returned HTTP 429 during this pass. The accessible
primary HTML versions above supplied the checked passages. No API success,
downloaded PDF, new version, or independent reproduction is inferred.
