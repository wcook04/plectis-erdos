<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Offline Prove2Me candidate: weighted Erdős #257 support theorem

The default unit `erdos257_finite_prime_weighted_support` presents a direct
irrationality theorem that applies to some supports with divergent reciprocal
sums.
The separately checked mixed weighted-cover theorem (`res:mixed-supports`)
covers further supports under its additional cover hypotheses.
The weighted theorem is **already proved locally**, so its possible Prove2Me
role is one theorem statement followed by its proof, not an open mission that
asks someone to discover it. Neither the adapter nor this note submits or
registers anything.

## Exact claim

For a finite nonempty prime set $P$, let
$h_P(a)=\prod_{p\in P}p^{v_p(a)}$. If $b\ge2$, $A$ is an infinite set of
positive integers, and

$$
\sum_{a\in A}\frac{h_P(a)}{a(b^{h_P(a)}-1)}<\infty,
$$

then $\sum_{a\in A}(b^a-1)^{-1}$ is irrational. Separately, if a host $H$
of positive integers has finite weighted mass at base two for some such $P$,
then **every infinite subset** $A\subseteq H$ has an irrational support sum
at **every** integer base $b\ge2$. The paper states both clauses and their
hereditary consequences at `res:weighted-support` in
`paper/257/erdos-257-mersenne-support-subseries.tex`.

The exact Lean declaration is
`ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim` at
`lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean:120`.
Its conjunction type `DivisibilityWeightedClaim` and the weighted-mass
definition `FinitePrimeWeighted` are in
`lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean:75` and
`:32`. The public claim row is `finite_prime_weighted_support` in
`docs/claims.json`, status `formalised here`. The packet hashes the theorem,
paper, and Lean claim-interface source, and checks the registered declaration
line, paper label and exact open-proposition mapping.

Lean checks the weighted criterion. The paper verifies an explicit
reciprocal-divergent support to which it applies; that example is ordinary
paper mathematics, not a separate Lean named-instance theorem. The criterion
does **not** prove the universal Erdős #257 assertion for every infinite
support. The registered
remainder is `remaining_open.universal_257_all_infinite_supports`. No
external novelty, priority, or peer-review verdict follows from this packet.

## Prepare a source-bound packet

From a checkout with `origin/main` available:

```sh
python3 scripts/prove2me_compat.py prepare \
  --out /tmp/erdos257-weighted-p2m/packet.json
python3 scripts/prove2me_compat.py validate \
  --packet /tmp/erdos257-weighted-p2m/packet.json \
  --out /tmp/erdos257-weighted-p2m/validation.json
```

The candidate is deliberately blocked. The local source is pinned to Lean
v4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
The authenticated environment inventory recorded on 23 September 2026 in
`PROVE2ME_COMPAT.md` contained no matching pair. An official
[Prove2Me environment](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md)
is identified by both toolchain and Mathlib revision. The current service
inventory must be checked again by an authorized contributor before any port;
this packet does not claim compatibility with any service environment.

The official
[whole-project guide](https://github.com/prove2me/prove2me_workspace/blob/main/references/upload_full_project.md)
requires a matching environment, declaration and sketch extraction, a
compiled staged tree, and an exact elaborated-type comparison. The local
adapter requires receipts for those steps before exporting a review draft.
Its checks cannot themselves certify that a port preserved the theorem.
Prove2Me's
[contribution guide](https://github.com/prove2me/prove2me_workspace/blob/main/references/contribute.md)
distinguishes a queued publish job from a published theorem ID; no such job
or ID exists for this candidate in the packet.

The narrower reciprocal-summable result remains selectable with
`--unit erdos257_reciprocal_summable_support` as a smaller portability pilot.
It retains its own Erdős attribution and the same environment and staged-port
blockers. Default selection changes neither the claim registry nor any
mission state.
