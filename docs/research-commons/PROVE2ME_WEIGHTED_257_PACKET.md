<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Weighted Erdős #257 theorem on Prove2Me

The [paper Theorem 1 wrapper](https://prove2.me/theorems/f6d332dc-466f-4f2a-a207-6b0455c0fbbd)
is public and **Proved** on Prove2Me in Lean 4.30.0 with Mathlib `c5ea003`.
It combines the fixed-base hereditary criterion with the all-base conclusion
from a base-two weighted witness. It is a new composition of two accepted
Lean declarations, not a declaration copied verbatim from this checkout.
A [finite-deletion consequence](https://prove2.me/theorems/617fa7c2-841e-4ab0-9f2c-7152d79e3891)
is also public and Proved in the same environment. Its statement removes an
arbitrary finite set from the weighted host. These public statuses establish
machine-checked native results; they do not establish outside first use,
mathematical peer review, or the universal Erdős #257 claim.

**Reading the proof.** Prove2Me displays its formal challenge statement with
`:= by sorry` even when the theorem is marked Proved. The accepted Solution is
separate under **View graph → Solutions & Sketches**; the graph route asks
signed-out readers to sign in. Without an account, start with the wrapper's
two linked component theorems and their pinned public Lean sources:
[fixed-base heredity](https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/WeightedHereditaryClaim.lean#L31)
and the [all-base weighted claim](https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120).
The [paper's Theorem 1](../../paper/257/erdos-257-mersenne-support-subseries.tex)
states the mathematical result and its context.

Here is the accepted wrapper Solution as stored by Prove2Me on 25 September.
It composes those two imports; the hard weighted criterion is in the imported
proofs. The platform imports belong to Prove2Me's Lean 4.30.0 environment,
not this checkout's Lean 4.29.1 toolchain. The public Proved badge and this
copy are useful inspection evidence, while an independent replay still needs
that pinned environment and its dependency graph.

```lean
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finitePrimeWeighted_fixedBase_hereditary
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisibilityWeightedClaim

noncomputable section

theorem solution :
    (∀ (b : ℕ) (H : Set ℕ), 2 ≤ b → 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted b H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        Irrational (Erdos249257.erdosSupportSeries b A)) ∧
    (∀ H : Set ℕ, 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b →
          Irrational (Erdos249257.erdosSupportSeries b A)) := by
  constructor
  · intro b H hb hH0 _ hweighted A hAH hA
    exact ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary
      b H hb hH0 hweighted A hAH hA
  · intro H hH0 _ hweighted A hAH hA b hb
    exact ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim.2
      H hH0 hweighted A hAH hA b hb
```

The offline adapter described below predates this hosted release. It remains
a source-bound experiment against this checkout's older toolchain; its
blocked validation is **not** a verdict on the separately ported and accepted
Prove2Me objects.

The default unit `erdos257_finite_prime_weighted_support` presents a direct
irrationality theorem that applies to some supports with divergent reciprocal
sums.
The separately checked mixed weighted-cover theorem (`res:mixed-supports`)
covers further supports under its additional cover hypotheses.
The weighted theorem was already proved locally before its native port.
Neither the adapter nor this note submits or registers anything.

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

This older adapter candidate is deliberately blocked. The local source is pinned to Lean
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
or ID is created by this offline adapter packet. The public theorem linked
above was delivered through a separate native port.

The narrower reciprocal-summable result remains selectable with
`--unit erdos257_reciprocal_summable_support` as a smaller portability pilot.
It retains its own Erdős attribution and the same environment and staged-port
blockers. Default selection changes neither the claim registry nor any
mission state.
