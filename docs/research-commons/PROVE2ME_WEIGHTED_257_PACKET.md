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
arbitrary finite set from the weighted host. The stronger
[eventual-containment consequence](https://prove2.me/theorems/f64da58c-9d9e-4d42-bff7-0907905e6ac5)
is public and Proved too: an infinite support may have arbitrary elements
outside a binary-weighted host up to a finite cutoff, provided its strict
tail lies in that host. Its proof combines the paper theorem with a separate
[finite-prefix transfer](https://prove2.me/theorems/26a05c39-b6fa-47d2-9e35-5a39a8185a03),
also public and Proved. This is source-prepared native reuse across two
results. These statuses do not establish outside first use, mathematical peer
review, or the universal Erdős #257 claim.

**Reading the proof.** Prove2Me displays its formal challenge statement with
`:= by sorry` even when the theorem is marked Proved. The accepted Solution is
separate under **View graph → Solutions & Sketches**; the graph route asks
signed-out readers to sign in. Without an account, start with the wrapper's
two linked component theorems and their pinned public Lean sources:
[fixed-base heredity](https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/WeightedHereditaryClaim.lean#L31)
and the [all-base weighted claim](https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120).
The [paper's Theorem 1](../../paper/257/erdos-257-mersenne-support-subseries.tex)
states the mathematical result and its context.

## Try changing a hypothesis

The paper's example uses the support
$A_\star=\{2^km:k\ge1,\ m\text{ odd},\ m\le2^{2^k}\}$.
Its reciprocal sum diverges, yet its base-two weighted mass is finite, so
Theorem 1 applies to every infinite subset at every integer base.
What changes if the odd-factor cutoff in layer $k$ becomes $2^{r_k}$, where

$$
r_k=\left\lceil\frac{c^{2^k}}{k^p}\right\rceil,
\qquad c\ge2\text{ an integer},\quad p>0?
$$

For $c=2,p=1$, decide whether the $P=\{2\}$ weighted test works at bases
$2$ and $3$. Then change only $p$ to $2$ and decide what Theorem 1 says at
*every* base. Before opening the calculation, distinguish “this test fails”
from a claim that the corresponding series is rational.

<details>
<summary>Show the calculation and decisions</summary>

Put $A(c,p)=\{2^km:k\ge1,\ m\text{ odd},\ 1\le m\le2^{r_k}\}$ and
$S_r=\sum_{1\le m\le2^r,\ m\text{ odd}}1/m$. The dyadic estimate in the
[paper's example](../../paper/257/erdos-257-mersenne-support-subseries.tex)
gives $r/4\le S_r\le r$ for $r\ge1$. Layers are disjoint because $2^km$
has exactly $k$ factors of $2$. Hence

$$
\sum_{a\in A(c,p)}\frac1a=\sum_{k\ge1}\frac{S_{r_k}}{2^k},
\qquad
W_{b,\{2\}}(A(c,p))=\sum_{k\ge1}\frac{S_{r_k}}{b^{2^k}-1}.
$$

The reciprocal sum diverges for every listed $c,p$: its $k$th layer is at
least $c^{2^k}/(4k^p2^k)$, which does not tend to zero. For the weighted
sum, $r_k$ lies between $c^{2^k}/k^p$ and $c^{2^k}/k^p+1$. The same bounds
on $S_r$, and $b^{2^k}/2\le b^{2^k}-1\le b^{2^k}$, bound its $k$th term
below by $(c/b)^{2^k}/(4k^p)$ and above by
$2(c/b)^{2^k}/k^p+2b^{-2^k}$. Therefore:

| Changed condition | $P=\{2\}$ weighted test at base $b$ |
| --- | --- |
| $b>c$ | Converges |
| $b=c$ and $p>1$ | Converges |
| $b=c$ and $0<p\le1$ | Diverges |
| $b<c$ | Diverges |

For $c=2,p=1$, the test passes at base $3$ and every larger integer base.
The fixed-base clause therefore makes $X_B(b)$ irrational for each such
base and every infinite $B\subseteq A(2,1)$. At base $2$, this particular
test diverges: it gives **no arithmetic verdict** there. Another witness
or argument has not been ruled out. When $p=2$, the base-two test passes;
the all-base clause makes $X_B(b)$ irrational for every integer $b\ge2$
and every infinite $B\subseteq A(2,2)$.

This parameterised calculation is an ordinary deduction from the paper's
criterion and its dyadic bound. The Lean declarations prove the conditional
criterion, not a named theorem about this family. The unrestricted Erdős
#257 question remains open.

</details>

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
