/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic

/-!
# Demand-ledger edges: cluster B — `survivorKill`

Three open antecedents of #249, all phrased with the decidable carry-survivor
certificate `TotientTailPeriodKiller.survivorKill`:

* `G081` — multiple-period supply:
  `∀ h₀ > 0, ∀ N₀, ∃ m > 0, ∃ N ≥ N₀, ∃ K, survivorKill (m * h₀) N K`
* `G102` — one-parameter (lcm ray) supply, general position:
  `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ K, survivorKill (periodLcm t) N K`
* `G094` — diagonal supply, standing on the ray:
  `∀ t₀, ∃ t ≥ t₀, ∃ K, survivorKill (periodLcm t) (periodLcm t) K`

This file kernel-checks the direct chain of specialisations:

  `G094 → G102 → G081`.

Thus `G081` is a weakest node in the implication order proved in this file: it
is implied by the other two.  This does not prove strict separation.
`DemandLedger/edges/Bridge1.lean` later supplies reverse implications through
the irrationality hub and proves all three equivalent to Erdős #249.

The two structural moves are exactly the ones the supply ladder uses on the
`Irrational` side, transported to the antecedents themselves:

* `G094 → G102` — the diagonal point `N = periodLcm t` is a legal general
  position, because `t ≤ periodLcm t`; evaluating the diagonal hypothesis at
  `max t₀ N₀` makes it clear both bounds at once.
* `G102 → G081` — every `h₀ ≤ t` divides `periodLcm t`, so the lcm period is
  itself a multiple `m * h₀` with `m = periodLcm t / h₀ > 0`.

The three reverse edges are not proved in this file; they are proved later in
`Bridge1.lean` by a different route.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.ClusterB

/-- **Diagonal ⟹ general position.**  A survivor kill sitting on the diagonal
`(h, N) = (periodLcm t, periodLcm t)` is in particular a survivor kill at a
position `N ≥ N₀`, because `periodLcm t ≥ t` and the diagonal hypothesis can be
evaluated at `max t₀ N₀`, which forces `t ≥ t₀` and `periodLcm t ≥ t ≥ N₀`
simultaneously.  This is the antecedent-level form of the wave-23 collapse. -/
theorem e_G094_G102 : G094 → G102 := by
  unfold G094 G102
  intro h t₀ N₀
  obtain ⟨t, ht, K, hkill⟩ := h (max t₀ N₀)
  refine ⟨t, le_trans (le_max_left _ _) ht, periodLcm t, ?_, K, hkill⟩
  exact le_trans (le_trans (le_max_right _ _) ht) (le_periodLcm t)

/-- **Lcm ray ⟹ multiple-period.**  Given a primitive period `h₀ > 0`, run the
lcm-ray supply from `t₀ = h₀`: the returned `t` satisfies `h₀ ≤ t`, hence
`h₀ ∣ periodLcm t`, so `periodLcm t = (periodLcm t / h₀) * h₀` is a genuine
positive multiple of `h₀` and the very same survivor certificate answers the
multiple-period demand.  This is the antecedent-level form of the wave-22
one-parameter collapse. -/
theorem e_G102_G081 : G102 → G081 := by
  unfold G102 G081
  intro h h₀ hpos N₀
  obtain ⟨t, ht, N, hN, K, hkill⟩ := h h₀ N₀
  have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hpos ht
  refine ⟨periodLcm t / h₀,
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) hpos, N, hN, K, ?_⟩
  rwa [Nat.div_mul_cancel hdvd]

/-- **Diagonal ⟹ multiple-period** (composite of the two edges above).  The top
of the cluster-B chain reaches the bottom: `G081` is dominated by `G094`. -/
theorem e_G094_G081 : G094 → G081 :=
  fun h => e_G102_G081 (e_G094_G102 h)

end DemandLedger.ClusterB
