/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic
import ErdosProblems.DemandLedger.edges.ClusterA
import ErdosProblems.DemandLedger.edges.ClusterB
import ErdosProblems.DemandLedger.edges.ClusterC
import ErdosProblems.DemandLedger.edges.ClusterD
import ErdosProblems.DemandLedger.edges.ClusterE
import ErdosProblems.DemandLedger.edges.ClusterF
import ErdosProblems.DemandLedger.edges.Bridge1
import ErdosProblems.DemandLedger.edges.Bridge2
import ErdosProblems.DemandLedger.edges.Bridge3
import ErdosProblems.DemandLedger.edges.Discharge1_G097
import ErdosProblems.DemandLedger.edges.Discharge2_G100
import ErdosProblems.DemandLedger.edges.Discharge3_G103

/-!
# Demand ledger: the open antecedents as first-class objects, and their order

`docs/semantic/frontier.json` records the open antecedents of #249 and #257 in
prose. Each one is in fact already a Lean `Prop`: it is the type of a named
hypothesis binder on a `conditional_implication` theorem, where nothing can
address it. `ErdosProblems/DemandLedger/Hyp.lean` provides `hypOf%`, which lifts
such a binder into a named constant taken straight from the kernel's own
`ConstantInfo` — extracted, never transcribed.

`Basic` holds the 101 closed antecedents obtained that way from the 259
conditional-implication declarations. The `edges` modules hold the implication
order over the 23 substantial ones.

The order collapses them into 7 equivalence classes. The largest, 14 antecedents
of #249, is equivalent to #249 itself (`DemandLedger.G103_iff_erdos249`, resting
on the corpus theorem `irrational_totient_series_iff_pointwise_certificates`).
The three #257 antecedents `G073 ≡ G075 ≡ G076` are likewise equivalent to
`1/2 ∈ mersenneAchievementSet`, via
`half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse`.

No recorded antecedent is *weaker* than the problem it is an antecedent of. Six
are strictly stronger so far as the proved edges go — see the caveat in
`docs/semantic/frontier.json::demand_lattice.limits`: an absent edge is unproved,
not refuted, so the separations are not established.
-/
