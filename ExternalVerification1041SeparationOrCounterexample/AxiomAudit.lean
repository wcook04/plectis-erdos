/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041SeparationOrCounterexample.Solution

/-!
# Axiom audit driver for the #1041 separation-or counterexample

Run this file under the pinned toolchain and read the printed axiom set. The
permitted budget in `comparator.json` is `propext`, `Quot.sound` and
`Classical.choice`; anything else, `sorryAx` above all, is a failure.
-/

#print axioms
  Erdos249257.ExternalVerification1041SeparationOrCounterexample.separation_or_counterexample
