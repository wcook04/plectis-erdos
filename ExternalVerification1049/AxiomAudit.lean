/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1049.Solution

/-!
# Trust audit for the #1049 Comparator Solution

The `#print axioms` command below is an executable audit of the configured
Solution declaration. Its expected trust budget is the standard Lean core
set `propext`, `Quot.sound`, and `Classical.choice`; this audit does not turn
the numerical height inequality into an irrationality proof or a solution of
Erdős #1049.
-/

namespace Erdos249257.ExternalVerification1049

#print axioms comparator_sevenHalves_numericalHeight

end Erdos249257.ExternalVerification1049
