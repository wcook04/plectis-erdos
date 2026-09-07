/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Deliberate negative fixture for periodic negative-orbit exclusion

Every declaration has an irrelevant extra argument and the wrong conclusion,
so Comparator must reject the module before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification243PeriodicNegativeOrbit

theorem no_phasePrimitivePeriodicNegative_orbit (_extra : True) : True := by
  trivial

theorem no_periodicNegative_orbit (_extra : True) : True := by
  trivial

theorem no_eventuallyPeriodicNegative_orbit (_extra : True) : True := by
  trivial

end Erdos249257.ExternalVerification243PeriodicNegativeOrbit
