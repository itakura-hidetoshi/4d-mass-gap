import MGAP4D.Basic
import MGAP4D.Axioms
import MGAP4D.Certificates

namespace MGAP4D

/-!
# The 33/20 Gap Interface

This file is the initial Lean landing point for the MGAP4D normalized mass-gap
statement. At this migration stage it records the target theorem shape without
claiming more formalized content than the current repository contains.
-/

/-- Internal normalized value of the MGAP4D gap target. -/
def gap3320 : Rat := 33 / 20

/-- Minimal computable check for the normalized gap value. -/
theorem gap3320_eq : gap3320 = 33 / 20 := by
  rfl

end MGAP4D
