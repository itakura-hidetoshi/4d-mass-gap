import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

/-- A real Borel function equipped with an explicit uniform bound for the
standalone PVM integration construction. -/
structure PVMBoundedBorelRealFunction where
  toFun : ℝ → ℝ
  measurable_toFun : Measurable toFun
  bounded_toFun : ∃ C : ℝ, ∀ t : ℝ, ‖toFun t‖ ≤ C

/-- The constant-one bounded Borel function. -/
def pvmBoundedBorelOne : PVMBoundedBorelRealFunction where
  toFun := fun _ => 1
  measurable_toFun := measurable_const
  bounded_toFun := ⟨1, by intro t; simp⟩

/-- Indicator of a measurable real set as a bounded Borel function. -/
def pvmBoundedBorelIndicator
    (s : Set ℝ) (hs : MeasurableSet s) :
    PVMBoundedBorelRealFunction := by
  classical
  exact
    { toFun := fun t => if t ∈ s then 1 else 0
      measurable_toFun :=
        Measurable.ite hs measurable_const measurable_const
      bounded_toFun := by
        refine ⟨1, ?_⟩
        intro t
        by_cases ht : t ∈ s <;> simp [ht] }

/-- Difference of two bounded Borel functions. -/
def pvmBoundedBorelSub
    (f g : PVMBoundedBorelRealFunction) :
    PVMBoundedBorelRealFunction where
  toFun := fun t => f.toFun t - g.toFun t
  measurable_toFun := f.measurable_toFun.sub g.measurable_toFun
  bounded_toFun := by
    obtain ⟨Cf, hf⟩ := f.bounded_toFun
    obtain ⟨Cg, hg⟩ := g.bounded_toFun
    refine ⟨Cf + Cg, ?_⟩
    intro t
    calc
      ‖f.toFun t - g.toFun t‖ ≤ ‖f.toFun t‖ + ‖g.toFun t‖ :=
        norm_sub_le _ _
      _ ≤ Cf + Cg := add_le_add (hf t) (hg t)

end

end MathlibAnalytic
end MGAP4D
