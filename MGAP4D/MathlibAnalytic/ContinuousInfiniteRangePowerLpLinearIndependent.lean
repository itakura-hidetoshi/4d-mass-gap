import MGAP4D.MathlibAnalytic.ContinuousMapToLpLinearIndependent
import MGAP4D.MathlibAnalytic.InfiniteRangePowerFamilyLinearIndependent

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A continuous real-valued function with infinite range has linearly
independent powers already in the continuous-function space. -/
theorem continuousMap_infiniteRange_powerFamily_linearIndependent
    {α : Type*}
    [TopologicalSpace α]
    (f : C(α, ℝ))
    (hf : (Set.range fun x => f x).Infinite) :
    LinearIndependent ℝ (fun n : ℕ => f ^ n) := by
  rw [linearIndependent_iff'ₛ]
  intro s a b hab i hi
  have hfun :=
    infiniteRange_powerFamily_linearIndependent (fun x : α => f x) hf
  rw [linearIndependent_iff'ₛ] at hfun
  apply hfun s a b
  · funext x
    have hx := congrArg (fun g : C(α, ℝ) => g x) hab
    simpa using hx
  · exact hi

/-- On a compact full-support finite-measure space, the power family of an
infinite-range continuous real function remains linearly independent after the
canonical Mathlib quotient into `Lᵖ`.

This is the exact composition of the algebraic infinite-range theorem with
`ContinuousMap.toLp_injective`. -/
theorem continuousMap_infiniteRange_powerFamily_toLp_linearIndependent
    {α : Type*}
    [TopologicalSpace α]
    [MeasurableSpace α]
    [BorelSpace α]
    [CompactSpace α]
    [SecondCountableTopologyEither α ℝ]
    {μ : Measure α}
    [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    (f : C(α, ℝ))
    (hf : (Set.range fun x => f x).Infinite) :
    LinearIndependent ℝ
      (fun n : ℕ => ContinuousMap.toLp (E := ℝ) p μ ℝ (f ^ n)) := by
  exact continuousMap_toLp_linearIndependent
    (v := fun n : ℕ => f ^ n)
    (continuousMap_infiniteRange_powerFamily_linearIndependent f hf)

end

end MathlibAnalytic
end MGAP4D
