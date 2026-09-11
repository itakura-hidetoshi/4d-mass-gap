import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory
open scoped ENNReal

noncomputable section

/-- On a compact finite-measure space whose measure is positive on every
nonempty open set, the canonical continuous-function map into `Lᵖ` preserves
linear independence.

Mathlib already proves that `ContinuousMap.toLp` is injective under exactly the
full-support hypothesis `Measure.IsOpenPosMeasure`.  Linear independence is
therefore transported by the injective linear map, with no representative-level
or almost-everywhere argument required here. -/
theorem continuousMap_toLp_linearIndependent
    {α ι : Type*}
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
    (v : ι → C(α, ℝ))
    (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ
      (fun i => ContinuousMap.toLp (E := ℝ) p μ ℝ (v i)) := by
  have h := hv.map_injOn
    (ContinuousMap.toLp (E := ℝ) p μ ℝ).toLinearMap
    (ContinuousMap.toLp_injective (E := ℝ) (p := p) (𝕜 := ℝ) μ).injOn
  simpa [Function.comp_def] using h

end

end MathlibAnalytic
end MGAP4D
