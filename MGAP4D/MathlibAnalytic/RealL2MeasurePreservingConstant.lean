import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pullback along a measure-preserving map fixes the canonical constant-one
vector in real `L²`.

This is a purely Mathlib measure-theoretic fact.  It will identify all finite
Wilson vacuum vectors after their interacting boundary marginal realizations
have been normalized to constant one. -/
theorem realL2_compMeasurePreserving_const_one
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : α → β)
    (hf : MeasurePreserving f μ ν) :
    Lp.compMeasurePreservingₗᵢ ℝ f hf (Lp.const 2 ν (1 : ℝ)) =
      Lp.const 2 μ (1 : ℝ) := by
  change Lp.compMeasurePreserving f hf (Lp.const 2 ν (1 : ℝ)) =
    Lp.const 2 μ (1 : ℝ)
  rw [← indicatorConstLp_univ, ← indicatorConstLp_univ]
  simpa using
    (Lp.indicatorConstLp_compMeasurePreserving
      (p := (2 : ENNReal))
      (μ := μ) (μb := ν) (f := f)
      MeasurableSet.univ (measure_ne_top ν Set.univ) (1 : ℝ) hf)

end

end MathlibAnalytic
end MGAP4D
