import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureNormalizationIdentity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- A jointly a.e.-measurable family of nonnegative Doob weights whose fiber
masses are positive and finite almost everywhere admits an everywhere-defined
Markov-kernel representative.  The representative is required to agree, for
outer-almost every parameter, with the literal normalized `doobWeightedMeasure`
of the original fiber weight.

This is the generic measurable-kernel bridge used by the ground-state one-link
split.  It makes no RCD or disintegration claim by itself. -/
theorem exists_doobWeightedMarkovKernel_ae_eq
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    (μ : Measure α)
    (ν : Measure β)
    [SFinite ν]
    (w : α → β → ℝ≥0∞)
    (hw : AEMeasurable (Function.uncurry w) (μ.prod ν))
    (hμ : μ ≠ 0)
    (hMass : ∀ᵐ a ∂μ,
      0 < doobWeightMass ν (w a) ∧ doobWeightMass ν (w a) < ∞) :
    ∃ κ : Kernel α β,
      IsMarkovKernel κ ∧
        ∀ᵐ a ∂μ, κ a = doobWeightedMeasure ν (w a) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
