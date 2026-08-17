import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassLimitBounds
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Cesàro convergence of regularized physical OS effective masses

For fixed positive regularization `ε` and positive sampling step `h`, the
sampled regularized physical OS effective-mass sequence converges to its
canonical long-time infimum.  Mathlib's Cesàro theorem therefore gives the same
limit for the arithmetic means of the sampled secant decay rates.

This is the averaging half of the later telescoping identification with the
long-time logarithmic decay of the regularized correlation.

No differentiability, spectral theorem, new decay estimate, or additional
physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter
open scoped Topology InnerProductSpace BigOperators

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The Cesàro averages of the fixed-step regularized physical OS effective
masses converge to the same long-time effective-mass limit. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_cesaro_tendsto_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range n,
            T.physicalCorrelationRealClampRegularizedEffectiveMassSequence
              psi ε h i)
      atTop
      (𝓝 (T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h)) := by
  exact
    (T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_tendsto_limit
      hSymmetric psi hε hh).cesaro

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
