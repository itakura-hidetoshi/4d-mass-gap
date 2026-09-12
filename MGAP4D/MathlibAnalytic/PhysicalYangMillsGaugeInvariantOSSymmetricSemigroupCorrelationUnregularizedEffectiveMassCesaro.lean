import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMassLimitBounds
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Cesàro convergence of unregularized physical OS effective masses

For a nonzero completed physical state and fixed positive sampling step `h`, the
unregularized physical OS effective-mass sequence converges to its canonical
long-time infimum.  Mathlib's Cesàro theorem therefore gives the same limit for
the arithmetic means of the sampled secant decay rates.

This is the averaging half of the unregularized telescoping identification with
long-time logarithmic correlation decay.  No fixed positive additive
regularization, differentiability, spectral theorem, new decay estimate, or
additional physical assumption is introduced.
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

/-- The Cesàro averages of the fixed-step unregularized physical OS effective
masses converge to the same long-time effective-mass limit. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_cesaro_tendsto_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ∑ i ∈ Finset.range n,
            T.physicalCorrelationRealClampEffectiveMassSequence psi h i)
      atTop
      (𝓝 (T.physicalCorrelationRealClampEffectiveMassLimit psi h)) := by
  exact
    (T.physicalCorrelationRealClampEffectiveMassSequence_tendsto_limit
      hSymmetric hpsi hh).cesaro

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
