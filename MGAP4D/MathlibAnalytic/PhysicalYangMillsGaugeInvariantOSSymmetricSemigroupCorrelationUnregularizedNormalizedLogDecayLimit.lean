import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMassTelescoping

/-!
# Normalized endpoint logarithmic decay of the unregularized physical OS correlation

For a nonzero completed physical state, the Cesàro averages of the sampled
unregularized effective masses converge to the canonical fixed-step long-time
limit.  The exact telescoping identity identifies the finite Cesàro numerator
with the endpoint difference of the unregularized logarithmic correlation.
Combining them gives the normalized endpoint logarithmic decay rate directly.

No fixed positive additive regularization, differentiability, spectral theorem,
new decay estimate, or additional physical assumption is introduced.
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

/-- The normalized endpoint decay of the unregularized log correlation
converges to the same canonical long-time effective-mass limit as the sampled
secant decay rates. -/
theorem physicalCorrelationRealClampNormalizedLogEndpoint_tendsto_effectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    {h : ℝ} (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ((T.physicalCorrelationRealClampLog psi 0 -
              T.physicalCorrelationRealClampLog psi ((n : ℝ) * h)) / h))
      atTop
      (𝓝 (T.physicalCorrelationRealClampEffectiveMassLimit psi h)) := by
  simpa only [physicalCorrelationRealClampEffectiveMassSequence_sum_eq_log_endpoint]
    using
      T.physicalCorrelationRealClampEffectiveMassSequence_cesaro_tendsto_limit
        hSymmetric hpsi hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
