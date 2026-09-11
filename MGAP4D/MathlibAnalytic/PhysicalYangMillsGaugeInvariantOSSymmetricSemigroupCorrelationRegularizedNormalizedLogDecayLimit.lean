import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassTelescoping

/-!
# Normalized endpoint logarithmic decay of the regularized physical OS correlation

The Cesàro averages of the sampled regularized effective masses converge to the
canonical long-time effective-mass limit.  The exact telescoping identity
identifies the finite Cesàro numerator with the endpoint difference of the
regularized logarithmic correlation.  Combining the two therefore gives the
long-time normalized endpoint logarithmic decay rate directly.

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

/-- The normalized endpoint decay of the regularized log correlation converges
to the same canonical long-time regularized effective-mass limit as the sampled
secant decay rates. -/
theorem physicalCorrelationRealClampRegularizedNormalizedLogEndpoint_tendsto_effectiveMassLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : P.PhysicalHilbert)
    {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ))⁻¹ *
          ((T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
              T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) / h))
      atTop
      (𝓝 (T.physicalCorrelationRealClampRegularizedEffectiveMassLimit psi ε h)) := by
  simpa only [physicalCorrelationRealClampRegularizedEffectiveMassSequence_sum_eq_log_endpoint]
    using
      T.physicalCorrelationRealClampRegularizedEffectiveMassSequence_cesaro_tendsto_limit
        hSymmetric psi hε hh

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
