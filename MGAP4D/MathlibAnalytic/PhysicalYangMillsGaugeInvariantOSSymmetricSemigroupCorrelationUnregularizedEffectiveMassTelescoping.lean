import MGAP4D.MathlibAnalytic.EqualStepSecantDecayRateTelescoping
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationUnregularizedEffectiveMassCesaro

/-!
# Telescoping identity for unregularized physical OS effective masses

At fixed step `h`, the discrete unregularized physical OS effective mass is the
negative secant slope of the unregularized log correlation on `[nh, nh+h]`.
Therefore the sum of the first `n` sampled effective masses telescopes exactly
to the endpoint unregularized logarithmic decay.

This is the algebraic half of the epsilon-zero Cesàro/telescoping identification
of the long-time effective-mass limit.  No positivity assumption on `h` is
needed for the finite identity itself, and no new analytic or physical
assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace BigOperators

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The finite sum of equal-step unregularized physical OS effective masses is
exactly the endpoint unregularized logarithmic decay divided by the step. -/
theorem physicalCorrelationRealClampEffectiveMassSequence_sum_eq_log_endpoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    (h : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        T.physicalCorrelationRealClampEffectiveMassSequence psi h i =
      (T.physicalCorrelationRealClampLog psi 0 -
        T.physicalCorrelationRealClampLog psi ((n : ℝ) * h)) / h := by
  unfold physicalCorrelationRealClampEffectiveMassSequence
  unfold physicalCorrelationRealClampEffectiveMass
  exact
    MGAP4D.sum_range_secantDecayRate_equalStep
      (T.physicalCorrelationRealClampLog psi) h n

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
