import MGAP4D.MathlibAnalytic.EqualStepSecantDecayRateTelescoping
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationRegularizedEffectiveMassCesaro

/-!
# Telescoping identity for regularized physical OS effective masses

At fixed step `h`, the discrete regularized physical OS effective mass is the
negative secant slope of the regularized log correlation on `[nh,nh+h]`.
Therefore the sum of the first `n` sampled effective masses telescopes exactly
to the endpoint regularized logarithmic decay.

This is the algebraic half of the Cesàro/telescoping identification of the
long-time effective-mass limit.
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

/-- The finite sum of equal-step regularized physical OS effective masses is
exactly the endpoint regularized logarithmic decay divided by the step. -/
theorem physicalCorrelationRealClampRegularizedEffectiveMassSequence_sum_eq_log_endpoint
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    (ε h : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n,
        T.physicalCorrelationRealClampRegularizedEffectiveMassSequence
          psi ε h i =
      (T.physicalCorrelationRealClampRegularizedLog psi ε 0 -
        T.physicalCorrelationRealClampRegularizedLog psi ε ((n : ℝ) * h)) / h := by
  unfold physicalCorrelationRealClampRegularizedEffectiveMassSequence
  unfold physicalCorrelationRealClampRegularizedEffectiveMass
  exact
    MGAP4D.sum_range_secantDecayRate_equalStep
      (T.physicalCorrelationRealClampRegularizedLog psi ε) h n

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
