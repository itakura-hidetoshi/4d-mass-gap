import MGAP4D.MathlibAnalytic.FiniteRealProbabilityExpectation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorObservablePathResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Expectation under one normalized residual-gauge Perron-smoothed component
law is exactly the normalized Perron posterior global expectation at the
correspondingly transformed boundary environment. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData_expectation_eq_globalExpectation
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H environment g).expectation f =
      finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
        H β energyIdentity energyNontrivial hβ hEnergy
        (g • environment) f := by
  unfold
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
    finitePositiveWeightMixtureComponentProbabilityData
  rw [finiteRealWeightProbabilityData_expectation_eq_globalExpectation_of_proofs]
  rfl

/-- For a fixed residual-gauge component index, arbitrary boundary
configurations are compared by summing the exact observable response envelope
only over their original disagreement set. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_disagreementResponseSum
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left g).expectation f| ≤
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := by
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData_expectation_eq_globalExpectation
      C β hβ hβCutoff H right g f,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData_expectation_eq_globalExpectation
      C β hβ hβCutoff H left g f]
  have hBound :=
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_difference_abs_le_disagreementResponseSum
      H β energyIdentity energyNontrivial hβ hEnergy
      (g • left) (g • right) f P kernel iterations hDomination
  rw [finiteProductDisagreementFinset_residualGauge_smul H g left right]
    at hBound
  exact hBound

/-- A uniform one-coordinate observable response envelope gives a fixed-index
component expectation bound proportional to the original boundary Hamming
distance. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_response_mul_hamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (response : ℝ)
    (hResponse :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target P.variation ≤ response) :
    |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left g).expectation f| ≤
      response * finiteProductHammingDistanceReal left right := by
  rw [
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData_expectation_eq_globalExpectation
      C β hβ hβCutoff H right g f,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData_expectation_eq_globalExpectation
      C β hβ hβCutoff H left g f]
  exact
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_sameResidualGauge_difference_abs_le_response_mul_hamming
      H β energyIdentity energyNontrivial hβ hEnergy
      g left right f P kernel iterations hDomination response hResponse

end

end MathlibAnalytic
end MGAP4D
