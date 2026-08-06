import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingKantorovichWeakDuality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorComponentHammingLipschitzResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact disagreement-set response sum is a finite Hamming dual transport
bound between two posterior component laws carrying the same residual-gauge
index. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_hammingDualBound_disagreementResponseSum
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
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H right g).HammingDualBound
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H left g)
      (∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target) := by
  intro f hLipschitz
  exact
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzExpectation_difference_abs_le_disagreementResponseSum
      C β hβ hβCutoff H g left right f hLipschitz
      kernel iterations hDomination

/-- A uniform one-coordinate response envelope gives a same-index Hamming
dual transport bound proportional to the original boundary Hamming distance. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_hammingDualBound_response_mul_hamming
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
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target ≤ response) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H right g).HammingDualBound
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H left g)
      (response * finiteProductHammingDistanceReal left right) := by
  intro f hLipschitz
  exact
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzExpectation_difference_abs_le_response_mul_hamming
      C β hβ hβCutoff H g left right f hLipschitz
      kernel iterations hDomination response hResponse

/-- A strict uniform response coefficient yields strict same-index contraction
on the dual side of finite Hamming transport.  No primal coupling existence or
geometric one-slab spectral-gap identification is asserted here. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_strictHammingDualContraction
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
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target ≤ response)
    (hResponseLt : response < 1) :
    response < 1 ∧
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right g).HammingDualBound
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left g)
        (response * finiteProductHammingDistanceReal left right) := by
  exact ⟨hResponseLt,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_hammingDualBound_response_mul_hamming
      C β hβ hβCutoff H g left right kernel iterations
      hDomination response hResponse⟩

end

end MathlibAnalytic
end MGAP4D
