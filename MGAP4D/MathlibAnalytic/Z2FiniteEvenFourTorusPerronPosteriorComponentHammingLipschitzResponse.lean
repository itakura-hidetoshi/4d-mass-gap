import MGAP4D.MathlibAnalytic.FiniteProductHammingLipschitzVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorComponentObservableResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One-coordinate posterior response error for the unit variation profile
shared by every Hamming `1`-Lipschitz observable. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
    H β energyIdentity energyNontrivial
    kernel iterations target (fun _ => 1)

/-- The Hamming-Lipschitz unit-profile response error is nonnegative. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    0 ≤
      finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target := by
  unfold
    finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
  exact
    finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel iterations target (fun _ => 1) (fun _ => by norm_num)

/-- For one fixed residual-gauge component index, every Hamming
`1`-Lipschitz observable is controlled by the exact sum of unit-profile
response errors over the boundary disagreement set. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzExpectation_difference_abs_le_disagreementResponseSum
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
    (hLipschitz : FiniteProductHammingOneLipschitz f)
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
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target := by
  let P : FiniteProductVariationBound f :=
    finiteProductHammingOneLipschitzVariationBound f hLipschitz
  have hBound :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_disagreementResponseSum
      C β hβ hβCutoff H g left right f P
      kernel iterations hDomination
  simpa [P,
    finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError]
    using hBound

/-- A uniform unit-profile response envelope controls every Hamming
`1`-Lipschitz observable between same-index posterior components by the
boundary Hamming distance. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzExpectation_difference_abs_le_response_mul_hamming
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
    (hLipschitz : FiniteProductHammingOneLipschitz f)
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
    |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left g).expectation f| ≤
      response * finiteProductHammingDistanceReal left right := by
  let P : FiniteProductVariationBound f :=
    finiteProductHammingOneLipschitzVariationBound f hLipschitz
  have hResponseP :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target P.variation ≤ response := by
    intro target
    simpa [P,
      finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError]
      using hResponse target
  exact
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_response_mul_hamming
      C β hβ hβCutoff H g left right f P
      kernel iterations hDomination response hResponseP

/-- Public same-index dual Hamming-response package: one common response
constant controls every Hamming `1`-Lipschitz observable.  This is a finite
Gibbs-law comparison statement and is not yet an identification with a
geometric one-slab transport contraction. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzResponsePackage
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
    ∀ f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ,
      FiniteProductHammingOneLipschitz f →
      |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H right g).expectation f -
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H left g).expectation f| ≤
        response * finiteProductHammingDistanceReal left right := by
  intro f hLipschitz
  exact
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentHammingOneLipschitzExpectation_difference_abs_le_response_mul_hamming
      C β hβ hβCutoff H g left right f hLipschitz
      kernel iterations hDomination response hResponse

end

end MathlibAnalytic
end MGAP4D
