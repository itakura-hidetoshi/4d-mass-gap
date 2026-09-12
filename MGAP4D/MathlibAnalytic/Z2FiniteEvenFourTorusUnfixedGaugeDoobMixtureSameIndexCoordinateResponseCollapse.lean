import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobMixtureSameIndexCoordinateResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Since the two latent residual-gauge laws are identical, their canonical
overlap coupling carries all of its mass on the diagonal. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_diagonalMass_eq_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right).diagonalMass = 1 := by
  have hDisagreement :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_zero
      C β hβ hβCutoff H left right
  unfold FiniteRealCouplingData.disagreementMass at hDisagreement
  linarith

/-- The exact diagonal latent average collapses to the same-index response
itself.  Thus the full geometric Doob-mixture coordinate mismatch is bounded
directly by the disagreement-set Hamming-dual response, without any remaining
latent-index factor. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_disagreementResponseSum
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target := by
  let responseSum :=
    ∑ target ∈ finiteProductDisagreementFinset left right,
      finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target
  have hBound :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_sameIndexDisagreementResponseSum
      C β hβ hβCutoff H left right source
      kernel iterations hDomination
  have hDiagonal :
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g) = 1 := by
    simpa [FiniteRealCouplingData.diagonalMass] using
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_diagonalMass_eq_one
        C β hβ hβCutoff H left right
  calc
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * responseSum := by
      simpa [responseSum] using hBound
    _ =
        (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
            C β hβ hβCutoff H left right).joint g g) * responseSum := by
      rw [Finset.sum_mul]
    _ = responseSum := by rw [hDiagonal, one_mul]
    _ =
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target := by
      rfl

/-- The uniform same-index response therefore controls the full exact-marginal
geometric Doob mixture directly by the original boundary Hamming magnitude. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_response_mul_hamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
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
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      response * finiteProductHammingDistanceReal left right := by
  let bound := response * finiteProductHammingDistanceReal left right
  have hWeighted :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_sameIndexResponseMulHamming
      C β hβ hβCutoff H left right source
      kernel iterations hDomination response hResponse
  have hDiagonal :
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g) = 1 := by
    simpa [FiniteRealCouplingData.diagonalMass] using
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_diagonalMass_eq_one
        C β hβ hβCutoff H left right
  calc
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * bound := by
      simpa [bound] using hWeighted
    _ =
        (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
            C β hβ hβCutoff H left right).joint g g) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by rw [hDiagonal, one_mul]
    _ = response * finiteProductHammingDistanceReal left right := by rfl

/-- For boundary configurations differing at at most one displayed link, the
full geometric Doob-mixture coordinate mismatch is bounded directly by the
uniform response coefficient. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_response_of_agreeOff
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff left right target)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (response : ℝ)
    (hResponseNonneg : 0 ≤ response)
    (hResponse :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target ≤ response) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤ response := by
  calc
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch
        C β hβ hβCutoff H left right source ≤
      response * finiteProductHammingDistanceReal left right :=
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_response_mul_hamming
          C β hβ hβCutoff H left right source
          kernel iterations hDomination response hResponse
    _ ≤ response * 1 :=
      mul_le_mul_of_nonneg_left
        (finiteProductHammingDistanceReal_le_one_of_agreeOff
          left right target hAgree)
        hResponseNonneg
    _ = response := by ring

end

end MathlibAnalytic
end MGAP4D
