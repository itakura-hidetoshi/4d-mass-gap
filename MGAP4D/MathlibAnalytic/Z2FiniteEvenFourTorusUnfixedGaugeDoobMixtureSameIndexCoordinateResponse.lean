import MGAP4D.MathlibAnalytic.FiniteRealProbabilityHammingDualCoordinateCoupling
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorComponentHammingDualTransport
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobMixtureIndexUniformity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact Hamming-dual disagreement response controls one displayed
coordinate of the canonical same-index posterior overlap coupling.  This is
the primal coordinate form of the previously integrated dual response bound. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch_le_disagreementResponseSum
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
    (source : FiniteEvenFourTorusSpatialLink H)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
        C β hβ hβCutoff H left right g g source ≤
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target := by
  let P :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H left g
  let Q :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H right g
  have hDual :
      P.HammingDualBound Q
        (∑ target ∈ finiteProductDisagreementFinset left right,
          finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target) :=
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_hammingDualBound_disagreementResponseSum
      C β hβ hβCutoff H g left right kernel iterations hDomination).symm
  have h :=
    P.overlapCouplingData_expectedFiniteProductCoordinateMismatch_le_of_hammingDualBound
      Q hDual source
  simpa [P, Q,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData]
    using h

/-- A uniform response envelope controls every displayed coordinate of the
same-index posterior overlap coupling by the original boundary Hamming
magnitude. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch_le_response_mul_hamming
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
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch
        C β hβ hβCutoff H left right g g source ≤
      response * finiteProductHammingDistanceReal left right := by
  let P :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H left g
  let Q :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H right g
  have hDual :
      P.HammingDualBound Q
        (response * finiteProductHammingDistanceReal left right) :=
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponent_hammingDualBound_response_mul_hamming
      C β hβ hβCutoff H g left right kernel iterations
      hDomination response hResponse).symm
  have h :=
    P.overlapCouplingData_expectedFiniteProductCoordinateMismatch_le_of_hammingDualBound
      Q hDual source
  simpa [P, Q,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch,
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData]
    using h

/-- After exact elimination of latent residual-gauge disagreement, the full
geometric Doob-mixture coordinate mismatch is bounded by the diagonal average
of the exact same-index Hamming-dual response. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_sameIndexDisagreementResponseSum
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
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g *
          (∑ target ∈ finiteProductDisagreementFinset left right,
            finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
              H β energyIdentity energyNontrivial
              kernel iterations target) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal
      C β hβ hβCutoff H left right source
      (fun _g =>
        ∑ target ∈ finiteProductDisagreementFinset left right,
          finiteEvenFourTorusZ2PerronPosteriorHammingOneLipschitzKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target)
      (fun g =>
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch_le_disagreementResponseSum
          C β hβ hβCutoff H g left right source
          kernel iterations hDomination)

/-- The corresponding uniform-response bound for the full exact-marginal
geometric Doob mixture.  The only remaining weights are diagonal latent-index
weights; no latent-index mismatch term survives. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_sameIndexResponseMulHamming
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
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g *
          (response * finiteProductHammingDistanceReal left right) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedCoordinateMismatch_le_diagonal
      C β hβ hβCutoff H left right source
      (fun _g => response * finiteProductHammingDistanceReal left right)
      (fun g =>
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedCoordinateMismatch_le_response_mul_hamming
          C β hβ hβCutoff H g left right source
          kernel iterations hDomination response hResponse)

end

end MathlibAnalytic
end MGAP4D
