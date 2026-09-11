import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalDobrushinL1Matrix
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualHighTemperatureContinuation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualParallelCoupling
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- The actual high-temperature continuation supplies a common strict bound
for both rows and columns of the canonical posterior influence matrix.  This
is the bidirectional package required by the correct-marginal parallel
coupling; its row projection is the existing Dobrushin package from PR #1390. -/
noncomputable def toBidirectionalDobrushinData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightBidirectionalDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) := by
  let F := C.continuationFamily β hβ hβCutoff
  let weight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment
  let D := finitePositiveWeightCanonicalNonstrictL1MatrixData weight
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy
  let boundaryTarget : FiniteEvenFourTorusSpatialLink H :=
    Classical.choice
      (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
  have hEndpoint := F.endpoint_envelopeCoefficients_lt H
  have hEntry
      (target source : FiniteEvenFourTorusSpatialLink H) :
      finitePositiveWeightCanonicalNonstrictInfluence
          weight target source ≤ kernel.influence target source := by
    have hDominates :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        H β energyIdentity energyNontrivial hβ hEnergy
        environment boundaryTarget (environment boundaryTarget)
        target source
    simpa [weight, kernel] using hDominates
  refine D.toBidirectionalDobrushinL1MatrixData
    F.barrier F.barrier_nonneg ?_ ?_ F.barrier_lt_one
  · intro target
    calc
      finitePositiveWeightNonstrictInfluenceRowSum D target ≤
          finiteInfluenceKernelRowSum kernel target := by
        unfold finitePositiveWeightNonstrictInfluenceRowSum
          finiteInfluenceKernelRowSum D
        apply Finset.sum_le_sum
        intro source _hSource
        exact hEntry target source
      _ ≤ finiteInfluenceKernelMaximumRowSum kernel :=
        finiteInfluenceKernelRowSum_le_maximum kernel target
      _ ≤ F.barrier := le_of_lt (by
        simpa [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient,
          kernel] using hEndpoint.1)
  · intro source
    calc
      finitePositiveWeightNonstrictInfluenceColumnSum D source ≤
          finiteInfluenceKernelColumnSum kernel source := by
        unfold finitePositiveWeightNonstrictInfluenceColumnSum
          finiteInfluenceKernelColumnSum D
        apply Finset.sum_le_sum
        intro target _hTarget
        exact hEntry target source
      _ ≤ finiteInfluenceKernelMaximumColumnSum kernel :=
        finiteInfluenceKernelColumnSum_le_maximum kernel source
      _ ≤ F.barrier := le_of_lt (by
        simpa [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient,
          kernel] using hEndpoint.2)

/-- The actual posterior weight used by the parallel coupling is strictly
positive throughout the continuation interval. -/
theorem posteriorWeight_pos
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (_hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      environment hidden :=
  finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
    H β energyIdentity energyNontrivial hβ hEnergy environment hidden

/-- Canonical correct-marginal coupling of two actual parallel posterior
resampling kernels at fixed observed boundary environment. -/
noncomputable def parallelOverlapCouplingData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealCouplingData
      (finitePositiveWeightParallelProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        leftHidden)
      (finitePositiveWeightParallelProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        rightHidden) :=
  finitePositiveWeightParallelOverlapCouplingData
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    leftHidden rightHidden

/-- If the two hidden input slices differ only at one spatial link, the actual
correct-marginal parallel coupling has total coordinate disagreement bounded
by the common high-temperature barrier. -/
theorem parallelTotalCoordinateDisagreement_le_barrier
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff leftHidden rightHidden source) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        leftHidden rightHidden ≤
      (C.continuationFamily β hβ hβCutoff).barrier := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  exact B.parallelTotalCoordinateDisagreement_le_coefficient
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    leftHidden rightHidden source hAgree

/-- Consequently every single-link input discrepancy is strictly contracted by
one actual parallel posterior update. -/
theorem parallelTotalCoordinateDisagreement_lt_one
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment leftHidden rightHidden :
      FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff leftHidden rightHidden source) :
    finitePositiveWeightParallelTotalCoordinateDisagreement
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        leftHidden rightHidden < 1 := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  exact B.parallelTotalCoordinateDisagreement_lt_one
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    leftHidden rightHidden source hAgree

end Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Canonical all-volume actual bidirectional Dobrushin data throughout the
high-temperature interval selected in PR #1390. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureBidirectionalDobrushinData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightBidirectionalDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).toBidirectionalDobrushinData
    β hβ hβCutoff H environment

end

end MathlibAnalytic
end MGAP4D
