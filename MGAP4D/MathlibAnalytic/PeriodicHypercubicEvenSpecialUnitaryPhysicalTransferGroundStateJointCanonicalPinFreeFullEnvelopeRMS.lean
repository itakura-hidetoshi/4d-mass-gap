import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageContextUniformFullEnvelopeRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import Mathlib.Tactic

/-!
# Configuration-independent canonical pin-free RMS envelope

The stagewise RMS spine currently uses the physical left envelope
`K_A(target,source)`, whose remote entry depends on the background
configuration `A`.  The source-pair L2 carrier from PR #4724 integrates over
that background, so the coefficient must first be replaced by a
configuration-independent majorant before it can leave the L2 norm.

The canonical fixed-right response profile already provides exactly such a
majorant.  This file proves pointwise

  K_A(target,source) <= K_pin(target,source),

where `K_pin` is the existing pin-free response-controlled physical kernel
built from the canonical fixed-right profile.

Active pairs are identical: both kernels use the same local Harnack
coefficient and the source-aligned remote residual vanishes there.  Remote
pairs use the exact identification of the physical residual with the
worst-case cross-ratio majorant, followed by the canonical uniform response
profile bound.

Consequently every existing full-envelope centered RMS estimate immediately
holds with the same configuration-independent `K_pin` coefficient.

No new response coefficient, no cardinality estimate, and no new probability
law are introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance canonicalPinFreeFullEnvelopeRMSSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalPinFreeFullEnvelopeRMSSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalPinFreeFullEnvelopeRMSSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalPinFreeFullEnvelopeRMSSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalPinFreeFullEnvelopeRMSSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalPinFreeFullEnvelopeRMSSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every background-dependent physical-envelope entry is bounded by the
configuration-independent pin-free kernel generated from the canonical
fixed-right response profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_le_canonicalPinFree
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source := by
  classical
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  have hRNonneg : ∀ t s, 0 ≤ R t s := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta
  have hUniform :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_uniformBound
        H N hN beta hbeta
  by_cases hEq : target = source
  · subst target
    have hLeft :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence_diagonal_zero source
    have hRight :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta R hRNonneg).influence_diagonal_zero source
    simpa [R, hLeft, hRight]
  · by_cases hActive :
        target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
    · have hResidualZero :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_zero_of_active
          H N hN beta hbeta A source target hActive
      change
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
          else 0) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source target ≤
          (if target = source then 0
            else if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
            else Real.exp (16 * beta) * R target source)
      rw [if_pos hActive, hResidualZero, if_neg hEq, if_pos hActive]
      norm_num
    · have hResidualEq :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_worstCase_of_remote
          H N hN beta hbeta A source target hEq hActive
      have hMajorant :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
              H N hN beta hbeta A target source ≤
            Real.exp (16 * beta) * R target source :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_of_responseBound
          H N hN beta hbeta A target source
          (R target source) (hRNonneg target source)
          (fun g₁ g₂ h k => hUniform A target source g₁ g₂ h k)
      change
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
          else 0) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source target ≤
          (if target = source then 0
            else if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
            else Real.exp (16 * beta) * R target source)
      rw [if_neg hActive, hResidualEq, if_neg hEq, if_neg hActive, zero_add]
      exact hMajorant

/-- Configuration-independent version of the physical full-envelope centered
RMS property, using the canonical pin-free kernel. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) : Prop :=
  ∀ (source : PeriodicHypercubicEvenSpatialSliceLink H),
    target ≠ source →
    ∀ (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
      |(∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂
            (Function.update A source u)) -
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N target F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource target k g₂
            (Function.update A source v))| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
          Real.sqrt
            ((∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N target F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B source distinguishedSource target k g₂
                  (Function.update A source u)) +
              ∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N target F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B source distinguishedSource target k g₂
                  (Function.update A source v))

/-- Any full physical-envelope RMS certificate upgrades, pointwise and without
loss, to the configuration-independent canonical pin-free coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS_of_fullEnvelope
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ)
    (hFull :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionFullEnvelopeCenteredRMS
        H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS
      H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center := by
  intro source hne u v
  have hBase := hFull source hne u v
  have hCoeff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_le_canonicalPinFree
      H N hN beta hbeta A target source
  have hSqrt : 0 ≤
      Real.sqrt
        ((∫ g,
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained g - center) ^ 2
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B source distinguishedSource target k g₂
              (Function.update A source u)) +
          ∫ g,
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained g - center) ^ 2
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B source distinguishedSource target k g₂
              (Function.update A source v)) :=
    Real.sqrt_nonneg _
  exact hBase.trans (mul_le_mul_of_nonneg_right hCoeff hSqrt)

/-- Bounded concrete sections on the strict physical-sweep interval satisfy the
configuration-independent canonical pin-free centered RMS estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS_of_bounded
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS
      H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionCanonicalPinFreeCenteredRMS_of_fullEnvelope
      H N hN beta hbeta target F left B A retained distinguishedSource k g₂ center
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_fullEnvelopeCenteredRMS_of_bounded
      N hN s hs beta hbeta hcut H target
      F hF bound hbound left B A retained distinguishedSource k g₂ center

end

end MathlibAnalytic
end MGAP4D
