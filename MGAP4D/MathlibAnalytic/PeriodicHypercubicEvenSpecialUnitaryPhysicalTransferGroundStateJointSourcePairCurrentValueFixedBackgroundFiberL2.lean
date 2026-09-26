import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import Mathlib.Tactic

/-!
# Current-value fixed-background source-pair fiber L2

PR #4821 keeps the outer physical background `A` outside the source-pair
fiber L2 norm and therefore retains the exact coefficient
`K_A(target,source)`.

This file specializes the remaining continuous-vacuum reference parameters to
their current values for one canonical kernel-section configuration `C`:

  B  = C,
  k  = C(distinguishedSource),
  g₂ = C(source).

The outer background `A` is deliberately *not* specialized.  It remains the
variable consumed by the PR #4773 outer transpose Schur receiver.

Under this current-value specialization the fixed-background source-pair law
is exactly the product of two copies of the genuine kernel-section source-link
conditional probability measure at `A`.  Thus the source-pair fiber carrier
is now written on the same physical kernel-section law used by the closed
localPart / target-residual chain, while the response coefficient remains the
actual `K_A(target,source)`.

No new probability law, comparison constant, pin-free replacement, factor
two, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueFixedBackgroundFiberL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance currentValueFixedBackgroundFiberL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance currentValueFixedBackgroundFiberL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance currentValueFixedBackgroundFiberL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueFixedBackgroundFiberL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance currentValueFixedBackgroundFiberL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At current reference values, the PR #4820 fixed-background source-pair
measure is literally the product of two genuine kernel-section source-link
conditional laws at the same outer background A. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure_diagonalCurrentValues_eq_kernelSectionSourcePair
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
        H N hN beta hbeta C A distinguishedSource source
        (C distinguishedSource) (C source) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A source).prod
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A source) := by
  unfold
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairMeasure
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalIndependentPairKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A source distinguishedSource source]

/-- Current-value specialization of the fixed-background source-specific fiber
L2 carrier.  It remains source-dependent but target-independent. -/
abbrev
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedBackgroundSourcePairL2
    H N hN beta hbeta C A distinguishedSource
    (C distinguishedSource) (C source) source

/-- Current-value concrete target-law response on the fixed-background
source-pair fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
      H N hN beta hbeta C A distinguishedSource source :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2
    H N hN beta hbeta C A distinguishedSource source target
    (C distinguishedSource) (C source)
    F hF bound hbound left 0

/-- Current-value final second-law-mean RMS amplitude on the same
fixed-background source-pair fiber. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
      H N hN beta hbeta C A distinguishedSource source :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeFixedBackgroundL2
    H N hN beta hbeta C A distinguishedSource source target
    (C distinguishedSource) (C source)
    F hF bound hbound left

/-- Current-value fixed-background response estimate with the actual physical
envelope and final second-law-mean RMS.

The same outer background A appears in both the source-pair fiber carrier and
the coefficient K_A(target,source), which is the compatibility required before
feeding pointwise source-dependent data into PR #4819. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        F hF bound hbound left‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        F hF bound hbound left‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeFixedBackgroundL2_norm
      N hN s hs beta hbeta hcut H C A distinguishedSource source target
      (C distinguishedSource) (C source)
      F hF bound hbound left

end

end MGAP4D.MathlibAnalytic
