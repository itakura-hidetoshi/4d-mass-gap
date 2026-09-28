import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSourceUpdateSemantics
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceVacuumResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardLawResponseCrossResidual
import Mathlib.Tactic

/-!
# Quantitative cyclic source-update bridges

PR #4901 connects an actual member of the exact cyclic between-visits list to
the source-update semantic decomposition.  This file pushes the same geometric
fact through the already-closed quantitative backward machinery.

For every source in `suffix ++ pre`, PR #4899 supplies the required
off-diagonal hypothesis against the distinguished target.  Consequently:

* the centered backward direct variance is charged to the genuine source
  `CondExpL2` residual with the existing Harnack factor;
* the backward law-response is charged to the same genuine source residual
  with the established transposed coefficient
  `K_pin(source,target)^2`.

The two estimates are deliberately kept separate.  In particular, no
`(a+b)^2 <= 2a^2+2b^2` weakening, finite-cardinality Cauchy estimate,
response symmetry, target/source reversal, or new coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance cyclicSourceUpdateQuantitativeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance cyclicSourceUpdateQuantitativeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance cyclicSourceUpdateQuantitativeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance cyclicSourceUpdateQuantitativeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicSourceUpdateQuantitativeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance cyclicSourceUpdateQuantitativeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For an actual cyclic between-visits source, the existing centered backward
direct-variance estimate applies with its coefficient unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCyclicSourceUpdateBackwardDirectVarianceEnergy_currentValue_vacuum_lintegral_le_harnackLawFactor_mul_condExpL2_sourceResidual
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hFresh : target ∉ pre)
    (hsource : source ∈ suffix ++ pre)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ CD,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source.1 F C C distinguishedSource
            (C distinguishedSource) (C source.1) CD)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C source.1 distinguishedSource target.1
          (C distinguishedSource) (C source.1)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta source.1
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have hneSourceTarget : source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hSplit hFresh hsource
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_currentValue_vacuum_lintegral_le_harnackLawFactor_mul_condExpL2_sourceResidual
      H N hN beta hbeta distinguishedSource source.1 target.1
      hneSourceTarget F hF bound hbound

/-- For the same actual cyclic source, the law-response estimate keeps the
already-certified transposed orientation `K_pin(source,target)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCyclicSourceUpdateBackwardLawResponse_currentValue_vacuum_lintegral_le_transposedCanonicalPinFree_sq_mul_crossCondExpResidual
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix)
    (hFresh : target ∉ pre)
    (hsource : source ∈ suffix ++ pre)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ CD,
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
            H N hN beta hbeta source.1 F C C distinguishedSource
            (C distinguishedSource) (C source.1) CD) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
          H N hN beta hbeta C target.1 distinguishedSource target.1
          (C distinguishedSource) (C target.1)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence source.1 target.1) ^ 2) *
        ((1 -
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                s beta) ^ 2))⁻¹ *
          ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
            ENNReal.ofReal
              (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound -
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                    H N hN beta hbeta source.1
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                      H N hN beta hbeta F hF bound hbound)‖ ^ 2))) := by
  have hneSourceTarget : source.1 ≠ target.1 :=
    periodicHypercubicEvenFixedSpatialColorLink_cyclicBetweenVisits_source_ne_target
      H color pre suffix target source hSplit hFresh hsource
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_vacuum_lintegral_le_transposedCanonicalPinFree_sq_mul_crossCondExpResidual
      N hN s hs beta hbeta hcut H distinguishedSource source.1 target.1
      hneSourceTarget F hF bound hbound

end

end MGAP4D.MathlibAnalytic
