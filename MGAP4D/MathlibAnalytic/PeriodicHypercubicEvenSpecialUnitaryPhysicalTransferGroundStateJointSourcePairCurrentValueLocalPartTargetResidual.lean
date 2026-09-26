import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueLocalPartFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumSecondMeanRMSTargetMajorant
import Mathlib.Tactic

/-!
# Current-value localPart energy equals the genuine target residual

PR #4824 lifts the PR #4736 diagonal source local mean to a constant vector in
the current-value fixed-background source-pair L2 carrier.

At current reference values the old reference heat-bath law is exactly the
genuine fixed-right kernel-section law by PR #4797.  Hence the scalar local
mean is pointwise

  F(C,A) - integral_g F(C, A[source <- g]) d kappa_{C,A,source}.

Consequently, integrating the squared norm of the PR #4824 fiber localPart
over the outer kernel-section background A gives exactly the PR #4813
source-independent target residual energy with target = source.

A second outer vacuum integration is therefore exactly the already-canonical
fiber variance, and the existing coefficient-one CondExpL2 theorem closes the
localPart energy bound.

No remote-link witness, comparison constant, response coefficient, factor two,
or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueLocalPartTargetResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance currentValueLocalPartTargetResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance currentValueLocalPartTargetResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance currentValueLocalPartTargetResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueLocalPartTargetResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance currentValueLocalPartTargetResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At current reference values, the PR #4736 diagonal local mean is exactly
the genuine kernel-section source-link conditional-expectation residual at the
same outer background A. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean_eq_kernelSectionResidual
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
        H N hN beta hbeta C A distinguishedSource source F =
      F (C, A) -
        ∫ g,
          F (C, Function.update A source g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A source := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (C, D)
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean_eq_value_sub_heatBathIntegral
      H N hN beta hbeta source F hF bound hbound
      C C A distinguishedSource (C distinguishedSource) (C source)]
  change
    F (C, A) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
          H N hN beta hbeta C source distinguishedSource source
          (C distinguishedSource) (C source) rightF A =
      F (C, A) -
        ∫ g,
          F (C, Function.update A source g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
            H N hN beta hbeta C A source
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A source distinguishedSource source
      rightF hRightStrong]

/-- For one fixed vacuum-side configuration C, the outer-A energy of the
current-value source-pair localPart is exactly the source-indexed genuine
kernel-section residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_sq_lintegral_eq_targetKernelSectionResidualEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source F‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C source F := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
  apply lintegral_congr
  intro A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_sq_eq,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean_eq_kernelSectionResidual
      H N hN beta hbeta C A distinguishedSource source
      F hF bound hbound]

/-- Vacuum integration of the current-value fiber localPart energy is exactly
the canonical source fiber variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ A,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source F‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source F := by
  calc
    (∫⁻ C,
      ∫⁻ A,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source F‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C source F
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_sq_lintegral_eq_targetKernelSectionResidualEnergy
          H N hN beta hbeta C distinguishedSource source
          F hF bound hbound
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
        H N hN beta hbeta source F := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
          H N hN beta hbeta source F hF bound hbound

/-- Coefficient-one global localPart bound in the genuine joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_vacuum_lintegral_le_condExpL2_residual_norm_sq
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C,
      ∫⁻ A,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source F‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) ≤
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta source
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_vacuum_lintegral_eq_canonicalFiberVarianceFunctional
      H N hN beta hbeta distinguishedSource source F hF bound hbound]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional_le_condExpL2_residual_norm_sq
      H N hN beta hbeta source F hF bound hbound

end

end MGAP4D.MathlibAnalytic
