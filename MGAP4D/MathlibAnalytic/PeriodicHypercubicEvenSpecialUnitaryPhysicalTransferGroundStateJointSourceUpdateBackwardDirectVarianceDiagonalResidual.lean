import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairUpdatedVarianceReferenceResidual
import Mathlib.Tactic

/-!
# Diagonal backward direct variance as a genuine source one-link residual

PR #4869 transports the cross-background backward direct variance to the
diagonal source law.  This file identifies that diagonal variance exactly.

For a fixed background C, put

  Y(v) = F(left, C[source <- v]).

The backward direct observable is the translated-and-reflected variable

  F(left,C) - Y(v).

Centering removes the translation and squaring removes the reflection.
Therefore its centered variance is exactly the source-fiber variance of Y.
For bounded concrete representatives this gives the exact ENNReal identity

  ofReal BackwardDirectVarianceEnergy(C,C)
    =
  integral_sourceFiber
    ofReal((Y - P_source Y)^2).

The right-hand side is precisely the existing updated-background variance
carrier specialized to target = source.  Consequently the already-closed
reference-law residual theorem can be reused verbatim.

No Harnack factor, triangle inequality, factor two, source/target cardinality
factor, response symmetry, or new comparison coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardDirectVarianceDiagonalResidualSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardDirectVarianceDiagonalResidualSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardDirectVarianceDiagonalResidualSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardDirectVarianceDiagonalResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardDirectVarianceDiagonalResidualSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardDirectVarianceDiagonalResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- On the diagonal backward carrier, the centered direct-difference variance
is exactly the genuine source heat-bath residual on that one-link fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_ofReal_eq_referenceSourceResidual_fiberLIntegral_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)) =
      ∫⁻ v,
        ENNReal.ofReal
          ((F (left, Function.update C source v) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource source k g₂
                (fun D => F (left, D)) C) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂ C := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (left, D)
  let Y : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun v => rightF (Function.update C source v)
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
      H N hN beta hbeta B source distinguishedSource source k g₂ rightF
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  have hRightStrong : StronglyMeasurable rightF := by
    dsimp [rightF]
    exact hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hYStrong : StronglyMeasurable Y := by
    exact hRightStrong.comp_measurable (measurable_update C)
  have hYBound : ∀ v, ‖Y v‖ ≤ |bound| := by
    intro v
    exact (hbound (left, Function.update C source v)).trans (le_abs_self bound)
  have hYLp : MemLp Y 2 μ :=
    MemLp.of_bound hYStrong.aestronglyMeasurable |bound|
      (Filter.Eventually.of_forall hYBound)
  have hYInt : Integrable Y μ :=
    hYLp.integrable one_le_two
  have hConstInt :
      Integrable
        (fun _v : Matrix.specialUnitaryGroup (Fin N) ℂ => F (left, C)) μ :=
    integrable_const _
  have hProjection :
      P C = ∫ v, Y v ∂μ := by
    simpa [P, Y, rightF, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_eq_fiberIntegral
        H N hN beta hbeta B source distinguishedSource source k g₂
        rightF hRightStrong C
  have hMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
        F (left, C) - P C := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
    change
      (∫ v, (F (left, C) - Y v) ∂μ) =
        F (left, C) - P C
    rw [integral_sub hConstInt hYInt, integral_const, probReal_univ, one_smul]
    rw [hProjection]
  have hResidualLp :
      MemLp (fun v => Y v - P C) 2 μ :=
    hYLp.sub (memLp_const (P C))
  have hResidualSq :
      Integrable (fun v => (Y v - P C) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hResidualLp.integrable_sq
  have hEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
        ∫ v, (Y v - P C) ^ 2 ∂μ := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
      hMean]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [
      Y, rightF,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    ring
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)) =
      ENNReal.ofReal (∫ v, (Y v - P C) ^ 2 ∂μ) := by
        rw [hEnergy]
    _ =
      ∫⁻ v, ENNReal.ofReal ((Y v - P C) ^ 2) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal
          hResidualSq
          (ae_of_all μ fun v => sq_nonneg (Y v - P C))
    _ =
      ∫⁻ v,
        ENNReal.ofReal
          ((F (left, Function.update C source v) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource source k g₂
                (fun D => F (left, D)) C) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂ C := by
      rfl

/-- The diagonal backward direct variance is exactly the already-existing
updated-background variance carrier, specialized to target = source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_ofReal_eq_referenceSourceUpdatedBackgroundVarianceEnergy_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left C :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)) =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source source k g₂
          F left C) := by
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)) =
      ∫⁻ v,
        ENNReal.ofReal
          ((F (left, Function.update C source v) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource source k g₂
                (fun D => F (left, D)) C) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂ C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_ofReal_eq_referenceSourceResidual_fiberLIntegral_of_bounded
        H N hN beta hbeta B distinguishedSource source k g₂
        F hF bound hbound left C
    _ =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source source k g₂
          F left C) := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy_ofReal_eq_referenceTargetResidual_fiberLIntegral
          H N hN beta hbeta B distinguishedSource source source k g₂
          F hF bound hbound left C

/-- After integration over the source reference law, the diagonal backward
variance is exactly the genuine source heat-bath projection residual energy.
This reuses the closed stationarity/residual spine with target specialized to
source and introduces no new loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_reference_lintegral_eq_referenceSourceResidual_sq_lintegral_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ C,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂) =
      ∫⁻ C,
        ENNReal.ofReal
          ((F (left, C) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource source k g₂
                (fun D => F (left, D)) C) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
  calc
    (∫⁻ C,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C))
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂) =
      ∫⁻ C,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
            H N hN beta hbeta B distinguishedSource source source k g₂
            F left C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ := by
      apply lintegral_congr
      intro C
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_diagonal_ofReal_eq_referenceSourceUpdatedBackgroundVarianceEnergy_of_bounded
          H N hN beta hbeta B distinguishedSource source k g₂
          F hF bound hbound left C
    _ =
      ∫⁻ C,
        ENNReal.ofReal
          ((F (left, C) -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
                H N hN beta hbeta B source distinguishedSource source k g₂
                (fun D => F (left, D)) C) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_reference_updatedBackgroundVarianceEnergy_lintegral_eq_referenceTargetResidual_sq_lintegral
        H N hN beta hbeta B distinguishedSource source source k g₂
        F hF bound hbound left

end

end MGAP4D.MathlibAnalytic
