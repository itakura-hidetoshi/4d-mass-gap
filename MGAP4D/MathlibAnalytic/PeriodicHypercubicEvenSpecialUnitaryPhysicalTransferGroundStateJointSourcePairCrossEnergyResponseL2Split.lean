import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairResponseSquareOrderedL2
import Mathlib.Tactic

/-!
# Global first-cross energy split with the response term in L2

PR #4783 proves the exact ordered-law decomposition

  firstCrossEnergy
    = integral (oldTargetVariance + response^2).

PR #4784 identifies the ordered response-square integral exactly with the
squared norm of the already-existing source-pair target-law response vector in

  L2(nu_source).

This file composes those two exact identities.  The resulting global formula is

  firstCrossEnergy
    = integral oldTargetVariance
      + ofReal (||responseL2||^2).

No inequality is introduced.  In particular, there is no factor two, no
cardinality loss, and no new influence coefficient.  The only genuinely new
analytic term left after this theorem is the ordered old-target-law variance.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairCrossEnergyResponseL2SplitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairCrossEnergyResponseL2SplitSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairCrossEnergyResponseL2SplitSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairCrossEnergyResponseL2SplitSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairCrossEnergyResponseL2SplitSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairCrossEnergyResponseL2SplitSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact global first-cross decomposition with the response-square contribution
expressed as the actual source-pair response L2 norm-square.

The remaining integral is only the old-target-law variance energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_firstVariance_lintegral_add_responseL2_norm_sq_ofReal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      (∫⁻ Cv,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) +
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) := by
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let varianceTerm :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun Cv =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
  let responseSq :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun Cv =>
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
            H N hN beta hbeta target source F left B distinguishedSource
            k g₂ 0
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
              H N source Cv)) ^ 2)
  have hOrderedResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left
  have hResponseSq : Measurable responseSq := by
    have h :
        Measurable
          (fun Cv =>
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
                  H N hN beta hbeta B distinguishedSource source target k g₂
                  F left Cv) ^ 2)) :=
      ENNReal.continuous_ofReal.measurable.comp
        (hOrderedResponse.measurable.pow_const 2)
    simpa [
      responseSq,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse] using h
  calc
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫⁻ Cv, varianceTerm Cv + responseSq Cv ∂rho := by
        simpa [varianceTerm, responseSq, rho] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_firstVariance_add_responseSq
            H N hN beta hbeta B distinguishedSource source target hne k g₂
            F hF bound hbound left
    _ =
      (∫⁻ Cv, varianceTerm Cv ∂rho) +
        ∫⁻ Cv, responseSq Cv ∂rho := by
      exact lintegral_add_right varianceTerm hResponseSq
    _ =
      (∫⁻ Cv, varianceTerm Cv ∂rho) +
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
              H N hN beta hbeta B distinguishedSource source target k g₂
              F hF bound hbound left 0‖ ^ 2) := by
      rw [
        show
          (∫⁻ Cv, responseSq Cv ∂rho) =
            ENNReal.ofReal
              (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                  H N hN beta hbeta B distinguishedSource source target k g₂
                  F hF bound hbound left 0‖ ^ 2) by
            simpa [responseSq, rho] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseSq_lintegral_eq_responseL2_norm_sq_ofReal
                H N hN beta hbeta B distinguishedSource source target hne k g₂
                F hF bound hbound left]
    _ =
      (∫⁻ Cv,
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂) +
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) := by
      rfl

end

end MGAP4D.MathlibAnalytic
