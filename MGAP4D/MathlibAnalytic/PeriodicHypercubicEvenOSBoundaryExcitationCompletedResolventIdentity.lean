import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedShiftedGeneratorResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The first resolvent identity for two bounded right/left inverses of real
shifts of the same bounded endomorphism.  The proof is purely algebraic. -/
theorem realContinuousLinearMap_shiftedInverse_resolvent_identity
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (G Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hlambda :
      Rlambda * (G - lambda • (1 : E →L[ℝ] E)) = 1)
    (hmu :
      (G - mu • (1 : E →L[ℝ] E)) * Rmu = 1) :
    Rlambda - Rmu =
      (lambda - mu) • (Rlambda * Rmu) := by
  have hshift :
      (G - mu • (1 : E →L[ℝ] E)) -
          (G - lambda • (1 : E →L[ℝ] E)) =
        (lambda - mu) • (1 : E →L[ℝ] E) := by
    module
  calc
    Rlambda - Rmu =
        Rlambda * ((G - mu • (1 : E →L[ℝ] E)) * Rmu) -
          (Rlambda * (G - lambda • (1 : E →L[ℝ] E))) * Rmu := by
      rw [hmu, hlambda, mul_one, one_mul]
    _ = Rlambda *
          ((G - mu • (1 : E →L[ℝ] E)) -
            (G - lambda • (1 : E →L[ℝ] E))) * Rmu := by
      noncomm_ring
    _ = Rlambda * ((lambda - mu) • (1 : E →L[ℝ] E)) * Rmu := by
      rw [hshift]
    _ = (lambda - mu) • (Rlambda * Rmu) := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc]

/-- Norm form of the first resolvent identity. -/
theorem realContinuousLinearMap_shiftedInverse_resolvent_identity_norm
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (G Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hlambda :
      Rlambda * (G - lambda • (1 : E →L[ℝ] E)) = 1)
    (hmu :
      (G - mu • (1 : E →L[ℝ] E)) * Rmu = 1) :
    ‖Rlambda - Rmu‖ =
      |lambda - mu| * ‖Rlambda * Rmu‖ := by
  rw [realContinuousLinearMap_shiftedInverse_resolvent_identity
    G Rlambda Rmu lambda mu hlambda hmu]
  simp only [norm_smul, Real.norm_eq_abs]

local instance osBoundaryExcitationCompletedResolventIdentitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedResolventIdentitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedResolventIdentitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedResolventIdentitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedResolventIdentitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedResolventIdentitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedResolventIdentitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedResolventIdentityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Exact first resolvent identity for the completed below-gap shifted Green
family. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda mu : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hmu :
      mu <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda -
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta mu hmu =
      (lambda - mu) •
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta mu hmu) := by
  exact
    realContinuousLinearMap_shiftedInverse_resolvent_identity
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta mu hmu)
      lambda mu
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreen_mul_generator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
        H N hN beta hbeta mu hmu)

/-- Exact operator-norm form of the completed first resolvent identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub_norm_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda mu : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hmu :
      mu <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda -
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta mu hmu‖ =
      |lambda - mu| *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta mu hmu‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub]
  simp only [norm_smul, Real.norm_eq_abs]

/-- The below-gap Green family is quantitatively Lipschitz, with the sharp
product of inverse spectral distances furnished by the coercive bounds. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda mu : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (hmu :
      mu <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda -
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta mu hmu‖ ≤
      |lambda - mu| *
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - lambda)⁻¹ *
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - mu)⁻¹) := by
  let Rlambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
      H N hN beta hbeta lambda hlambda
  let Rmu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
      H N hN beta hbeta mu hmu
  have hRlambda :
      ‖Rlambda‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
      H N hN beta hbeta lambda hlambda
  have hRmu :
      ‖Rmu‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - mu)⁻¹ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
      H N hN beta hbeta mu hmu
  have hinvLambda :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hlambda.le)
  have hproduct :
      ‖Rlambda‖ * ‖Rmu‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - lambda)⁻¹ *
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
              H N hN beta hbeta - mu)⁻¹ :=
    mul_le_mul hRlambda hRmu (norm_nonneg Rmu) hinvLambda
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub_norm_eq]
  calc
    |lambda - mu| * ‖Rlambda * Rmu‖ ≤
        |lambda - mu| * (‖Rlambda‖ * ‖Rmu‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le Rlambda Rmu) (abs_nonneg _)
    _ ≤
        |lambda - mu| *
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
                H N hN beta hbeta - lambda)⁻¹ *
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
                H N hN beta hbeta - mu)⁻¹) :=
      mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)

/-- Audit-visible first-resolvent-identity and quantitative regularity package
for the completed below-gap Green family. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventIdentityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  firstResolventIdentity :
    ∀ (lambda mu : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (hmu :
        mu <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta mu hmu =
        (lambda - mu) •
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
              H N hN beta hbeta lambda hlambda *
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
              H N hN beta hbeta mu hmu)
  resolventLipschitzBound :
    ∀ (lambda mu : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (hmu :
        mu <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta mu hmu‖ ≤
        |lambda - mu| *
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
                H N hN beta hbeta - lambda)⁻¹ *
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
                H N hN beta hbeta - mu)⁻¹)

/-- Construct the completed below-gap first-resolvent-identity package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedResolventIdentityPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedResolventIdentityPackage
      H N hN beta hbeta :=
  { firstResolventIdentity :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub
        H N hN beta hbeta
    resolventLipschitzBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_sub_norm_le
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D