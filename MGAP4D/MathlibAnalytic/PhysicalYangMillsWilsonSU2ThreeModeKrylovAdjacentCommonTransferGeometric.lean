import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransferPerturbation
import Mathlib.Tactic

/-!
# Geometric decay of the adjacent common-transfer mismatch

PR #5103 reduces fixed-natural-time SU(2) Krylov strong-limit existence to
summability of one operator-valued refinement mismatch:

  n ↦ ‖A_n^L - A_n^R‖.

This file packages the quantitative geometric form needed by the model-facing
route.  If there are constants C >= 0 and 0 <= q < 1 such that

  ‖A_n^L - A_n^R‖ <= C q^n

for every refinement scale n, then the operator mismatch is summable.  The
#5103 perturbation bridge therefore theorem-generates summability of every
fixed-time first-three Krylov adjacent defect, all corresponding strong limits,
and the already-established q0^m continuum decay.

The remaining H1-C3 model-facing frontier is thus the single pointwise estimate
on the actual adjacent common-marginal physical transfers.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentGeometricTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentGeometricCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentGeometricSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentGeometricMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentGeometricBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentGeometricSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentGeometricSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentGeometricNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentCommonTransferGeometric

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)

/-- Geometric scale control of the one remaining adjacent common-transfer
operator mismatch. -/
structure PhysicalYangMillsSU2AdjacentCommonTransferMismatchGeometricInput where
  prefactor : ℝ
  ratio : ℝ
  prefactor_nonneg : 0 ≤ prefactor
  ratio_nonneg : 0 ≤ ratio
  ratio_lt_one : ratio < 1
  mismatch_le_geometric :
    ∀ n : ℕ,
      ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ ≤
      prefactor * ratio ^ n

namespace PhysicalYangMillsSU2AdjacentCommonTransferMismatchGeometricInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentCommonTransferMismatchGeometricInput
        (Q := Q) (R := R))

include G

/-- The geometric operator-mismatch majorant is summable. -/
theorem majorant_summable :
    Summable (fun n : ℕ => G.prefactor * G.ratio ^ n) := by
  exact
    (summable_geometric_of_lt_one G.ratio_nonneg G.ratio_lt_one).mul_left
      G.prefactor

/-- Geometric operator mismatch implies scale summability of the actual
adjacent common-transfer mismatch. -/
theorem mismatch_summable :
    Summable
      (fun n =>
        ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖) := by
  refine Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (fun n => G.mismatch_le_geometric n)
    (majorant_summable Q R G)

/-- Geometric common-transfer control produces the #5103 summability package. -/
noncomputable def toMismatchSummableInput :
    PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput
      (Q := Q) (R := R) where
  mismatch_summable := mismatch_summable Q R G

/-- Geometric adjacent common-transfer decay theorem-generates all fixed
natural-time strong limits of the exact norm-one three-mode excitation. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
            (fun j =>
              physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                Q R L hInvariant (phi j) m)
            atTop
            (𝓝
              (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toMismatchSummableInput Q R G) hInvariant C))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L (toMismatchSummableInput Q R G) hInvariant C

/-- The same geometric mismatch estimate retains the existing uniform q0^m
decay after passage to the continuum. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        ∀ m : ℕ,
          Tendsto
              (fun j =>
                physicalYangMillsVacuumNormalizedSU2ThreeModeEvolvedProjectiveContinuumImage
                  Q R L hInvariant (phi j) m)
              atTop
              (𝓝
                (PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                  Q R L
                  (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                    Q R L
                    (PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                      Q R L (toMismatchSummableInput Q R G) hInvariant C))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput.toFiniteAdjacentKrylovSummableInput
                    Q R L (toMismatchSummableInput Q R G) hInvariant C))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L (toMismatchSummableInput Q R G) hInvariant C s hs hcut

end PhysicalYangMillsSU2AdjacentCommonTransferMismatchGeometricInput

end AdjacentCommonTransferGeometric

end

end MathlibAnalytic
end MGAP4D
