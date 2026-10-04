import MGAP4D.MathlibAnalytic.ContinuousLinearMapContractionPowerPerturbation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovTimeZeroAdjacentDefectZero
import Mathlib.Tactic

/-!
# Adjacent common-transfer perturbation control for SU(2) Krylov defects

The adjacent common-marginal construction places the consecutive-scale
normalized physical pair transfers on one finite Hilbert space.  The generic
contraction perturbation theorem then gives, for every natural time m,

  d_n^{m,k}
    <= d_n^{0,k}
       + m ||A_n^L - A_n^R||.

Under the existing coherent readout, d_n^{0,k} is eventually zero and hence
summable.  Therefore a single summability assumption on the adjacent
common-transfer mismatch

  Summable (fun n => ||A_n^L - A_n^R||)

theorem-generates summability of every fixed-time first-three Krylov adjacent
defect, and hence the existing strong-limit machinery.

This isolates the remaining model-facing H1-C3 frontier to quantitative decay
of the adjacent physical transfer mismatch itself.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentPerturbTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentPerturbCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentPerturbSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentPerturbMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentPerturbBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentPerturbSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentPerturbSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentPerturbNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentCommonTransferPerturbation

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

/-- The evolved adjacent Krylov defect is bounded by the time-zero initial-mode
mismatch plus natural time times the common-transfer operator mismatch. -/
theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_le_zero_add_nat_mul_commonTransferMismatch
    (n m : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k ≤
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k +
        (m : ℝ) *
          ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ := by
  let A := physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n
  let B := physicalYangMillsSU2AdjacentCommonRightTransfer Q R n
  let x := physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k
  let y := physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k
  have hA : ‖A‖ ≤ 1 := by
    simpa [A] using
      physicalYangMillsSU2AdjacentCommonLeftTransfer_opNorm_le_one Q R n
  have hB : ‖B‖ ≤ 1 := by
    simpa [B] using
      physicalYangMillsSU2AdjacentCommonRightTransfer_opNorm_le_one Q R n
  have hy : ‖y‖ ≤ 1 := by
    simpa [y] using
      le_of_eq
        (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode_norm
          Q R n k)
  have hpert :=
    continuousLinearMap_contraction_pow_apply_sub_pow_apply_norm_le
      A B hA hB m x y hy
  have hm :
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n m k =
        ‖(A ^ m) x - (B ^ m) y‖ := by
    simpa [A, B, x, y] using
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_eq_commonTransferPowerDifference
        Q R n m k
  have hzero :
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n 0 k =
        ‖x - y‖ := by
    simpa [A, B, x, y] using
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_eq_commonTransferPowerDifference
        Q R n 0 k
  rw [hm, hzero]
  simpa [A, B] using hpert

/-- A single scale-summability input for the adjacent common-transfer operator
mismatch.  It is independent of natural time and of the three-mode index. -/
structure PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput where
  mismatch_summable :
    Summable
      (fun n =>
        ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
          physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖)

namespace PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput

variable
    (M :
      PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput
        (Q := Q) (R := R))

include M

/-- Under coherent time-zero readout, summable adjacent transfer mismatch
implies summability of every fixed-time first-three adjacent Krylov defect. -/
theorem adjacentDefect_summable
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (m : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
          (Q := Q) (R := R) n m k) := by
  have hzero :
      Summable
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
            (Q := Q) (R := R) n 0 k) :=
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_zero_summable
      Q R L hInvariant C k
  have hmismatch :
      Summable
        (fun n =>
          (m : ℝ) *
            ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
              physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖) :=
    M.mismatch_summable.mul_left (m : ℝ)
  have hmajorant :
      Summable
        (fun n =>
          physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
              (Q := Q) (R := R) n 0 k +
            (m : ℝ) *
              ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
                physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖) :=
    hzero.add hmismatch
  refine Summable.of_nonneg_of_le
    (fun n => ?_)
    (fun n =>
      physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_le_zero_add_nat_mul_commonTransferMismatch
        Q R n m k)
    hmajorant
  unfold physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
  unfold physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
  exact norm_nonneg _

/-- Summable adjacent common-transfer mismatch theorem-generates the #5098
adjacent-defect summability package. -/
noncomputable def toFiniteAdjacentKrylovSummableInput
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput
      (Q := Q) (R := R) where
  adjacentDefect_summable :=
    adjacentDefect_summable Q R L M hInvariant C

/-- Hence summable adjacent common-transfer mismatch gives all fixed-natural-time
strong limits for the theorem-generated norm-one three-mode excitation. -/
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
                  (toFiniteAdjacentKrylovSummableInput
                    Q R L M hInvariant C))
                m cInf)) := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R L M hInvariant C)
      hInvariant

/-- The same hypothesis retains the previously proved uniform q0^m decay. -/
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
                    (toFiniteAdjacentKrylovSummableInput
                      Q R L M hInvariant C))
                  m cInf)) ∧
            ‖PhysicalYangMillsSU2ThreeModeEvolvedBasisCoherenceInput.continuumSynthesis
                Q R L
                (PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.toEvolvedBasisCoherenceInput
                  Q R L
                  (toFiniteAdjacentKrylovSummableInput
                    Q R L M hInvariant C))
                m cInf‖ ≤
              GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m := by
  exact
    PhysicalYangMillsSU2ThreeModeFiniteAdjacentKrylovSummableInput.physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_evolved_strong_limits_q0
      Q R L
      (toFiniteAdjacentKrylovSummableInput Q R L M hInvariant C)
      hInvariant s hs hcut

end PhysicalYangMillsSU2AdjacentCommonTransferMismatchSummableInput

end AdjacentCommonTransferPerturbation

end

end MathlibAnalytic
end MGAP4D
