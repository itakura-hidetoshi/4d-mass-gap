import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumResponseEnergyMatrix
import Mathlib.Tactic

/-!
# Vacuum response amplitude matrix

PR #4817 packages the physical-vacuum response energies as a finite ordered-pair
matrix and proves, off the diagonal,

  E_resp(source,target)
    <= ofReal(K_pin(target,source)^2) * M_target,

where M_target is source-independent.

The normed response assemblers and transpose Schur receivers are stated in
amplitudes rather than squared energies.  This file therefore takes the exact
nonnegative square roots.

We define

  A_resp(source,target) = sqrt(toReal(E_resp(source,target)))

and

  U_target(target) = sqrt(toReal(M_target)).

On the existing strict physical-sweep interval M_target is finite because the
feedback gap is positive.  Hence ENNReal.toReal is monotone on the PR #4817
bound, and

  A_resp(source,target) <= K_pin(target,source) * U_target(target)

for every ordered pair, including the zero diagonal.

No new estimate, cutoff, response coefficient, factor two, or cardinality
factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance vacuumResponseAmplitudeMatrixSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumResponseAmplitudeMatrixSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumResponseAmplitudeMatrixSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumResponseAmplitudeMatrixSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumResponseAmplitudeMatrixSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumResponseAmplitudeMatrixSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Source-independent real target amplitude obtained from the PR #4817
ENNReal target majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant
        H N hN s beta hbeta target F hF bound hbound))

/-- Real square-root amplitude of one global response-energy matrix entry. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseEnergyMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound source target))

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude_nonneg
    (H N : ℕ) (hN : 0 < N)
    (s beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta target F hF bound hbound := by
  exact Real.sqrt_nonneg _

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_nonneg
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound source target := by
  exact Real.sqrt_nonneg _

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_diag
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound
        source source = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix]

/-- The target majorant is finite on the existing strict physical-sweep
interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant_ne_top
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant
        H N hN s beta hbeta target F hF bound hbound ≠ ⊤ := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  let gap : ℝ≥0∞ := 1 - c
  have hc : c < 1 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
        s beta hbeta hcut
  have hGapPos : 0 < gap := by
    simpa [gap] using (tsub_pos_iff_lt.mpr hc)
  have hGapZero : gap ≠ 0 := ne_of_gt hGapPos
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant
  change
    gap⁻¹ *
        ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound)‖ ^ 2)) ≠ ⊤
  apply ENNReal.mul_ne_top
  · exact ENNReal.inv_ne_top.2 hGapZero
  · apply ENNReal.mul_ne_top
    · exact
        ENNReal.add_ne_top.2
          ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
    · exact ENNReal.ofReal_ne_top

/-- Off-diagonal square-root form of the PR #4817 response-energy matrix
bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude_of_ne
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound
        source target ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta target F hF bound hbound := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let E : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseEnergyMatrix
      H N hN beta hbeta distinguishedSource F hF bound hbound source target
  let M : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant
      H N hN s beta hbeta target F hF bound hbound
  have hEnergy : E ≤ ENNReal.ofReal ((K.influence target source) ^ 2) * M := by
    simpa [E, M, K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseEnergyMatrix_le_canonicalPinFree_sq_ofReal_mul_targetMajorant_of_ne
        N hN s hs beta hbeta hcut H distinguishedSource source target hne
        F hF bound hbound
  have hMTop : M ≠ ⊤ := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetMajorant_ne_top
        N hN s hs beta hbeta hcut H target F hF bound hbound
  have hRhsTop :
      ENNReal.ofReal ((K.influence target source) ^ 2) * M ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hMTop
  have hToReal :
      E.toReal ≤
        (ENNReal.ofReal ((K.influence target source) ^ 2) * M).toReal :=
    ENNReal.toReal_mono hRhsTop hEnergy
  have hToReal' :
      E.toReal ≤ (K.influence target source) ^ 2 * M.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at hToReal
    exact hToReal
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound
        source target =
      Real.sqrt E.toReal := by
        rfl
    _ ≤ Real.sqrt ((K.influence target source) ^ 2 * M.toReal) :=
      Real.sqrt_le_sqrt hToReal'
    _ =
      Real.sqrt ((K.influence target source) ^ 2) *
        Real.sqrt M.toReal := by
      rw [Real.sqrt_mul (sq_nonneg _)]
    _ =
      K.influence target source * Real.sqrt M.toReal := by
      rw [Real.sqrt_sq hK0]
    _ =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta target F hF bound hbound := by
      rfl

/-- Receiver-ready all-pairs amplitude bound, with the diagonal handled by its
definitional zero response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix
        H N hN beta hbeta distinguishedSource F hF bound hbound
        source target ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta target F hF bound hbound := by
  by_cases hne : target = source
  · subst target
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_diag]
    exact
      mul_nonneg
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)).influence_nonneg source source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumSecondMeanRMSTargetAmplitude_nonneg
          H N hN s beta hbeta source F hF bound hbound)
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointVacuumResponseAmplitudeMatrix_le_canonicalPinFree_mul_targetAmplitude_of_ne
        N hN s hs beta hbeta hcut H distinguishedSource source target hne
        F hF bound hbound

end

end MGAP4D.MathlibAnalytic
