import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseAmplitude
import Mathlib.Tactic

/-!
# Fixed-background target amplitudes as genuine target residual energy

PR #4833 defines the fixed-C source-independent target majorant

  M_target(C,target)
    = gap(s,beta)^(-1) * (K_H(beta) + 1) * E_target(C,target),

and PR #4836 defines its real square-root amplitude

  U_target^C(target) = sqrt(toReal(M_target(C,target))).

On the strict physical-sweep interval the target majorant is finite for every
bounded concrete observable.  Therefore taking the square root and returning
through ENNReal.ofReal loses no information:

  ofReal((U_target^C(target))^2) = M_target(C,target).

For a link-indexed family F_target this file sums the identity over target and
factors out the common source-independent scalar coefficient.  The resulting
exact formula reconnects the target-amplitude profile used by the pin-free
Schur step to the genuine kernel-section target residual energy.

No inequality, source summation, finite-cardinality factor, or new response
coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundTargetAmplitudeResidualSumSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Common ENNReal coefficient multiplying the fixed-C genuine target residual
energy in the deweighted second-mean RMS target majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
    (s beta : ℝ) : ℝ≥0∞ :=
  (1 -
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta) ^ 2))⁻¹ *
    (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1)

/-- The fixed-C target majorant is exactly the common scalar coefficient times
the genuine target kernel-section residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_eq_coefficient_mul_targetResidualEnergy
    (H N : ℕ) (hN : 0 < N)
    (s beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient,
    mul_assoc]

/-- For a bounded concrete representative, taking the real square root of the
finite target majorant and returning through ENNReal.ofReal is exact. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude_sq_ofReal_eq_targetMajorant
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta C target F ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F := by
  let M : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
      H N hN s beta hbeta C target F
  have hMTop : M ≠ ⊤ := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_ne_top
        N hN s hs beta hbeta hcut H C target F hF bound hbound
  have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  calc
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
        H N hN s beta hbeta C target F ^ 2) =
      ENNReal.ofReal ((Real.sqrt M.toReal) ^ 2) := by
        rfl
    _ = ENNReal.ofReal M.toReal := by
      rw [Real.sq_sqrt hM0]
    _ = M :=
      ENNReal.ofReal_toReal_eq_iff.mpr hMTop
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F := by
      rfl

/-- For a link-indexed family, ENNReal.ofReal of the finite sum of squared
fixed-C target amplitudes is exactly the sum of the corresponding target
majorants. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetAmplitude_sq_sum_ofReal_eq_targetMajorant_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    ENNReal.ofReal
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target (F target) ^ 2) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
          H N hN s beta hbeta C target (F target) := by
  rw [
    ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (f := fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target (F target) ^ 2)
      (fun target _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro target htarget
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude_sq_ofReal_eq_targetMajorant
      N hN s hs beta hbeta hcut H C target
      (F target) (hF target) (bound target) (hbound target)

/-- The sum of link-indexed fixed-C target majorants factors exactly into the
common target-majorant coefficient times the sum of genuine target residual
energies. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetMajorant_sum_eq_coefficient_mul_targetResidualEnergy_sum
    (H N : ℕ) (hN : 0 < N)
    (s beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target (F target)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
            H N hN beta hbeta C target (F target) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target htarget
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant_eq_coefficient_mul_targetResidualEnergy
      H N hN s beta hbeta C target (F target)

/-- Exact link-indexed fixed-C target-amplitude energy in terms of genuine
kernel-section target residual energies. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetAmplitude_sq_sum_ofReal_eq_coefficient_mul_targetResidualEnergy_sum
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    ENNReal.ofReal
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetAmplitude
          H N hN s beta hbeta C target (F target) ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
          s beta *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
            H N hN beta hbeta C target (F target) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetAmplitude_sq_sum_ofReal_eq_targetMajorant_sum
      N hN s hs beta hbeta hcut H C F hF bound hbound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundSecondMeanRMSTargetMajorant_sum_eq_coefficient_mul_targetResidualEnergy_sum
      H N hN s beta hbeta C F]

end

end MGAP4D.MathlibAnalytic
