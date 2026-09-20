import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackExponentialWeightedRow
import Mathlib.Tactic

/-!
# Response-controlled weighted row and the distinguished-target pin obstruction

For a response profile R, a weighted row bound controls the transpose-oriented
mass needed for spatial response decay. The response-controlled physical
kernel then splits into the local Harnack row, the response feedback row, and
one explicit distinguished-target pin.

Away from the distinguished target the pin vanishes exactly. At the
distinguished target the remaining obstruction is eta(beta) times the total
growing spatial weight. No closure or hidden uniformity is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance responseControlledWeightedRowPinObstructionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedRowBound
    (H : ℕ)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (responseCoefficient : ℝ) : Prop :=
  ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      R target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      responseCoefficient *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le_local_add_pin_add_response
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center distinguishedTarget target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseRow :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedRowBound
        H s center R responseCoefficient) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
          H beta hbeta distinguishedTarget R hRNonneg).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target +
      (if target = distinguishedTarget then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center source
      else 0) := by
  classical
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeightNonneg : ∀ source, 0 ≤ W source := by
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg center source
  have hPointwise :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
            H beta hbeta distinguishedTarget R hRNonneg).influence target source *
            W source ≤
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence target source +
            (if target = distinguishedTarget then eta else 0) +
            Real.exp (16 * beta) * R target source) *
            W source := by
    intro source
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [eta] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_le_local_add_targetPin_add_response
            H beta hbeta distinguishedTarget target source R hRNonneg)
      (hWeightNonneg source)
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
      H beta hbeta s hs center target
  have hResponse := hResponseRow target
  have hExpNonneg : 0 ≤ Real.exp (16 * beta) := (Real.exp_pos _).le
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
          H beta hbeta distinguishedTarget R hRNonneg).influence target source *
        W source) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence target source +
          (if target = distinguishedTarget then eta else 0) +
          Real.exp (16 * beta) * R target source) * W source := by
        exact Finset.sum_le_sum fun source _ => hPointwise source
    _ =
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source * W source) +
      (if target = distinguishedTarget then
        eta * ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, W source
      else 0) +
      Real.exp (16 * beta) *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          R target source * W source) := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        by_cases hDist : target = distinguishedTarget
        · rw [if_pos hDist]
          simp only [Finset.sum_const_zero, add_zero]
          rw [Finset.mul_sum]
          ring
        · rw [if_neg hDist]
          simp
          rw [Finset.mul_sum]
          ring
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) * W target +
      (if target = distinguishedTarget then
        eta * ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, W source
      else 0) +
      Real.exp (16 * beta) * (responseCoefficient * W target) := by
        exact add_le_add
          (add_le_add hLocal (le_refl _))
          (mul_le_mul_of_nonneg_left hResponse hExpNonneg)
    _ =
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) * W target +
      (if target = distinguishedTarget then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H, W source
      else 0) := by
        simp [eta]
        ring

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le_of_ne_distinguishedTarget
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center distinguishedTarget target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hTarget : target ≠ distinguishedTarget)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseRow :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedRowBound
        H s center R responseCoefficient) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
          H beta hbeta distinguishedTarget R hRNonneg).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le_local_add_pin_add_response
      H beta hbeta s hs center distinguishedTarget target
      R hRNonneg responseCoefficient hResponseRow
  simpa [hTarget] using h

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le_at_distinguishedTarget
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center distinguishedTarget :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseRow :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedRowBound
        H s center R responseCoefficient) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel
          H beta hbeta distinguishedTarget R hRNonneg).influence distinguishedTarget source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        Real.exp (16 * beta) * responseCoefficient) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center distinguishedTarget +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
        ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center source := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledPhysicalLeftKernel_exponentialWeightedRow_le_local_add_pin_add_response
      H beta hbeta s hs center distinguishedTarget distinguishedTarget
      R hRNonneg responseCoefficient hResponseRow

end

end MathlibAnalytic
end MGAP4D
