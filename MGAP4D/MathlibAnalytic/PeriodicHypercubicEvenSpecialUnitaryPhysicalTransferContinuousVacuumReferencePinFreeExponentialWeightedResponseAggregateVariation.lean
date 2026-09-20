import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledSourceForcingResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioStationaryResidual
import Mathlib.Tactic

/-!
# Pin-free exponentially weighted response aggregate variation

The self-consistent response closure must aggregate the target family before
propagating it.  Summing pointwise target-centered resolvent estimates would
multiply two growing exponential weights in the wrong orientation.

For a fixed spatial center `center`, define instead the weighted aggregate
of all singleton fixed-right target-ratio variation profiles

  V_center(e) =
    sum_target W_center(target) * V_target(e).

Because `V_target` is supported exactly at `target`, this finite sum
collapses identically to

  V_center(e) = exp(16 * beta) * W_center(e).

Thus the complete target family enters the pin-free random-scan/source-forcing
machinery with exactly the same target-centered exponential weight and with no
target-cardinality factor.

This file records that exact identity and feeds the aggregate profile into the
existing pin-free source-forcing resolvent.  No response closure, covariance
decay, coercivity, or mass-gap input is assumed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance pinFreeExponentialWeightedResponseAggregateVariationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exponentially weighted aggregate of all singleton fixed-right target-ratio
variation profiles around one spatial center. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
    (H : ℕ)
    (beta s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target e

/-- The weighted aggregate singleton variation collapses exactly to the
centered exponential weight.  In particular, no volume/cardinality factor
appears. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_eq_exp_sixteen_mul_weight
    (H : ℕ)
    (beta s : ℝ)
    (center e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
        H beta s center e =
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center e := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
  rw [Finset.sum_eq_single e]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
      mul_comm]
  · intro target _hTarget hTargetNe
    have hENe : e ≠ target := Ne.symm hTargetNe
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
      hENe]
  · simp

/-- The weighted aggregate variation is nonnegative whenever the exponential
weight base is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_nonneg
    (H : ℕ)
    (beta s : ℝ)
    (hs : 0 ≤ s)
    (center e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
        H beta s center e := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_eq_exp_sixteen_mul_weight]
  exact
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hs center e)

/-- The complete weighted target family therefore satisfies the exact
pointwise input bound required by the pin-free source-forcing resolvent, with
bound `exp(16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_le_exp_sixteen_mul_weight
    (H : ℕ)
    (beta s : ℝ)
    (center e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
        H beta s center e ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center e := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_eq_exp_sixteen_mul_weight]

/-- The pin-free accumulated source discrepancy generated by the complete
exponentially weighted target family has the same volume-independent resolvent
bound as a single weighted profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregatePinFreeAccumulatedSourceDiscrepancy_le_weightedResolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
          H beta s center)
        n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_le_weightedResolvent
      H beta hbeta s hs center source R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      hCoefficientLtOne
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation
        H beta s center)
      (fun e =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_nonneg
          H beta s (le_trans (by norm_num) hs) center e)
      (Real.exp (16 * beta))
      (Real.exp_pos _).le
      (fun e =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioExponentialWeightedAggregateVariation_le_exp_sixteen_mul_weight
          H beta s center e)
      n

end

end MathlibAnalytic
end MGAP4D
