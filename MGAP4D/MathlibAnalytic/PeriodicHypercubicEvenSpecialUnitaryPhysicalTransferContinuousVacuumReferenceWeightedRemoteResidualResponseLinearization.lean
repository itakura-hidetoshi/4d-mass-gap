import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftExponentialWeightedEnvelopeColumn
import Mathlib.Tactic

/-!
# Linearize the actual weighted remote residual through fixed-right response bounds

The targetwise worst-case cross-ratio influence majorant is defined from the
fixed-right target-ratio response by the monotone transform

  x ↦ 2 * (exp (log (1 + exp(16 beta) x)) - 1)
          / (exp (log (1 + exp(16 beta) x)) + 1).

The existing finite-step theorem immediately appends the old coarse tagged
transport estimate.  For the exponentially weighted physical route we first
need the strictly earlier, carrier-free part of that argument:

  worstCaseMajorant(target,source)
    ≤ exp(16 beta) * responseBound(target).

This file exposes that linearization and sums it against the growing base-L1
weight.  The resulting weighted remote-residual column is controlled by a
weighted fixed-right response-bound profile without introducing any coarse
all-to-all left-left carrier.

No remote coefficient kappa is assumed, no random-scan transport is used, and
no covariance-decay, sweep-contraction, Poincare/coercivity, or mass-gap input
is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance weightedRemoteResidualResponseLinearizationSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any common upper bound on all fixed-right target-ratio responses at one
target/source pair linearizes the targetwise worst-case cross-ratio majorant
with the exact factor exp(16 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_of_responseBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R : ℝ)
    (hRNonneg : 0 ≤ R)
    (hResponse :
      ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k ≤
          R) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta B target source ≤
      Real.exp (16 * beta) * R := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
  apply csSup_le
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorantSet_nonempty
      H N hN beta hbeta B target source)
  intro x hx
  rcases hx with ⟨g₁, g₂, h, k, rfl⟩
  let response : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
      H N hN beta hbeta B target source g₁ g₂ h k
  have hResponseNonneg : 0 ≤ response := by
    dsimp [response]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_nonneg
        H N hN beta hbeta B target source g₁ g₂ h k
  have hLinear :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
          H N hN beta hbeta B target source g₁ g₂ h k ≤
        Real.exp (16 * beta) * response := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant,
      response] using
      finitePositiveWeightCrossRatioInfluenceTransform_log_one_add_le
        (Real.exp (16 * beta) * response)
        (mul_nonneg (Real.exp_pos _).le hResponseNonneg)
  have hResponseBound : response ≤ R := by
    simpa [response] using hResponse g₁ g₂ h k
  exact
    hLinear.trans
      (mul_le_mul_of_nonneg_left hResponseBound (Real.exp_pos _).le)

/-- On an intrinsic remote target, any fixed-right response bound controls the
actual source-aligned physical residual with the same exp(16 beta) factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_of_responseBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hNotActive :
      target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source)
    (R : ℝ)
    (hRNonneg : 0 ≤ R)
    (hResponse :
      ∀ g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A target source g₁ g₂ h k ≤
          R) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target ≤
      Real.exp (16 * beta) * R := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_worstCase_of_remote
      H N hN beta hbeta A source target hne hNotActive]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_of_responseBound
      H N hN beta hbeta A target source R hRNonneg hResponse

/-- A nonnegative pointwise fixed-right response-bound profile controls the
entire actual exponentially weighted remote residual column.  This is the
carrier-free weighted interface needed before applying the actual physical
response bootstrap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn_le_exp_sixteen_mul_responseWeightedMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 0 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target, 0 ≤ R target)
    (hResponse :
      ∀ target g₁ g₂ h k,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta A target source g₁ g₂ h k ≤
          R target) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source ≤
      Real.exp (16 * beta) *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          R target *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
  have hPoint :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source target ≤
          Real.exp (16 * beta) * R target := by
    intro target
    by_cases hEq : target = source
    · subst target
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_self]
      exact mul_nonneg (Real.exp_pos _).le (hRNonneg source)
    · by_cases hActive :
          target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
      · rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_zero_of_active
            H N hN beta hbeta A source target hActive]
        exact mul_nonneg (Real.exp_pos _).le (hRNonneg target)
      · exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_of_responseBound
            H N hN beta hbeta A source target hEq hActive
            (R target) (hRNonneg target)
            (fun g₁ g₂ h k => hResponse target g₁ g₂ h k)
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (Real.exp (16 * beta) * R target) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target := by
      apply Finset.sum_le_sum
      intro target _hTarget
      exact
        mul_le_mul_of_nonneg_right
          (hPoint target)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
            H s hs center target)
    _ =
      Real.exp (16 * beta) *
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          R target *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro target _hTarget
      ring

end

end MathlibAnalytic
end MGAP4D
