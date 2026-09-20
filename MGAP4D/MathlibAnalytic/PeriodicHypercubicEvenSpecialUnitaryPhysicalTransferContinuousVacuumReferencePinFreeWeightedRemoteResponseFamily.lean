import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeSourceDiscrepancySuperposition
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledStationaryTerminalResidual
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Pin-free weighted remote response family

The pointwise pin-free response resolvent cannot be summed naively in the
target variable: the product of two increasing target-centered exponential
weights has the wrong orientation.

Instead, this file first aggregates the singleton target-ratio variations with
the fixed center weight and then transports that aggregate through the
pin-free response-controlled recurrence.

For a fixed center C and source y, let Remote(y,C) be the complement of the C5
exceptional target set and let

  V_remote(e) =
    sum_{t in Remote(y,C)} W_C(t) * V_t(e).

Because every V_t is the singleton profile exp(16 beta) * 1_{e=t},

  V_remote(e) <= exp(16 beta) * W_C(e).

The superposition theorem then identifies the accumulated discrepancy of
V_remote with the weighted sum of the targetwise discrepancies exactly.

At complete-block depth n, arbitrary target-indexed response witnesses satisfy

  sum_remote W_C(t) Response_t
    <= aggregate_discrepancy
       + rho_H(beta)^n * exp(16 beta) * sum_remote W_C(t).

The last factor may depend on the fixed finite volume, but rho_H(beta)^n tends
to zero before any volume-uniform conclusion is taken.  Hence the asymptotic
weighted remote response bound is volume-independent.

No targetwise witness is required to be shared between different targets.
This is the form needed for the subsequent canonical-supremum lift.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance pinFreeWeightedRemoteResponseFamilySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The center-weighted aggregate of singleton target-ratio variations over the
geometrically remote C5 target set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
    (H : ℕ)
    (beta s : ℝ)
    (center source e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target e

/-- The remote weighted aggregate is exactly the full weighted singleton value
on remote coordinates and zero elsewhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_eq_if
    (H : ℕ)
    (beta s : ℝ)
    (center source e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
        H beta s center source e =
      if e ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source center
      then
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center e
      else 0 := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source center
  by_cases he : e ∈ remote
  · rw [if_pos]
    · unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
      rw [Finset.sum_eq_single e]
      · simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
          mul_comm]
      · intro target hTarget hTargetNe
        have hENe : e ≠ target := Ne.symm hTargetNe
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
          hENe]
      · simpa [remote] using he
    · simpa [remote] using he
  · rw [if_neg]
    · unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
      apply Finset.sum_eq_zero
      intro target hTarget
      have hENe : e ≠ target := by
        intro hEq
        subst target
        exact he (by simpa [remote] using hTarget)
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
        hENe]
    · simpa [remote] using he

/-- The remote aggregate variation is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_nonneg
    (H : ℕ)
    (beta s : ℝ)
    (hs : 0 ≤ s)
    (center source e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
        H beta s center source e := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_eq_if]
  split
  · exact
      mul_nonneg (Real.exp_pos _).le
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
          H s hs center e)
  · exact le_rfl

/-- The remote aggregate is bounded by the same center weight with coefficient
exp(16 beta), independently of the number of remote targets. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_le_exp_sixteen_mul_weight
    (H : ℕ)
    (beta s : ℝ)
    (hs : 0 ≤ s)
    (center source e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
        H beta s center source e ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center e := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_eq_if]
  split
  · exact le_rfl
  · exact
      mul_nonneg (Real.exp_pos _).le
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
          H s hs center e)

/-- The discrepancy generated by the remote weighted aggregate variation is
exactly the center-weighted sum of the singleton target discrepancies. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregatePinFreeAccumulatedSourceDiscrepancy_eq_sum
    (H : ℕ)
    (beta s : ℝ)
    (hbeta : 0 ≤ beta)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
          H beta s center source)
        n =
      ∑ target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source center,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
            H beta hbeta source R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source center
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta
  have hSum :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_finset_sum
      H beta hbeta source R hRNonneg remote
      (fun target e => W target * V target e) n
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
          H beta s center source)
        n =
      ∑ target ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta source R hRNonneg
          (fun e => W target * V target e)
          n := by
            simpa [
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation,
              remote, W, V] using hSum
    _ =
      ∑ target ∈ remote,
        W target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
            H beta hbeta source R hRNonneg (V target) n := by
          apply Finset.sum_congr rfl
          intro target _hTarget
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_const_mul
              H beta hbeta source R hRNonneg
              (W target) (V target) n
    _ =
      ∑ target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source center,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
            H beta hbeta source R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n := by
          rfl

/-- Complete-block finite-step bound for an arbitrary target-indexed family of
remote fixed-right response witnesses.  The target witnesses are independent;
only the common response majorant R and source are shared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteWeightedResponseFamily_le_pinFreeAggregateResolvent_add_terminalBlockResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (B :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta (B target) target source
          (g₁ target) (g₂ target) (h target) (k target)) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n *
        Real.exp (16 * beta) *
        (∑ target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source center,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source center
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta
  let m :=
    n *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  let rho : ℝ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  let D :=
    fun target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
        H beta hbeta source R hRNonneg (V target) m
  let T :=
    fun target =>
      |(∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta (B target) target source (g₂ target) (k target)
            (fun C =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C (B target) target (g₁ target) /
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C (B target) target (g₂ target))
            m A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update (B target) source (h target)) target (g₂ target))) -
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta (B target) target source (g₂ target) (k target)
            (fun C =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C (B target) target (g₁ target) /
                periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                    H N beta C (B target) target (g₂ target))
            m A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update (B target) source (k target)) target (g₂ target)))|
  have hGeometry :
      ∀ target ∈ remote,
        target ≠ source ∧
          ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
    intro target hTarget
    have hRemote :
        target ∉
          periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
            H source center := by
      simpa [
        remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
        hTarget
    rcases
      periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
        H source center target hRemote with
      ⟨hSourceTarget, _hTargetCenter, hNoShare⟩
    exact ⟨Ne.symm hSourceTarget, hNoShare⟩
  have hWNonneg : ∀ target, 0 ≤ W target := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (le_trans (by norm_num) hs) center target
  have hPoint :
      ∀ target ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta (B target) target source
            (g₁ target) (g₂ target) (h target) (k target) ≤
          D target + T target := by
    intro target hTarget
    rcases hGeometry target hTarget with ⟨hne, hNoShare⟩
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_pinFreeResponseControlledAccumulated_add_terminal_of_remote
        H N hN beta hbeta R hRNonneg hResponse
        (B target) hne hNoShare
        (g₁ target) (g₂ target) (h target) (k target) m
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs,
      D, T, V] using hRaw
  have hTerminal :
      ∀ target ∈ remote,
        T target ≤ rho ^ n * Real.exp (16 * beta) := by
    intro target hTarget
    rcases hGeometry target hTarget with ⟨hne, hNoShare⟩
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_terminalResponse_mul_scheduleLength_le_exp_sixteen_of_remote
        H N hN beta hbeta (B target) hne hNoShare
        (g₁ target) (g₂ target) (h target) (k target) n
    simpa [T, m, rho] using hRaw
  have hResponseSum :
      (∑ target ∈ remote,
        W target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta (B target) target source
            (g₁ target) (g₂ target) (h target) (k target)) ≤
        (∑ target ∈ remote, W target * D target) +
          (∑ target ∈ remote, W target * T target) := by
    calc
      (∑ target ∈ remote,
        W target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta (B target) target source
            (g₁ target) (g₂ target) (h target) (k target)) ≤
        ∑ target ∈ remote, W target * (D target + T target) := by
          apply Finset.sum_le_sum
          intro target hTarget
          exact mul_le_mul_of_nonneg_left (hPoint target hTarget) (hWNonneg target)
      _ =
        (∑ target ∈ remote, W target * D target) +
          (∑ target ∈ remote, W target * T target) := by
            simp only [mul_add, Finset.sum_add_distrib]
  have hDiscrepancyEq :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta source R hRNonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
            H beta s center source)
          m =
        ∑ target ∈ remote, W target * D target := by
    simpa [remote, W, D, V] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregatePinFreeAccumulatedSourceDiscrepancy_eq_sum
        H beta s hbeta center source R hRNonneg m
  have hTerminalSum :
      (∑ target ∈ remote, W target * T target) ≤
        rho ^ n * Real.exp (16 * beta) * ∑ target ∈ remote, W target := by
    calc
      (∑ target ∈ remote, W target * T target) ≤
        ∑ target ∈ remote,
          W target * (rho ^ n * Real.exp (16 * beta)) := by
            apply Finset.sum_le_sum
            intro target hTarget
            exact mul_le_mul_of_nonneg_left (hTerminal target hTarget) (hWNonneg target)
      _ =
        rho ^ n * Real.exp (16 * beta) * ∑ target ∈ remote, W target := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro target _hTarget
          ring
  have hAggregateNonneg :
      ∀ e,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
            H beta s center source e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_nonneg
        H beta s (le_trans (by norm_num) hs) center source e
  have hAggregateBound :
      ∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
            H beta s center source e ≤
          Real.exp (16 * beta) * W e := by
    intro e
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation_le_exp_sixteen_mul_weight
        H beta s (le_trans (by norm_num) hs) center source e
  have hAccum :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy_le_weightedResolvent
      H beta hbeta s hs center source R hRNonneg
      responseCoefficient hResponseCoefficient hResponseWeighted
      hCoefficientLtOne
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
        H beta s center source)
      hAggregateNonneg
      (Real.exp (16 * beta))
      (Real.exp_pos _).le
      hAggregateBound
      m
  calc
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta (B target) target source
          (g₁ target) (g₂ target) (h target) (k target)) =
      ∑ target ∈ remote,
        W target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta (B target) target source
            (g₁ target) (g₂ target) (h target) (k target) := by
              rfl
    _ ≤
      (∑ target ∈ remote, W target * D target) +
        (∑ target ∈ remote, W target * T target) := hResponseSum
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta source R hRNonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteExponentialWeightedAggregateVariation
            H beta s center source)
          m +
        rho ^ n * Real.exp (16 * beta) * ∑ target ∈ remote, W target := by
          rw [hDiscrepancyEq]
          exact add_le_add_left hTerminalSum _
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        W source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ +
        rho ^ n * Real.exp (16 * beta) * ∑ target ∈ remote, W target := by
          exact add_le_add_right hAccum _
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ +
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n *
        Real.exp (16 * beta) *
        (∑ target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source center,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) := by
          rfl

/-- Letting complete-block depth tend to infinity removes the finite-volume
terminal mass and leaves a volume-independent bound for every arbitrary
target-indexed remote response family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteWeightedResponseFamily_le_pinFreeAggregateResolvent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (B :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta (B target) target source
          (g₁ target) (g₂ target) (h target) (k target)) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  let left : ℝ :=
    ∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta (B target) target source
          (g₁ target) (g₂ target) (h target) (k target)
  let bound : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹
  let terminalMass : ℝ :=
    Real.exp (16 * beta) *
      (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source center,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target)
  let rho : ℝ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  have hFinite :
      ∀ n : ℕ, left ≤ bound + rho ^ n * terminalMass := by
    intro n
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteWeightedResponseFamily_le_pinFreeAggregateResolvent_add_terminalBlockResidual
        H N hN beta hbeta s hs center source R hRNonneg hResponse
        responseCoefficient hResponseCoefficient hResponseWeighted hCoefficientLtOne
        B g₁ g₂ h k n
    simpa [left, bound, terminalMass, rho] using h
  have hPow :
      Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) := by
    dsimp [rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
        H beta
  have hTail :
      Tendsto (fun n : ℕ => rho ^ n * terminalMass) atTop (𝓝 0) := by
    have h := hPow.mul_const terminalMass
    simpa using h
  have hLimit :
      Tendsto (fun n : ℕ => bound + rho ^ n * terminalMass)
        atTop (𝓝 bound) := by
    simpa using (tendsto_const_nhds.add hTail)
  have hLeft :
      Tendsto (fun _n : ℕ => left) atTop (𝓝 left) :=
    tendsto_const_nhds
  have hFinal : left ≤ bound :=
    le_of_tendsto_of_tendsto' hLeft hLimit hFinite
  simpa [left, bound] using hFinal

end

end MathlibAnalytic
end MGAP4D
