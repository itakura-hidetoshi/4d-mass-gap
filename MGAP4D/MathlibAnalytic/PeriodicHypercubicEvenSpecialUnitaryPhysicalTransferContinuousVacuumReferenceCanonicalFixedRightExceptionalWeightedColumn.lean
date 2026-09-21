import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightLocalHarnackResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceC5ExceptionalSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackExponentialWeightedRow
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedTargetPhysicalLeftExponentialWeightedPinAbsorption
import Mathlib.Tactic

/-!
# Canonical fixed-right exceptional weighted column

The canonical fixed-right response profile is now pointwise bounded by the
volume-independent fixed-right boundary-update Harnack response coefficient

  exp(16 beta) * eta_R(beta).

The C5 exceptional target set contains only the source, the chosen center, and
the direct intrinsic active neighbors of the source, and has cardinality at
most twenty.  Every active-neighbor move changes the embedded base-L1 distance
by at most two, so for s >= 1 every exceptional target weight is bounded by
s^2 times the source weight.

Combining these two independent facts closes the complete exceptional weighted
response block by

  20 * s^2 * exp(16 beta) * eta_R(beta) * W_center(source),

uniformly in the finite volume.  The coefficient vanishes at beta = 0.

No weighted response hypothesis, remote resolvent, contraction assumption,
covariance decay, coercivity, or mass-gap input is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance canonicalFixedRightExceptionalWeightedColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every target in the C5 exceptional set lies within the two-step
base-L1 weight envelope of the source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_le_twoStep_mul_of_mem_C5Exceptional
    (H : ℕ)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hTarget :
      target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source center) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target ≤
      s ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  classical
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWSourceNonneg : 0 ≤ W source := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg center source
  have hScale : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hSourceScale : W source ≤ s ^ 2 * W source := by
    simpa using
      (mul_le_mul_of_nonneg_right hScale hWSourceNonneg)
  have hCases :
      target = source ∨
        target = center ∨
          target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source := by
    simpa [periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers] using hTarget
  rcases hCases with hEqSource | hRest
  · subst target
    simpa [W] using hSourceScale
  · rcases hRest with hEqCenter | hActive
    · subst target
      have hOneSource :
          1 ≤ W source := by
        simpa [W] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_one_le
            H s hs center source
      have hOneScale :
          1 ≤ s ^ 2 * W source :=
        hOneSource.trans hSourceScale
      simpa [
        W,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self] using
        hOneScale
    · have hAdjSourceTarget :
          (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj source target :=
        (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
          H source target).mpr hActive
      have hStep :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ≤ 2 :=
        periodicHypercubicEvenSpatialSliceActiveGraph_adj_baseL1Distance_le_two
          H hAdjSourceTarget
      have hTriangle :=
        periodicHypercubicEdgeBaseL1Distance_triangle
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
      have hDistance :
          periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ≤
            periodicHypercubicEdgeBaseL1Distance
                (PeriodicHypercubicEvenSideLength H)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) +
              2 := by
        omega
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      calc
        s ^
            periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) ≤
          s ^
            (periodicHypercubicEdgeBaseL1Distance
                (PeriodicHypercubicEvenSideLength H)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) +
              2) :=
          pow_le_pow_right₀ hs hDistance
        _ =
          s ^ 2 *
            s ^
              periodicHypercubicEdgeBaseL1Distance
                (PeriodicHypercubicEvenSideLength H)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
                (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) := by
          rw [pow_add]
          ring

/-- The complete canonical response mass on the finite C5 exceptional target
block has a volume-independent exponentially weighted bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exceptionalExponentialWeightedColumn_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta target source) ≤
      (20 * s ^ 2 * Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
          beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  classical
  let exceptional :=
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
      H source center
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let Rcan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let etaR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
      beta
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hEtaR : 0 ≤ etaR := by
    simpa [etaR] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_nonneg
        beta hbeta
  have hResponseCoeff :
      0 ≤ Real.exp (16 * beta) * etaR :=
    mul_nonneg (Real.exp_pos _).le hEtaR
  have hWNonneg : ∀ target, 0 ≤ W target := by
    intro target
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg center target
  have hPoint :
      ∀ target ∈ exceptional,
        W target * Rcan target source ≤
          (s ^ 2 * Real.exp (16 * beta) * etaR) * W source := by
    intro target hTarget
    have hWeight :
        W target ≤ s ^ 2 * W source := by
      simpa [W, exceptional] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_le_twoStep_mul_of_mem_C5Exceptional
          H s hs center source target hTarget
    have hResponse :
        Rcan target source ≤ Real.exp (16 * beta) * etaR := by
      simpa [Rcan, etaR] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_exp_sixteen_mul_boundaryUpdateHarnackInfluence
          H N hN beta hbeta target source
    calc
      W target * Rcan target source ≤
          W target * (Real.exp (16 * beta) * etaR) :=
        mul_le_mul_of_nonneg_left hResponse (hWNonneg target)
      _ ≤
          (s ^ 2 * W source) * (Real.exp (16 * beta) * etaR) :=
        mul_le_mul_of_nonneg_right hWeight hResponseCoeff
      _ = (s ^ 2 * Real.exp (16 * beta) * etaR) * W source := by
        ring
  have hCardNat : exceptional.card ≤ 20 := by
    simpa [exceptional] using
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers_card_le_twenty
        H source center
  have hCard : (exceptional.card : ℝ) ≤ 20 := by
    exact_mod_cast hCardNat
  have hConstantNonneg :
      0 ≤ (s ^ 2 * Real.exp (16 * beta) * etaR) * W source := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg hsNonneg 2) (Real.exp_pos _).le)
          hEtaR)
        (hWNonneg source)
  calc
    (∑ target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta target source) =
      ∑ target ∈ exceptional, W target * Rcan target source := by
        rfl
    _ ≤
      ∑ _target ∈ exceptional,
        (s ^ 2 * Real.exp (16 * beta) * etaR) * W source := by
          apply Finset.sum_le_sum
          intro target hTarget
          exact hPoint target hTarget
    _ =
      (exceptional.card : ℝ) *
        ((s ^ 2 * Real.exp (16 * beta) * etaR) * W source) := by
          simp [nsmul_eq_mul]
    _ ≤
      20 * ((s ^ 2 * Real.exp (16 * beta) * etaR) * W source) :=
        mul_le_mul_of_nonneg_right hCard hConstantNonneg
    _ =
      (20 * s ^ 2 * Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
          beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
      simp [W, etaR]
      ring

end

end MathlibAnalytic
end MGAP4D
