import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernelBaseL1Propagation
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

/-!
# Exponentially weighted row bound for the physical local Harnack kernel

The physical left influence envelope has already been split exactly into its
intrinsic active-neighbor Harnack carrier plus the source-aligned remote
residual.  This file treats only the genuinely local carrier.

For a base link `center` and a scale `s ≥ 1`, attach the growing spatial
weight

  `s ^ baseL1Distance(center, source)`.

Every nonzero local-Harnack edge moves the embedded base-L1 coordinate by at
most two.  Therefore one local update can enlarge the spatial weight by at
most `s^2`.  Combining this with the volume-independent eighteen-neighbor row
bound gives the weighted Schur estimate

  `sum_source K(target,source) * weight(source)
      ≤ (18 * eta(beta) * s^2) * weight(target)`.

No remote-response estimate, covariance decay, terminal contraction,
Poincare/coercivity inequality, or mass-gap statement is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalHarnackExponentialWeightedRowSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Growing exponential weight associated with embedded periodic base-L1
separation from a chosen spatial-link center. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
    (H : ℕ)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  s ^
    periodicHypercubicEdgeBaseL1Distance
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)

/-- The exponential base-L1 weight is nonnegative for a nonnegative scale. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
    (H : ℕ)
    (s : ℝ)
    (hs : 0 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  exact pow_nonneg hs _

/-- The exponential base-L1 weight is strictly positive for a positive scale. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
    (H : ℕ)
    (s : ℝ)
    (hs : 0 < s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  exact pow_pos hs _

/-- Across one nonzero local-Harnack edge, a growing base-L1 exponential
weight changes by at most the two-step factor `s^2`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_le_twoStep_mul_of_influence_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNe :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source ≠ 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center source ≤
      s ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  have hActive :
      target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_active_of_influence_ne_zero
      H beta hbeta target source hNe
  have hAdjSourceTarget :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj source target :=
    (periodicHypercubicEvenSpatialSliceActiveGraph_adj_iff_mem_activeNeighbors
      H source target).mpr hActive
  have hAdjTargetSource :
      (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj target source :=
    hAdjSourceTarget.symm
  have hStep :
      periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤ 2 :=
    periodicHypercubicEvenSpatialSliceActiveGraph_adj_baseL1Distance_le_two
      H hAdjTargetSource
  have hTriangle :=
    periodicHypercubicEdgeBaseL1Distance_triangle
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
      (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
  have hDistance :
      periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤
        periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) +
          2 := by
    omega
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
  calc
    s ^
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source) ≤
      s ^
        (periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) +
          2) :=
      pow_le_pow_right₀ hs hDistance
    _ =
      s ^ 2 *
        s ^
          periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H center)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target) := by
      rw [pow_add]
      ring

/-- Volume-independent exponentially weighted Schur row bound for the genuine
local physical Harnack carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hTargetWeightNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
      H s hsNonneg center target
  have hScaleNonneg :
      0 ≤
        s ^ 2 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target :=
    mul_nonneg (pow_nonneg hsNonneg 2) hTargetWeightNonneg
  have hRow :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) ≤
        18 * eta := by
    simpa [K, eta, finiteInfluenceKernelRowSum] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
        H beta hbeta target
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      K.influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source *
          (s ^ 2 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target) := by
        apply Finset.sum_le_sum
        intro source _hsource
        by_cases hZero : K.influence target source = 0
        · simp [hZero]
        · have hNe :
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
                H beta hbeta).influence target source ≠ 0 := by
            simpa [K] using hZero
          exact
            mul_le_mul_of_nonneg_left
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_le_twoStep_mul_of_influence_ne_zero
                H beta hbeta s hs center target source hNe)
              (K.influence_nonneg target source)
    _ =
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) *
          (s ^ 2 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center target) := by
        rw [Finset.sum_mul]
    _ ≤
      (18 * eta) *
        (s ^ 2 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) :=
      mul_le_mul_of_nonneg_right hRow hScaleNonneg
    _ =
      (18 * eta * s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      ring
    _ =
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
      rfl

/-- Under the strict exponentially weighted local threshold, the local
Harnack row acts strictly below the chosen growing spatial weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_lt_weight
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (hWeightedThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 < 1)
    (center target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target := by
  have hsPos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hWeightPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
      H s hsPos center target
  have hRow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
      H beta hbeta s hs center target
  exact hRow.trans_lt (by
    simpa using
      (mul_lt_mul_of_pos_right hWeightedThreshold hWeightPos))

end

end MathlibAnalytic
end MGAP4D
