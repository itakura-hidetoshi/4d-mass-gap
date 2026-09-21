import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightFullWeightedBootstrap
import Mathlib.Tactic

/-!
# Exact canonical fixed-right weighted response coefficient

For a fixed lattice, exponential scale and center, define the exact canonical
weighted response coefficient as the maximum over sources of the normalized
weighted response column

  M_can = max_source
    [sum_target R_can(target,source) W_center(target)] / W_center(source).

Because the source set is finite and nonempty, this maximum is an actual
finite maximum, not an external upper bound.

This file proves:

* M_can is nonnegative for s >= 1;
* M_can itself supplies the weighted-column certificate required by the
  response-controlled machinery;
* whenever its induced pin-free coefficient is strictly below one, the merged
  full-column bootstrap theorem yields the scalar inequality

    M_can <= Phi(M_can);

* at beta = 0, the canonical response profile and therefore M_can vanish
  exactly.

Thus the remaining closure problem is reduced to controlling the actual scalar
M_can, rather than an arbitrary assumed response coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance canonicalFixedRightWeightedCoefficientSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance canonicalFixedRightWeightedCoefficientSpatialLinkNonempty
    (H : ℕ) : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) := by
  refine ⟨
    (⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by decide⟩)⟩

/-- One source-normalized exponentially weighted canonical response column. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target) /
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center source

/-- Finite set of all source-normalized canonical weighted columns. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnValues
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) : Finset ℝ := by
  classical
  exact Finset.univ.image
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
      H N hN beta hbeta s center)

/-- Exact maximum normalized weighted column of the canonical fixed-right
response profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumnValues
      H N hN beta hbeta s center).max' (by
    classical
    let source : PeriodicHypercubicEvenSpatialSliceLink H :=
      Classical.choice
        (inferInstance : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H))
    refine ⟨
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
        H N hN beta hbeta s center source, ?_⟩
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩)

/-- Every concrete normalized weighted column is bounded by the exact canonical
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn_le_coefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
        H N hN beta hbeta s center source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨source, Finset.mem_univ source, rfl⟩

/-- The exact canonical weighted-column coefficient is nonnegative for a
growing scale s >= 1. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center := by
  let source : PeriodicHypercubicEvenSpatialSliceLink H :=
    Classical.choice
      (inferInstance : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H))
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let Rcan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hWPos : 0 < W source := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
        H s hsPos center source
  have hWNonneg : ∀ target, 0 ≤ W target := by
    intro target
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsPos.le center target
  have hRNonneg : ∀ target, 0 ≤ Rcan target source := by
    intro target
    simpa [Rcan] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta target source
  have hNumerator :
      0 ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          Rcan target source * W target := by
    exact Finset.sum_nonneg fun target _ =>
      mul_nonneg (hRNonneg target) (hWNonneg target)
  have hNormalized :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
          H N hN beta hbeta s center source := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
    simpa [W, Rcan] using div_nonneg hNumerator hWPos.le
  exact hNormalized.trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn_le_coefficient
      H N hN beta hbeta s center source)

/-- The exact canonical coefficient supplies its own weighted-column
certificate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_exactCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
      H s center
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center) := by
  intro source
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hWPos : 0 < W source := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
        H s hsPos center source
  have hNormalized :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn_le_coefficient
      H N hN beta hbeta s center source
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn at hNormalized
  simpa [W] using
    (div_le_iff₀ hWPos).mp hNormalized

/-- The actual exact canonical coefficient satisfies the scalar bootstrap
inequality whenever its own induced pin-free physical coefficient lies below
one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_bootstrap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
            H N hN beta hbeta s center) < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
        beta s
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
            H N hN beta hbeta s center) := by
  classical
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  have hMNonneg : 0 ≤ M := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_nonneg
        H N hN beta hbeta s hs center
  have hCertificate :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s center
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        M := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_exactCoefficient
        H N hN beta hbeta s hs center
  have hImproved :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_bootstrap
      H N hN beta hbeta s hs center M hMNonneg hCertificate
      (by simpa [M] using hCoefficientLtOne)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
  rw [Finset.max'_le_iff]
  intro value hValue
  rcases Finset.mem_image.mp hValue with ⟨source, _hSource, rfl⟩
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hWPos : 0 < W source := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
        H s hsPos center source
  have hColumn := hImproved source
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
  apply (div_le_iff₀ hWPos).2
  simpa [W, M] using hColumn

/-- At zero coupling every canonical fixed-right response vanishes exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_beta_zero
    (H N : ℕ)
    (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN 0 (by norm_num) target source = 0 := by
  have hUpper :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_exp_sixteen_mul_boundaryUpdateHarnackInfluence
      H N hN 0 (by norm_num) target source
  have hUpperZero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN 0 (by norm_num) target source ≤ 0 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence] using
      hUpper
  have hNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
      H N hN 0 (by norm_num) target source
  exact le_antisymm hUpperZero hNonneg

/-- Consequently the exact canonical weighted-column coefficient starts at
zero coupling with value zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_beta_zero
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN 0 (by norm_num) s center = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
  rw [Finset.max'_le_iff]
  apply le_antisymm
  · intro value hValue
    rcases Finset.mem_image.mp hValue with ⟨source, _hSource, rfl⟩
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_beta_zero
        H N hN]
  · let source : PeriodicHypercubicEvenSpatialSliceLink H :=
      Classical.choice
        (inferInstance : Nonempty (PeriodicHypercubicEvenSpatialSliceLink H))
    have hLe :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn_le_coefficient
        H N hN 0 (by norm_num) s center source
    have hZero :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
            H N hN 0 (by norm_num) s center source = 0 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioNormalizedExponentialWeightedColumn
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_beta_zero
          H N hN]
    simpa [hZero] using hLe

end

end MathlibAnalytic
end MGAP4D
