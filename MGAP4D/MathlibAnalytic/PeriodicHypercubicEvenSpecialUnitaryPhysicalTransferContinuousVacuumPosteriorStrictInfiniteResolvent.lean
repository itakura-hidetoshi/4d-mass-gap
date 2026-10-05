import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStrictGeometricResolvent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Strict posterior random-scan infinite resolvent

PR #5182 proves, at fixed finite volume and inside the strict posterior
Dobrushin cutoff, the uniform finite resolvent estimate

  w_M(s) <= V / (1 - alpha_H(beta)).

This file closes the corresponding infinite random-scan resolvent.  The
pointwise variation iterates are nonnegative and their finite partial sums are
uniformly bounded, so the real series is summable.  Its tsum is bounded by the
same geometric envelope, and after the exact random-scan normalization one
obtains

  w_infty(s) <= V / (1 - alpha_H(beta)).

All statements are fixed-volume.  No H-independent cutoff, volume-uniform
strictness, Euclidean-time identification, continuum generator limit, H1-D5
exact descent, or complete Yang--Mills mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
open Filter

noncomputable section

local instance posteriorStrictInfiniteResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Infinite normalized posterior random-scan variation resolvent. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanInfiniteResolventProfile
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    ∑' m : ℕ,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D variation m source

/-- Inside the fixed-volume strict Dobrushin cutoff, every fixed-source
posterior random-scan variation orbit is summable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationIterate_summable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    Summable
      (fun m : ℕ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
            H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  have hIterNonneg :
      ∀ m : ℕ,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source := by
    intro m
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation hVariationNonneg m source
  have hRange :
      ∀ M : ℕ,
        (Finset.range M).sum
            (fun m =>
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
                variation m source) ≤
          (1 - q)⁻¹ * V := by
    intro M
    rw [
      ← periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source]
    simpa [D, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  exact summable_of_sum_range_le hIterNonneg hRange

/-- The unnormalized infinite variation sum is bounded by the full geometric
series envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationTsum_le_inv_one_sub_rate_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑' m : ℕ,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation m source) ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  have hIterNonneg :
      ∀ m : ℕ,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source := by
    intro m
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation hVariationNonneg m source
  have hRange :
      ∀ M : ℕ,
        (Finset.range M).sum
            (fun m =>
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
                variation m source) ≤
          (1 - q)⁻¹ * V := by
    intro M
    rw [
      ← periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source]
    simpa [D, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  simpa [D, q] using
    (Real.tsum_le_of_sum_range_le hIterNonneg hRange)

/-- The normalized infinite strict posterior random-scan resolvent obeys the
same fixed-volume Dobrushin bound as every finite resolvent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanInfiniteResolventProfile_le_one_sub_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanInfiniteResolventProfile
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      V /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
            H beta) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff
  have hOneSubQNe : 1 - q ≠ 0 :=
    ne_of_gt (sub_pos.mpr hqLt)
  have hTsum :
      (∑' m : ℕ,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source) ≤
        (1 - q)⁻¹ * V := by
    simpa [D, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationTsum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe source
  have hIdentity :
      n * (1 - q) = 1 - alpha := by
    simpa [n, alpha, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_one_sub_identity
        H beta
  have hNormalize :
      n⁻¹ * ((1 - q)⁻¹ * V) = V / (1 - alpha) := by
    calc
      n⁻¹ * ((1 - q)⁻¹ * V) =
          V / (n * (1 - q)) := by
            field_simp [hnNe, hOneSubQNe]
      _ = V / (1 - alpha) := by
        rw [hIdentity]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanInfiniteResolventProfile
  change
    n⁻¹ *
        (∑' m : ℕ,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source) ≤
      V / (1 - alpha)
  calc
    n⁻¹ *
        (∑' m : ℕ,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source) ≤
      n⁻¹ * ((1 - q)⁻¹ * V) :=
        mul_le_mul_of_nonneg_left hTsum (inv_nonneg.mpr hnPos.le)
    _ = V / (1 - alpha) := hNormalize

end

end MathlibAnalytic
end MGAP4D
