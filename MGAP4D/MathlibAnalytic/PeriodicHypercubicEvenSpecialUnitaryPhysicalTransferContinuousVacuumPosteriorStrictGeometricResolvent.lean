import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStrictRandomScanGeometric
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-!
# Strict posterior random-scan geometric resolvent

PR #5181 proves, at every fixed finite side H and inside the fixed-volume
posterior Dobrushin cutoff, the geometric variation estimate

  U^m v(s) <= q_H(beta)^m V,

where

  q_H(beta) = (n - 1 + alpha_H(beta)) / n,
  0 <= q_H(beta) < 1.

This file converts that pointwise contraction into finite geometric resolvent
control.  The finite partial variation sum obeys the exact geometric-series
upper bound

  S_M(s) <= ((1 - q^M) / (1 - q)) V,

and the normalized finite random-scan resolvent

  w_M(s) = n^{-1} S_M(s)

is uniformly bounded in M by

  w_M(s) <= V / (1 - alpha_H(beta)).

The identity n (1 - q_H) = 1 - alpha_H is proved explicitly and is the bridge
between the random-scan normalization and the Dobrushin coefficient.

All statements remain fixed-volume.  No H-independent cutoff, volume-uniform
strictness, Euclidean-time identification, continuum generator limit, H1-D5
exact descent, or complete Yang--Mills mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorStrictGeometricResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact algebraic relation between the fixed-volume random-scan contraction
rate and the total strict Dobrushin coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_one_sub_identity
    (H : ℕ)
    (beta : ℝ) :
    let n : ℝ :=
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
    let alpha :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta
    n *
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta) =
      1 - alpha := by
  dsimp
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  change
    n * (1 - (n - 1 + alpha) / n) =
      1 - alpha
  field_simp [hnNe]
  ring

/-- The finite strict posterior random-scan variation sum is bounded by the
exact finite geometric series. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_geometric
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
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta)) * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum]
  calc
    (Finset.range M).sum
        (fun m =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source) ≤
      (Finset.range M).sum (fun m => q ^ m * V) := by
        apply Finset.sum_le_sum
        intro m _hm
        simpa [D, q] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationIterate_le_rate_pow_mul
            H N hN beta hbeta hbetaPos hbetaCutoff B
            variation hVariationNonneg V hV hVariationLe m source
    _ =
      ((Finset.range M).sum (fun m => q ^ m)) * V := by
        rw [Finset.sum_mul]
    _ = ((1 - q ^ M) / (1 - q)) * V := by
      rw [geom_sum_of_lt_one hqLt]
    _ =
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta)) * V := by
      rfl

/-- The finite strict posterior random-scan variation sum is uniformly bounded
by the full geometric-series envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
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
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_nonneg
        H beta hbeta
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_geometric
      H N hN beta hbeta hbetaPos hbetaCutoff B
      variation hVariationNonneg V hV hVariationLe M source
  have hRatio :
      (1 - q ^ M) / (1 - q) ≤ (1 : ℝ) / (1 - q) := by
    apply (div_le_div_iff_of_pos_right hOneSubQPos).2
    have hPowNonneg : 0 ≤ q ^ M := pow_nonneg hqNonneg M
    linarith
  calc
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      ((1 - q ^ M) / (1 - q)) * V := by
        simpa [q] using hFinite
    _ ≤ ((1 : ℝ) / (1 - q)) * V :=
      mul_le_mul_of_nonneg_right hRatio hV
    _ = (1 - q)⁻¹ * V := by
      rw [one_div]
    _ =
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
      rfl

/-- The normalized finite strict posterior random-scan resolvent is uniformly
bounded by V / (1 - alpha_H(beta)). -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanFiniteResolventProfile_le_one_sub_totalCoefficient
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
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
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
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hOneSubQNe : 1 - q ≠ 0 := ne_of_gt hOneSubQPos
  have hAlphaLt : alpha < 1 := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
        H beta hbetaPos hbetaCutoff
  have hOneSubAlphaPos : 0 < 1 - alpha := sub_pos.mpr hAlphaLt
  have hOneSubAlphaNe : 1 - alpha ≠ 0 := ne_of_gt hOneSubAlphaPos
  have hPartial :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
        (1 - q)⁻¹ * V := by
    simpa [D, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  have hIdentity :
      n * (1 - q) = 1 - alpha := by
    simpa [n, alpha, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_one_sub_identity
        H beta
  have hNormalize :
      n⁻¹ * ((1 - q)⁻¹ * V) = V / (1 - alpha) := by
    field_simp [hnNe, hOneSubQNe, hOneSubAlphaNe]
    nlinarith [hIdentity]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
  change
    n⁻¹ *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
      V / (1 - alpha)
  calc
    n⁻¹ *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
      n⁻¹ * ((1 - q)⁻¹ * V) :=
        mul_le_mul_of_nonneg_left hPartial (inv_nonneg.mpr hnPos.le)
    _ = V / (1 - alpha) := hNormalize

end

end MathlibAnalytic
end MGAP4D
