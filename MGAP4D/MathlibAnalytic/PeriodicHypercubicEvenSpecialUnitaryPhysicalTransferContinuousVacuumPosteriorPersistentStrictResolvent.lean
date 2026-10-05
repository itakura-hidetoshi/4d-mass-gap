import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorPersistentStrictRandomScanGeometric
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Persistent second-bootstrap strict random-scan resolvent

Merged PR #5187 gives the persistent second-bootstrap geometric contraction

  U^m v(s) <= q_H^(2)(beta)^m V,

with 0 <= q_H^(2)(beta) < 1.  This file sums that estimate and closes both the
finite and infinite normalized random-scan resolvents.

For alpha_H^(2)(beta) the persistent refined total coefficient,

  S_M(s) <= ((1 - q^M) / (1 - q)) V,

and the exact identity

  n * (1 - q) = 1 - alpha_H^(2)

gives the normalized bound

  w_M(s) <= V / (1 - alpha_H^(2)).

The fixed-source variation orbit is summable, and the infinite normalized
resolvent obeys the same bound.

All statements remain fixed-volume and the second cutoff is H-dependent.
No volume-uniform strictness, Euclidean-time identification, continuum
spacing-scaled generator bridge, H1-D5 exact descent, or complete
Yang--Mills mass-gap claim is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance posteriorPersistentStrictResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Finite partial variation sums obey the exact second-bootstrap geometric
series bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_geometric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
            H beta) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
            H beta)) * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
      H beta
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_lt_one
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
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationIterate_le_rate_pow_mul
            H N hN beta hbeta hbetaPos hbetaCutoff B
            variation hVariationNonneg V hV hVariationLe m source
    _ = ((Finset.range M).sum (fun m => q ^ m)) * V := by
      rw [Finset.sum_mul]
    _ = ((1 - q ^ M) / (1 - q)) * V := by
      have hqNe : q ≠ 1 := ne_of_lt hqLt
      rw [geom_sum_eq hqNe]
      have hqSubOneNe : q - 1 ≠ 0 := sub_ne_zero.mpr hqNe
      have hOneSubQNe : 1 - q ≠ 0 := sub_ne_zero.mpr hqNe.symm
      field_simp [hqSubOneNe, hOneSubQNe]
      ring
    _ =
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
            H beta) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
            H beta)) * V := by
      rfl

/-- Finite partial sums are uniformly bounded by the full geometric-series
envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
      H beta
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_nonneg
        H beta hbeta hbetaPos hbetaCutoff
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_geometric
      H N hN beta hbeta hbetaPos hbetaCutoff B
      variation hVariationNonneg V hV hVariationLe M source
  have hRatio :
      (1 - q ^ M) / (1 - q) ≤ (1 : ℝ) / (1 - q) := by
    apply (div_le_div_iff_of_pos_right hOneSubQPos).2
    have hPowNonneg : 0 ≤ q ^ M := pow_nonneg hqNonneg M
    linarith
  calc
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
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
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
      rfl

/-- Every normalized finite persistent second-bootstrap resolvent is bounded by
V / (1 - alpha_H^(2)). -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanFiniteResolventProfile_le_one_sub_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      V /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
            H beta) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
      H beta
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
      H beta
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff
  have hOneSubQNe : 1 - q ≠ 0 :=
    ne_of_gt (sub_pos.mpr hqLt)
  have hPartial :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
        (1 - q)⁻¹ * V := by
    simpa [D, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  have hIdentity :
      n * (1 - q) = 1 - alpha := by
    simpa [n, alpha, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_one_sub_identity
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

/-- Every fixed-source persistent second-bootstrap variation orbit is summable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationIterate_summable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
            H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
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
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  exact summable_of_sum_range_le hIterNonneg hRange

/-- The unnormalized infinite variation sum is bounded by the persistent
second-bootstrap full geometric-series envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationTsum_le_inv_one_sub_rate_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation m source) ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
          H beta)⁻¹ * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
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
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe M source
  simpa [D, q] using
    (Real.tsum_le_of_sum_range_le hIterNonneg hRange)

/-- The normalized infinite persistent second-bootstrap random-scan resolvent
obeys the same V / (1 - alpha_H^(2)) bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanInfiniteResolventProfile_le_one_sub_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinCutoff
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      V /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
            H beta) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentRefinedTotalCoefficient
      H beta
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate
      H beta
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_lt_one
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
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanVariationTsum_le_inv_one_sub_rate_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe source
  have hIdentity :
      n * (1 - q) = 1 - alpha := by
    simpa [n, alpha, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapStrictPersistentFixedVolumeRandomScanRate_one_sub_identity
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
