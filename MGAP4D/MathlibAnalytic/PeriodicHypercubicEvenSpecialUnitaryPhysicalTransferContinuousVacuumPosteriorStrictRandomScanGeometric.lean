import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFixedVolumeStrictDobrushin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Strict posterior random-scan geometric variation contraction

PR #5180 constructs, at every fixed finite side H and sufficiently small
positive beta, a strict posterior Dobrushin coefficient alpha_H(beta)<1.

The exact random-scan variation identity from PR #5165 is transpose-oriented:

  n (U v)(s)
    = (n - 1) v(s) + sum_t c(t,s) v(t).

The coefficient used in PR #5180 is the total finite influence mass, so it
controls columns as well as rows.  Therefore if 0 <= v <= V pointwise,

  U v <= q_H(beta) V,

with

  q_H(beta) = (n - 1 + alpha_H(beta)) / n < 1.

Iteration gives

  U^m v <= q_H(beta)^m V,

and hence pointwise geometric decay at every fixed finite volume inside the
constructed strict Dobrushin neighborhood.

No volume-uniform cutoff or Euclidean-time identification is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance posteriorStrictRandomScanGeometricSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The intrinsic spatial-link carrier is nonempty. -/
theorem
    periodicHypercubicEvenSpatialSliceLink_card_pos
    (H : ℕ) :
    0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.card_pos_iff.mpr
    ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
        simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
      ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- Column sum of the zero-depth refined first-bootstrap influence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedColumnSum
    (H : ℕ)
    (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
      H beta target source

/-- Every column is bounded by the same total finite influence coefficient
used for rows in PR #5180. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedColumnSum_le_totalCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedColumnSum
        H beta source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedColumnSum
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
  rw [Finset.sum_comm]
  apply
    Finset.single_le_sum
      (fun s _ =>
        Finset.sum_nonneg fun t _ => by
          unfold
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
          exact
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRefinedInfluence_nonneg
              H beta hbeta
              (fun _target _source =>
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
                  H beta 0)
              (fun _target _source =>
                periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_nonneg
                  H beta hbeta 0)
              t s)
      (Finset.mem_univ source)

/-- The concrete strict first-bootstrap data inherit the same column bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData_columnSum_le_coefficient
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
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).influence target source) ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
        H N hN beta hbeta hbetaPos hbetaCutoff B).coefficient := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  change
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedInfluence
        H beta target source) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
        H beta
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedColumnSum_le_totalCoefficient
      H beta hbeta source

/-- Fixed-volume strict random-scan variation contraction factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
    (H : ℕ)
    (beta : ℝ) : ℝ :=
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  (n - 1 + alpha) / n

/-- The fixed-volume random-scan rate is nonnegative at nonnegative coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
        H beta := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnOne : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (periodicHypercubicEvenSpatialSliceLink_card_pos H)))
  have hAlpha : 0 ≤ alpha := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient_nonneg
        H beta hbeta
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
  dsimp [n, alpha]
  exact div_nonneg (add_nonneg (sub_nonneg.mpr hnOne) hAlpha) hnPos.le

/-- Inside the fixed-volume Dobrushin cutoff, the random-scan rate is strictly
below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_lt_one
    (H : ℕ)
    (beta : ℝ)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
        H beta < 1 := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapZeroDepthRefinedTotalCoefficient
      H beta
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hAlpha :
      alpha < 1 := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff_totalCoefficient_lt_one
        H beta hbetaPos hbetaCutoff
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
  dsimp [n, alpha]
  apply (div_lt_one hnPos).2
  linarith

/-- One strict posterior random-scan step contracts every nonnegative
pointwise variation envelope by the fixed-volume rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanUpdatedVariation_le_rate_mul
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
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let alpha : ℝ := D.coefficient
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnOne : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hEdge))
  have hColumn :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source) ≤ alpha := by
    dsimp [alpha]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData_columnSum_le_coefficient
        H N hN beta hbeta hbetaPos hbetaCutoff B source
  have hWeighted :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target) ≤
        alpha * V := by
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * V := by
            apply Finset.sum_le_sum
            intro target _hTarget
            exact
              mul_le_mul_of_nonneg_left
                (hVariationLe target)
                (D.influence_nonneg target source)
      _ =
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) * V := by
            rw [Finset.sum_mul]
      _ ≤ alpha * V :=
        mul_le_mul_of_nonneg_right hColumn hV
  have hCard :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_card_mul_eq
      D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      variation hEdge source
  have hCardBound :
      n *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation source ≤
        (n - 1 + alpha) * V := by
    calc
      n *
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation source =
        (n - 1) * variation source +
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            D.influence target source * variation target := by
              simpa [n, D] using hCard
      _ ≤
        (n - 1) * V + alpha * V := by
          apply add_le_add
          · exact
              mul_le_mul_of_nonneg_left
                (hVariationLe source)
                (sub_nonneg.mpr hnOne)
          · exact hWeighted
      _ = (n - 1 + alpha) * V := by ring
  have hDiv :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation source ≤
        ((n - 1 + alpha) * V) / n :=
    (le_div_iff₀ hnPos).2 hCardBound
  simpa [
    D,
    alpha,
    n,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate,
    div_mul_eq_mul_div] using hDiv

/-- Every finite random-scan variation iterate contracts by the geometric
factor q^m. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationIterate_le_rate_pow_mul
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
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V) :
    ∀ m source,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
            H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source ≤
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta) ^ m * V := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
      H N hN beta hbeta hbetaPos hbetaCutoff B
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
      H beta
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_nonneg
        H beta hbeta
  intro m
  induction m with
  | zero =>
      intro source
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
      ] using hVariationLe source
  | succ m ih =>
      intro source
      let previous :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m
      have hPreviousNonneg :
          ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ previous e := by
        intro e
        dsimp [previous]
        exact
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation hVariationNonneg m e
      have hEnvelopeNonneg : 0 ≤ q ^ m * V :=
        mul_nonneg (pow_nonneg hqNonneg m) hV
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanUpdatedVariation_le_rate_mul
          H N hN beta hbeta hbetaPos hbetaCutoff B
          previous hPreviousNonneg
          (q ^ m * V) hEnvelopeNonneg
          (fun e => by
            dsimp [previous]
            simpa [q, D] using ih e)
          source
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ]
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            previous source ≤
          q * (q ^ m * V) := by
            simpa [D, q] using hStep
        _ = q ^ (m + 1) * V := by
          rw [pow_succ]
          ring

/-- The strict fixed-volume random-scan rate has powers tending to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_pow_tendsto_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaPos : 0 < beta)
    (hbetaCutoff :
      beta <
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinCutoff
          H) :
    Tendsto
      (fun m : ℕ =>
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
          H beta) ^ m)
      atTop
      (𝓝 0) := by
  exact
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_nonneg
        H beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_lt_one
        H beta hbetaPos hbetaCutoff)

/-- Every fixed source variation iterate tends to zero geometrically. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationIterate_tendsto_zero
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
    Tendsto
      (fun m =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
            H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source)
      atTop
      (𝓝 0) := by
  have hUpper :
      ∀ m : ℕ,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
              H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source ≤
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta) ^ m * V :=
    fun m =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanVariationIterate_le_rate_pow_mul
        H N hN beta hbeta hbetaPos hbetaCutoff B
        variation hVariationNonneg V hV hVariationLe m source
  have hLower :
      ∀ m : ℕ,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
              H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source :=
    fun m =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeDobrushinData
          H N hN beta hbeta hbetaPos hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation hVariationNonneg m source
  have hGeom :
      Tendsto
        (fun m : ℕ =>
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate
            H beta) ^ m * V)
        atTop
        (𝓝 0) := by
    simpa using
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapFixedVolumeRandomScanRate_pow_tendsto_zero
        H beta hbeta hbetaPos hbetaCutoff).mul_const V
  exact squeeze_zero hLower hUpper hGeom

end

end MathlibAnalytic
end MGAP4D
