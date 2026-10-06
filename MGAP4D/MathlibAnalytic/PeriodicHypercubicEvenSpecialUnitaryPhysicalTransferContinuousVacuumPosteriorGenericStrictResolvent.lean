import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalVolumeUniformDobrushinColumn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorStrictInfiniteResolvent
import Mathlib.Tactic

/-!
# Generic strict posterior random-scan resolvent from bidirectional Dobrushin data

The earlier strict posterior random-scan files specialized every scalar step to
the first-bootstrap fixed-volume coefficient.  PRs #5196--#5197 now provide an
actual canonical posterior matrix with one H- and N-independent coefficient
controlling both rows and columns.

This file factors the random-scan argument through the abstract strict
posterior Dobrushin structure itself.

For strict data D with column sums bounded by D.coefficient = alpha, define

  q_D = (n - 1 + alpha) / n,

where n is the finite number of spatial links.  Then

  0 <= q_D < 1,
  n * (1 - q_D) = 1 - alpha,

and every nonnegative pointwise envelope v <= V satisfies

  U^m v <= q_D^m V.

Although q_D approaches one when n grows, the normalized random-scan resolvent
contains the compensating factor n^(-1).  The exact identity above therefore
gives the volume-independent bound

  w_M(source) <= V / (1 - alpha),

and the same estimate for the infinite normalized resolvent.

Finally the canonical strict data from PR #5196 and the column theorem from
PR #5197 are substituted, yielding

  w_infty(source)
    <= V / (1 - alpha_bar(s,beta))

on the positive volume-uniform posterior Dobrushin interval.

No random-scan update time / Euclidean-time identification, spacing-scaled
continuum generator theorem, H1-D5 exact descent, or complete Yang--Mills
mass-gap claim is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance posteriorGenericStrictResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Random-scan contraction rate attached to arbitrary strict posterior
Dobrushin data. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) : ℝ :=
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  (n - 1 + D.coefficient) / n

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_nonneg
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnOne : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (periodicHypercubicEvenSpatialSliceLink_card_pos H)))
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
  dsimp [n]
  exact
    div_nonneg
      (add_nonneg (sub_nonneg.mpr hnOne) D.coefficient_nonneg)
      hnPos.le

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_lt_one
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
        D < 1 := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
  dsimp [n]
  apply (div_lt_one hnPos).2
  linarith [D.coefficient_lt_one]

/-- Exact cancellation identity behind the normalized resolvent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_one_sub_identity
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B) :
    let n : ℝ :=
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
    n *
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
            D) =
      1 - D.coefficient := by
  dsimp
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  change
    n * (1 - (n - 1 + D.coefficient) / n) =
      1 - D.coefficient
  field_simp [hnNe]
  ring

/-- A column bound by the strict coefficient gives one-step pointwise
random-scan contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanUpdatedVariation_le_rate_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
          D * V := by
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
        mul_le_mul_of_nonneg_right (hColumn source) hV
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
              simpa [n] using hCard
      _ ≤
        (n - 1) * V + alpha * V := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (hVariationLe source)
              (sub_nonneg.mpr hnOne))
            hWeighted
      _ = (n - 1 + alpha) * V := by ring
  have hCardBound' :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation source * n ≤
        (n - 1 + alpha) * V := by
    simpa [mul_comm] using hCardBound
  have hDiv :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation source ≤
        ((n - 1 + alpha) * V) / n :=
    (le_div_iff₀ hnPos).2 hCardBound'
  simpa [
    alpha,
    n,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate,
    div_mul_eq_mul_div] using hDiv

/-- Iteration gives the generic geometric pointwise envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_le_rate_pow_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V) :
    ∀ m source,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source ≤
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
          D) ^ m * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_nonneg
        D
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
      have hEnvelopeNonneg : 0 ≤ q ^ m * V :=
        mul_nonneg (pow_nonneg hqNonneg m) hV
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanUpdatedVariation_le_rate_mul
          D hColumn previous
          (q ^ m * V) hEnvelopeNonneg
          (fun e => by
            dsimp [previous]
            simpa [q] using ih e)
          source
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ]
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            previous source ≤
          q * (q ^ m * V) := by
            simpa [q] using hStep
        _ = q ^ (m + 1) * V := by
          rw [pow_succ]
          ring

/-- Finite variation sums are bounded by the exact geometric series. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_geometric
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
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
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
            D) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
            D)) * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_lt_one
        D
  have hOneSubQNe : 1 - q ≠ 0 :=
    ne_of_gt (sub_pos.mpr hqLt)
  have hGeom :
      (Finset.range M).sum (fun m => q ^ m) =
        (1 - q ^ M) / (1 - q) := by
    apply (eq_div_iff hOneSubQNe).2
    exact geom_sum_mul_neg q M
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
        simpa [q] using
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_le_rate_pow_mul
            D hColumn variation hVariationNonneg V hV hVariationLe m source
    _ =
      ((Finset.range M).sum (fun m => q ^ m)) * V := by
        rw [Finset.sum_mul]
    _ = ((1 - q ^ M) / (1 - q)) * V := by
      rw [hGeom]
    _ =
      ((1 -
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
            D) ^ M) /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
            D)) * V := by
      rfl

/-- Finite variation sums are bounded by the full geometric envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
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
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
          D)⁻¹ * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_nonneg
        D
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_lt_one
        D
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_geometric
      D hColumn variation hVariationNonneg V hV hVariationLe M source
  have hRatio :
      (1 - q ^ M) / (1 - q) ≤ (1 : ℝ) / (1 - q) := by
    apply (div_le_div_iff_of_pos_right hOneSubQPos).2
    have hPowNonneg : 0 ≤ q ^ M := pow_nonneg hqNonneg M
    linarith
  calc
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      ((1 - q ^ M) / (1 - q)) * V := by
        simpa [q] using hFinite
    _ ≤ ((1 : ℝ) / (1 - q)) * V :=
      mul_le_mul_of_nonneg_right hRatio hV
    _ = (1 - q)⁻¹ * V := by
      rw [one_div]
    _ =
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
          D)⁻¹ * V := by
      rfl

/-- After the exact random-scan normalization, every finite resolvent loses the
finite-volume factor n and is bounded only by the strict Dobrushin coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanFiniteResolventProfile_le_one_sub_coefficient
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
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
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      V / (1 - D.coefficient) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_lt_one
        D
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hOneSubQNe : 1 - q ≠ 0 := ne_of_gt hOneSubQPos
  have hPartial :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
        (1 - q)⁻¹ * V := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        D hColumn variation hVariationNonneg V hV hVariationLe M source
  have hIdentity :
      n * (1 - q) = 1 - D.coefficient := by
    simpa [n, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_one_sub_identity
        D
  have hNormalize :
      n⁻¹ * ((1 - q)⁻¹ * V) =
        V / (1 - D.coefficient) := by
    calc
      n⁻¹ * ((1 - q)⁻¹ * V) =
          V / (n * (1 - q)) := by
            field_simp [hnNe, hOneSubQNe]
      _ = V / (1 - D.coefficient) := by
        rw [hIdentity]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
  change
    n⁻¹ *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
      V / (1 - D.coefficient)
  calc
    n⁻¹ *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation M source ≤
      n⁻¹ * ((1 - q)⁻¹ * V) :=
        mul_le_mul_of_nonneg_left hPartial (inv_nonneg.mpr hnPos.le)
    _ = V / (1 - D.coefficient) := hNormalize

/-- Every generic strict posterior random-scan variation orbit is summable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationIterate_summable
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
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
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source) := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
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
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        D hColumn variation hVariationNonneg V hV hVariationLe M source
  exact summable_of_sum_range_le hIterNonneg hRange

/-- The unnormalized infinite variation sum is bounded by the full geometric
series envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationTsum_le_inv_one_sub_rate_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
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
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation m source) ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
          D)⁻¹ * V := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
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
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationPartialSum_le_inv_one_sub_rate_mul
        D hColumn variation hVariationNonneg V hV hVariationLe M source
  simpa [q] using
    (Real.tsum_le_of_sum_range_le hIterNonneg hRange)

/-- The normalized infinite resolvent has the same coefficient-only bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanInfiniteResolventProfile_le_one_sub_coefficient
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
        H N hN beta hbeta B)
    (hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanInfiniteResolventProfile
        D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      V / (1 - D.coefficient) := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let q :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate
      D
  have hnPos : 0 < n :=
    Nat.cast_pos.mpr (periodicHypercubicEvenSpatialSliceLink_card_pos H)
  have hnNe : n ≠ 0 := ne_of_gt hnPos
  have hqLt : q < 1 := by
    dsimp [q]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_lt_one
        D
  have hOneSubQPos : 0 < 1 - q := sub_pos.mpr hqLt
  have hOneSubQNe : 1 - q ≠ 0 := ne_of_gt hOneSubQPos
  have hTsum :
      (∑' m : ℕ,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          variation m source) ≤
        (1 - q)⁻¹ * V := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanVariationTsum_le_inv_one_sub_rate_mul
        D hColumn variation hVariationNonneg V hV hVariationLe source
  have hIdentity :
      n * (1 - q) = 1 - D.coefficient := by
    simpa [n, q] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanRate_one_sub_identity
        D
  have hNormalize :
      n⁻¹ * ((1 - q)⁻¹ * V) =
        V / (1 - D.coefficient) := by
    calc
      n⁻¹ * ((1 - q)⁻¹ * V) =
          V / (n * (1 - q)) := by
            field_simp [hnNe, hOneSubQNe]
      _ = V / (1 - D.coefficient) := by
        rw [hIdentity]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanInfiniteResolventProfile
  change
    n⁻¹ *
        (∑' m : ℕ,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source) ≤
      V / (1 - D.coefficient)
  calc
    n⁻¹ *
        (∑' m : ℕ,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
            variation m source) ≤
      n⁻¹ * ((1 - q)⁻¹ * V) :=
        mul_le_mul_of_nonneg_left hTsum (inv_nonneg.mpr hnPos.le)
    _ = V / (1 - D.coefficient) := hNormalize

/-- The concrete cutoff data expose exactly the H-independent scalar
coefficient used in PRs #5195--#5197. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_coefficient
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B).coefficient =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta := by
  rfl

/-- Canonical volume-uniform finite normalized resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanFiniteResolventProfile_le
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          H N hN s hs beta hbeta hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation M source ≤
      V /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  have hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient := by
    intro source
    simpa [D] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_columnSum_le_coefficient
        H N hN s hs beta hbeta hbetaCutoff B source
  have h :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanFiniteResolventProfile_le_one_sub_coefficient
      D hColumn variation hVariationNonneg V hV hVariationLe M source
  simpa [D] using h

/-- Canonical volume-uniform infinite normalized resolvent bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanInfiniteResolventProfile_le
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
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
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          H N hN s hs beta hbeta hbetaCutoff B).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        variation source ≤
      V /
        (1 -
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta) := by
  let D :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
      H N hN s hs beta hbeta hbetaCutoff B
  have hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ D.coefficient := by
    intro source
    simpa [D] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData_columnSum_le_coefficient
        H N hN s hs beta hbeta hbetaCutoff B source
  have h :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinRandomScanInfiniteResolventProfile_le_one_sub_coefficient
      D hColumn variation hVariationNonneg V hV hVariationLe source
  simpa [D] using h

end

end MathlibAnalytic
end MGAP4D
