import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScan
import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Pull an influence kernel back to the finite family of coordinates that are
actually eligible for a restricted random scan. -/
noncomputable def finiteInfluenceKernelRestrictedTargetPullback
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι) :
    FiniteNonnegativeInfluenceKernelData τ where
  influence t s := K.influence (target t) (target s)
  influence_nonneg t s := K.influence_nonneg (target t) (target s)
  influence_diagonal_zero t := K.influence_diagonal_zero (target t)

/-- On an injectively embedded eligible target family, one restricted random
scan evaluated on an eligible coordinate is exactly the ordinary random scan
for the pulled-back kernel. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_target_eq_pullback
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hTarget : Function.Injective target)
    (variation : ι → ℝ)
    (source : τ) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target variation (target source) =
      finiteInfluenceKernelRandomScanUpdatedVariation
        (finiteInfluenceKernelRestrictedTargetPullback K target)
        (fun t => variation (target t)) source := by
  classical
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    finiteInfluenceKernelRandomScanUpdatedVariation
  congr 1
  apply Finset.sum_congr rfl
  intro t _ht
  unfold finiteInfluenceKernelUpdatedVariation
  by_cases hEq : source = t
  · subst source
    simp [finiteInfluenceKernelRestrictedTargetPullback]
  · have hTargetNe : target source ≠ target t := by
      intro h
      exact hEq (hTarget h)
    simp [hEq, hTargetNe, finiteInfluenceKernelRestrictedTargetPullback]

/-- The eligible-coordinate restriction of every finite restricted-scan
iterate is the ordinary random-scan iterate for the pulled-back kernel. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_target_eq_pullback
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hTarget : Function.Injective target)
    (variation : ι → ℝ)
    (n : ℕ)
    (source : τ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation n (target source) =
      finiteInfluenceKernelRandomScanVariationIterate
        (finiteInfluenceKernelRestrictedTargetPullback K target)
        (fun t => variation (target t)) n source := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
            K target variation (n + 1) (target source) =
          finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
            K target
            (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target variation n)
            (target source) := by
              rfl
        _ =
          finiteInfluenceKernelRandomScanUpdatedVariation
            (finiteInfluenceKernelRestrictedTargetPullback K target)
            (fun t =>
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K target variation n (target t))
            source := by
              exact
                finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_target_eq_pullback
                  K target hTarget
                  (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                    K target variation n)
                  source
        _ =
          finiteInfluenceKernelRandomScanUpdatedVariation
            (finiteInfluenceKernelRestrictedTargetPullback K target)
            (finiteInfluenceKernelRandomScanVariationIterate
              (finiteInfluenceKernelRestrictedTargetPullback K target)
              (fun t => variation (target t)) n)
            source := by
              congr 2
              funext t
              exact ih t
        _ =
          finiteInfluenceKernelRandomScanVariationIterate
            (finiteInfluenceKernelRestrictedTargetPullback K target)
            (fun t => variation (target t)) (n + 1) source := by
              rfl

/-- A row bound for the pulled-back eligible kernel yields geometric
contraction of the total variation carried by eligible coordinates, even when
the ambient carrier contains additional coordinates that are never scanned. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_eligibleTotal_le_rate_pow_mul
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hTarget : Function.Injective target)
    (hCard : 0 < Fintype.card τ)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ t : τ,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K target) t ≤
            rowCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (n : ℕ) :
    (∑ t : τ,
      finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation n (target t)) ≤
      finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient ^ n *
        ∑ t : τ, variation (target t) := by
  have hPulled :=
    finiteInfluenceKernelRandomScanVariationIterate_total_le_rate_pow_mul
      (finiteInfluenceKernelRestrictedTargetPullback K target)
      hCard rowCoefficient hRowNonneg hRowSum
      (fun t => variation (target t))
      (fun t => hVariationNonneg (target t)) n
  calc
    (∑ t : τ,
      finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation n (target t)) =
      finiteProductVariationTotal
        (finiteInfluenceKernelRandomScanVariationIterate
          (finiteInfluenceKernelRestrictedTargetPullback K target)
          (fun t => variation (target t)) n) := by
            unfold finiteProductVariationTotal
            apply Finset.sum_congr rfl
            intro t _ht
            exact
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_target_eq_pullback
                K target hTarget variation n t
    _ ≤
      finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient ^ n *
        finiteProductVariationTotal (fun t => variation (target t)) :=
          hPulled
    _ =
      finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient ^ n *
        ∑ t : τ, variation (target t) := by
          rfl

/-- Summing the eligible total variation over finitely many restricted-scan
steps gives the corresponding finite geometric series. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_sum_eligibleTotal_le_geometric
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hTarget : Function.Injective target)
    (hCard : 0 < Fintype.card τ)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ t : τ,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K target) t ≤
            rowCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ) :
    (∑ m ∈ Finset.range M,
      ∑ t : τ,
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation m (target t)) ≤
      (∑ t : τ, variation (target t)) *
        finiteRealGeometricSeries
          (finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient) M := by
  calc
    (∑ m ∈ Finset.range M,
      ∑ t : τ,
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation m (target t)) ≤
      ∑ m ∈ Finset.range M,
        finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient ^ m *
          ∑ t : τ, variation (target t) := by
            apply Finset.sum_le_sum
            intro m hm
            exact
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_eligibleTotal_le_rate_pow_mul
                K target hTarget hCard rowCoefficient hRowNonneg hRowSum
                variation hVariationNonneg m
    _ =
      (∑ t : τ, variation (target t)) *
        finiteRealGeometricSeries
          (finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient) M := by
            unfold finiteRealGeometricSeries
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring

/-- Under a strict eligible-row coefficient, the cardinality-normalized
accumulated eligible variation has a uniform resolvent bound. The random-scan
cardinality cancels exactly, so the final denominator is one minus the row
coefficient. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_normalized_sum_eligibleTotal_le_resolvent
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hTarget : Function.Injective target)
    (hCard : 0 < Fintype.card τ)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ t : τ,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K target) t ≤
            rowCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ) :
    (Fintype.card τ : ℝ)⁻¹ *
        (∑ m ∈ Finset.range M,
          ∑ t : τ,
            finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target variation m (target t)) ≤
      (∑ t : τ, variation (target t)) * (1 - rowCoefficient)⁻¹ := by
  let rate := finiteInfluenceKernelReciprocalRandomScanRate τ rowCoefficient
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard rowCoefficient hRowNonneg
  have hRateLtOne : rate < 1 :=
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      hCard rowCoefficient hRowLtOne
  have hAccum :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_sum_eligibleTotal_le_geometric
      K target hTarget hCard rowCoefficient hRowNonneg hRowSum
      variation hVariationNonneg M
  have hGeom :=
    finiteRealGeometricSeries_le_inv_one_sub
      rate hRateNonneg hRateLtOne M
  have hInitialNonneg :
      0 ≤ ∑ t : τ, variation (target t) :=
    Finset.sum_nonneg fun t _ => hVariationNonneg (target t)
  have hInvCardNonneg : 0 ≤ (Fintype.card τ : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hCancel :
      (Fintype.card τ : ℝ)⁻¹ * (1 - rate)⁻¹ =
        (1 - rowCoefficient)⁻¹ :=
    inv_card_mul_inv_one_sub_reciprocalRate
      hCard rowCoefficient hRowLtOne
  calc
    (Fintype.card τ : ℝ)⁻¹ *
        (∑ m ∈ Finset.range M,
          ∑ t : τ,
            finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target variation m (target t)) ≤
      (Fintype.card τ : ℝ)⁻¹ *
        ((∑ t : τ, variation (target t)) *
          finiteRealGeometricSeries rate M) :=
      mul_le_mul_of_nonneg_left hAccum hInvCardNonneg
    _ ≤
      (Fintype.card τ : ℝ)⁻¹ *
        ((∑ t : τ, variation (target t)) * (1 - rate)⁻¹) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hGeom hInitialNonneg)
          hInvCardNonneg
    _ =
      ((Fintype.card τ : ℝ)⁻¹ * (1 - rate)⁻¹) *
        (∑ t : τ, variation (target t)) := by
      ring
    _ =
      (1 - rowCoefficient)⁻¹ *
        (∑ t : τ, variation (target t)) := by
      rw [hCancel]
    _ =
      (∑ t : τ, variation (target t)) * (1 - rowCoefficient)⁻¹ := by
      ring

end

end MathlibAnalytic
end MGAP4D
