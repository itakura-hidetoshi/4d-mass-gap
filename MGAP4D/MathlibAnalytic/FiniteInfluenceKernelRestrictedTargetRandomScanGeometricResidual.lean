import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScan
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Restrict a nonnegative influence kernel on `Sum τ σ` to the physical left
coordinates.  This is the kernel seen by a random scan that is allowed to update
only `Sum.inl` coordinates. -/
def finiteInfluenceKernelSumLeftRestriction
    {τ σ : Type}
    [DecidableEq τ]
    [Fintype τ]
    [DecidableEq σ]
    [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ)) :
    FiniteNonnegativeInfluenceKernelData τ :=
  { influence := fun target source =>
      K.influence (Sum.inl target) (Sum.inl source)
    influence_nonneg := by
      intro target source
      exact K.influence_nonneg (Sum.inl target) (Sum.inl source)
    influence_diagonal_zero := by
      intro e
      exact K.influence_diagonal_zero (Sum.inl e) }

/-- On a physical left source, restricted scanning over `Sum.inl` targets is
exactly the ordinary full random scan of the left-restricted kernel. -/
theorem finiteInfluenceKernelSumRestrictedTargetRandomScanUpdatedVariation_inl_eq
    {τ σ : Type}
    [DecidableEq τ]
    [Fintype τ]
    [DecidableEq σ]
    [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ))
    (variation : Sum τ σ → ℝ)
    (source : τ) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K (fun target : τ => Sum.inl target) variation (Sum.inl source) =
      finiteInfluenceKernelRandomScanUpdatedVariation
        (finiteInfluenceKernelSumLeftRestriction K)
        (fun e : τ => variation (Sum.inl e)) source := by
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    finiteInfluenceKernelRandomScanUpdatedVariation
  apply congrArg (fun x : ℝ => (Fintype.card τ : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro target _
  by_cases hEq : source = target
  · subst target
    simp [finiteInfluenceKernelUpdatedVariation,
      finiteInfluenceKernelSumLeftRestriction]
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]

/-- The entire left projection of the restricted-target iterate agrees exactly
with the existing full random-scan iterate of the left-restricted kernel. -/
theorem finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inl_eq
    {τ σ : Type}
    [DecidableEq τ]
    [Fintype τ]
    [DecidableEq σ]
    [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ))
    (variation : Sum τ σ → ℝ)
    (n : ℕ)
    (source : τ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K (fun target : τ => Sum.inl target) variation n (Sum.inl source) =
      finiteInfluenceKernelRandomScanVariationIterate
        (finiteInfluenceKernelSumLeftRestriction K)
        (fun e : τ => variation (Sum.inl e)) n source := by
  induction n generalizing source with
  | zero => rfl
  | succ n ih =>
      rw [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      rw [finiteInfluenceKernelRandomScanVariationIterate_succ]
      rw [finiteInfluenceKernelSumRestrictedTargetRandomScanUpdatedVariation_inl_eq]
      apply congrArg
        (fun v : τ → ℝ =>
          finiteInfluenceKernelRandomScanUpdatedVariation
            (finiteInfluenceKernelSumLeftRestriction K) v source)
      funext e
      exact ih e

/-- Existing reciprocal column contraction applies verbatim to the physical
left projection of a restricted-target scan. -/
theorem finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inl_le_rate_pow_mul
    {τ σ : Type}
    [DecidableEq τ]
    [Fintype τ]
    [DecidableEq σ]
    [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ))
    (hCard : 0 < Fintype.card τ)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : τ,
        finiteInfluenceKernelColumnSum
          (finiteInfluenceKernelSumLeftRestriction K) source ≤
            columnCoefficient)
    (variation : Sum τ σ → ℝ)
    (hVariationNonneg : ∀ e : τ, 0 ≤ variation (Sum.inl e))
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e : τ, variation (Sum.inl e) ≤ bound)
    (n : ℕ)
    (source : τ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K (fun target : τ => Sum.inl target) variation n (Sum.inl source) ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          τ columnCoefficient ^ n * bound := by
  rw [finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inl_eq]
  exact
    finiteInfluenceKernelRandomScanVariationIterate_le_rate_pow_mul
      (finiteInfluenceKernelSumLeftRestriction K)
      hCard columnCoefficient hColumnNonneg hColumnSum
      (fun e : τ => variation (Sum.inl e))
      hVariationNonneg bound hBoundNonneg hVariationBound n source

/-- A represented right-source coordinate is never reset by a physical-left
restricted scan.  One step is its previous value plus the exact averaged forcing
from the physical left coordinates. -/
theorem finiteInfluenceKernelSumRestrictedTargetRandomScanUpdatedVariation_inr_eq
    {τ σ : Type}
    [DecidableEq τ]
    [Fintype τ]
    [DecidableEq σ]
    [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ))
    (hCard : 0 < Fintype.card τ)
    (variation : Sum τ σ → ℝ)
    (source : σ) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K (fun target : τ => Sum.inl target) variation (Sum.inr source) =
      variation (Sum.inr source) +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target) := by
  have hCardCastNe : (Fintype.card τ : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCard
  have hSum :
      (∑ target : τ,
        finiteInfluenceKernelUpdatedVariation
          K variation (Sum.inl target) (Sum.inr source)) =
        (Fintype.card τ : ℝ) * variation (Sum.inr source) +
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target) := by
    calc
      (∑ target : τ,
        finiteInfluenceKernelUpdatedVariation
          K variation (Sum.inl target) (Sum.inr source)) =
        ∑ target : τ,
          (variation (Sum.inr source) +
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target)) := by
        apply Finset.sum_congr rfl
        intro target _
        simp [finiteInfluenceKernelUpdatedVariation]
      _ = (Fintype.card τ : ℝ) * variation (Sum.inr source) +
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target) := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  rw [hSum]
  have hInvCard :
      (Fintype.card τ : ℝ)⁻¹ * (Fintype.card τ : ℝ) = 1 :=
    inv_mul_cancel₀ hCardCastNe
  calc
    (Fintype.card τ : ℝ)⁻¹ *
        ((Fintype.card τ : ℝ) * variation (Sum.inr source) +
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target)) =
      ((Fintype.card τ : ℝ)⁻¹ * (Fintype.card τ : ℝ)) *
          variation (Sum.inr source) +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target) := by ring
    _ = variation (Sum.inr source) +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              variation (Sum.inl target) := by
      rw [hInvCard, one_mul]

/-- A represented right-source coordinate accumulates only geometrically
shrinking left forcing.  This is the restricted-target analogue of a geometric
terminal residual: the right coordinate itself is not asserted to contract. -/
theorem finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inr_le_geometricResidual
    {τ σ : Type} [DecidableEq τ] [Fintype τ] [DecidableEq σ] [Fintype σ]
    (K : FiniteNonnegativeInfluenceKernelData (Sum τ σ))
    (hCard : 0 < Fintype.card τ) (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum : ∀ source : τ,
      finiteInfluenceKernelColumnSum (finiteInfluenceKernelSumLeftRestriction K) source ≤ columnCoefficient)
    (variation : Sum τ σ → ℝ)
    (hVariationNonneg : ∀ e : τ, 0 ≤ variation (Sum.inl e))
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e : τ, variation (Sum.inl e) ≤ bound)
    (source : σ) (sourceCoefficient : ℝ)
    (hSourceSum : (∑ target : τ, K.influence (Sum.inl target) (Sum.inr source)) ≤ sourceCoefficient)
    (n : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K (fun target : τ => Sum.inl target) variation n (Sum.inr source) ≤
      variation (Sum.inr source) +
        (Fintype.card τ : ℝ)⁻¹ * sourceCoefficient * bound *
          Finset.sum (Finset.range n)
            (fun j => finiteInfluenceKernelReciprocalRandomScanRate τ columnCoefficient ^ j) := by
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate τ columnCoefficient
  have hRateNonneg : 0 ≤ rate := by
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCard columnCoefficient hColumnNonneg
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hLeftBound (target : τ) :
          finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K (fun e : τ => Sum.inl e) variation n (Sum.inl target) ≤
            rate ^ n * bound := by
        simpa [rate] using
          finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inl_le_rate_pow_mul
            K hCard columnCoefficient hColumnNonneg hColumnSum
            variation hVariationNonneg bound hBoundNonneg hVariationBound
            n target
      have hBoundNNonneg : 0 ≤ rate ^ n * bound :=
        mul_nonneg (pow_nonneg hRateNonneg n) hBoundNonneg
      have hForcingBound :
          (∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K (fun e : τ => Sum.inl e) variation n (Sum.inl target)) ≤
            sourceCoefficient * (rate ^ n * bound) := by
        calc
          (∑ target : τ,
            K.influence (Sum.inl target) (Sum.inr source) *
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K (fun e : τ => Sum.inl e) variation n (Sum.inl target)) ≤
            ∑ target : τ,
              K.influence (Sum.inl target) (Sum.inr source) *
                (rate ^ n * bound) := by
            apply Finset.sum_le_sum
            intro target _
            exact mul_le_mul_of_nonneg_left
              (hLeftBound target)
              (K.influence_nonneg (Sum.inl target) (Sum.inr source))
          _ = (∑ target : τ,
                K.influence (Sum.inl target) (Sum.inr source)) *
              (rate ^ n * bound) := by
            rw [Finset.sum_mul]
          _ ≤ sourceCoefficient * (rate ^ n * bound) :=
            mul_le_mul_of_nonneg_right hSourceSum hBoundNNonneg
      rw [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      rw [finiteInfluenceKernelSumRestrictedTargetRandomScanUpdatedVariation_inr_eq
        (K := K) (hCard := hCard)
        (variation :=
          finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
            K (fun e : τ => Sum.inl e) variation n)
        (source := source)]
      calc
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K (fun e : τ => Sum.inl e) variation n (Sum.inr source) +
            (Fintype.card τ : ℝ)⁻¹ *
              ∑ target : τ,
                K.influence (Sum.inl target) (Sum.inr source) *
                  finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                    K (fun e : τ => Sum.inl e) variation n (Sum.inl target) ≤
          (variation (Sum.inr source) +
            (Fintype.card τ : ℝ)⁻¹ * sourceCoefficient * bound *
              Finset.sum (Finset.range n) (fun j => rate ^ j)) +
            (Fintype.card τ : ℝ)⁻¹ *
              (sourceCoefficient * (rate ^ n * bound)) := by
          exact add_le_add ih
            (mul_le_mul_of_nonneg_left hForcingBound
              (inv_nonneg.mpr (Nat.cast_nonneg _)))
        _ = variation (Sum.inr source) +
            (Fintype.card τ : ℝ)⁻¹ * sourceCoefficient * bound *
              Finset.sum (Finset.range (n + 1)) (fun j => rate ^ j) := by
          rw [Finset.sum_range_succ]
          ring

end

end MathlibAnalytic
end MGAP4D
