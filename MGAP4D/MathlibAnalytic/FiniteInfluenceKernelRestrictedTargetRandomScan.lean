import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelDeterministicSchedule
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Uniform random scan over a specified finite family of target coordinates.
The state/variation index `ι` may be larger than the actually updated target
family `τ`; `target` embeds each physical target into the carrier index. -/
def finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ)
    (source : ι) : ℝ :=
  (Fintype.card τ : ℝ)⁻¹ *
    ∑ t : τ,
      finiteInfluenceKernelUpdatedVariation K variation (target t) source

/-- Restricted-target random-scan updating preserves nonnegative profiles. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_nonneg
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (source : ι) :
    0 ≤ finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
      K target variation source := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun t _ =>
      finiteInfluenceKernelUpdatedVariation_nonneg
        K variation hVariation (target t) source)

/-- A restricted target scan is exactly the uniform average of the corresponding
singleton deterministic schedules. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_eq_uniformAverage_singletonSchedule
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target variation source =
      (Fintype.card τ : ℝ)⁻¹ *
        ∑ t : τ,
          finiteInfluenceKernelDeterministicScheduleVariation
            K variation [target t] source := by
  rfl

/-- When every carrier coordinate is an eligible target, the restricted target
scan is definitionally the repository's existing uniform random-scan update. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_id_eq
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K (fun e : ι => e) variation source =
      finiteInfluenceKernelRandomScanUpdatedVariation K variation source := by
  rfl

/-- Equivalently, the existing random-scan update is the uniform average of all
singleton deterministic schedules. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_eq_uniformAverage_singletonSchedule
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRandomScanUpdatedVariation K variation source =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          finiteInfluenceKernelDeterministicScheduleVariation
            K variation [target] source := by
  rfl

/-- Iterated restricted-target random-scan profile. -/
def finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => variation
  | n + 1 =>
      finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target
        (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation n)

@[simp] theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_zero
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation 0 = variation := rfl

@[simp] theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ)
    (n : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation (n + 1) =
      finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target
        (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation n) := rfl

/-- Iterated restricted-target profiles remain nonnegative. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_nonneg
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (n : ℕ)
    (source : ι) :
    0 ≤ finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
      K target variation n source := by
  induction n generalizing source with
  | zero => exact hVariation source
  | succ n ih =>
      rw [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      exact finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_nonneg
        K target _ (fun e => ih e) source

/-- The restricted-target iterate recovers the existing random-scan iterate
exactly when the eligible target family is the whole carrier (`target = id`). -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_id_eq
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (n : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K (fun e : ι => e) variation n =
      finiteInfluenceKernelRandomScanVariationIterate K variation n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      rw [finiteInfluenceKernelRandomScanVariationIterate_succ]
      rw [ih]
      funext source
      exact finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_id_eq
        K (finiteInfluenceKernelRandomScanVariationIterate K variation n) source

end

end MathlibAnalytic
end MGAP4D
