import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanPullbackResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- An unscanned auxiliary coordinate evolves by its previous value plus the
uniform average of the eligible-target influences into that coordinate. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_aux_eq
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hCard : 0 < Fintype.card τ)
    (aux : ι)
    (hAux : ∀ t : τ, aux ≠ target t)
    (variation : ι → ℝ) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target variation aux =
      variation aux +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ t : τ, K.influence (target t) aux * variation (target t) := by
  have hCardReal : (Fintype.card τ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCard)
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  calc
    (Fintype.card τ : ℝ)⁻¹ *
        ∑ t : τ, finiteInfluenceKernelUpdatedVariation K variation (target t) aux =
      (Fintype.card τ : ℝ)⁻¹ *
        ∑ t : τ,
          (variation aux + K.influence (target t) aux * variation (target t)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro t _ht
        simp [finiteInfluenceKernelUpdatedVariation, hAux t]
    _ =
      (Fintype.card τ : ℝ)⁻¹ *
        ((∑ _t : τ, variation aux) +
          ∑ t : τ, K.influence (target t) aux * variation (target t)) := by
        rw [Finset.sum_add_distrib]
    _ =
      (Fintype.card τ : ℝ)⁻¹ * (∑ _t : τ, variation aux) +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ t : τ, K.influence (target t) aux * variation (target t) := by
        ring
    _ =
      variation aux +
        (Fintype.card τ : ℝ)⁻¹ *
          ∑ t : τ, K.influence (target t) aux * variation (target t) := by
        congr 1
        simp [hCardReal]

/-- If every eligible-target influence into an unscanned auxiliary coordinate
is bounded by `auxCoefficient`, then the auxiliary iterate is bounded by its
initial value plus `auxCoefficient` times the normalized accumulated eligible
variation mass. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_aux_le_initial_add_normalizedAccumulatedEligible
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq τ]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (hCard : 0 < Fintype.card τ)
    (aux : ι)
    (hAux : ∀ t : τ, aux ≠ target t)
    (auxCoefficient : ℝ)
    (hAuxCoefficientNonneg : 0 ≤ auxCoefficient)
    (hAuxInfluence : ∀ t : τ, K.influence (target t) aux ≤ auxCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (M : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation M aux ≤
      variation aux +
        auxCoefficient *
          ((Fintype.card τ : ℝ)⁻¹ *
            (∑ m ∈ Finset.range M,
              ∑ t : τ,
                finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                  K target variation m (target t))) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      let vM :=
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation M
      have hvMNonneg : ∀ e, 0 ≤ vM e := by
        intro e
        dsimp [vM]
        exact
          finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_nonneg
            K target variation hVariationNonneg M e
      have hWeighted :
          (Fintype.card τ : ℝ)⁻¹ *
              (∑ t : τ, K.influence (target t) aux * vM (target t)) ≤
            auxCoefficient *
              ((Fintype.card τ : ℝ)⁻¹ * ∑ t : τ, vM (target t)) := by
        have hSum :
            (∑ t : τ, K.influence (target t) aux * vM (target t)) ≤
              ∑ t : τ, auxCoefficient * vM (target t) := by
          apply Finset.sum_le_sum
          intro t _ht
          exact
            mul_le_mul_of_nonneg_right
              (hAuxInfluence t) (hvMNonneg (target t))
        have hInvNonneg : 0 ≤ (Fintype.card τ : ℝ)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg _)
        calc
          (Fintype.card τ : ℝ)⁻¹ *
              (∑ t : τ, K.influence (target t) aux * vM (target t)) ≤
            (Fintype.card τ : ℝ)⁻¹ *
              (∑ t : τ, auxCoefficient * vM (target t)) :=
            mul_le_mul_of_nonneg_left hSum hInvNonneg
          _ =
            auxCoefficient *
              ((Fintype.card τ : ℝ)⁻¹ * ∑ t : τ, vM (target t)) := by
            rw [← Finset.mul_sum]
            ring
      rw [finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      rw [
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_aux_eq
          K target hCard aux hAux vM]
      calc
        vM aux +
            (Fintype.card τ : ℝ)⁻¹ *
              (∑ t : τ, K.influence (target t) aux * vM (target t)) ≤
          (variation aux +
              auxCoefficient *
                ((Fintype.card τ : ℝ)⁻¹ *
                  (∑ m ∈ Finset.range M,
                    ∑ t : τ,
                      finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                        K target variation m (target t)))) +
            auxCoefficient *
              ((Fintype.card τ : ℝ)⁻¹ * ∑ t : τ, vM (target t)) := by
          exact add_le_add ih hWeighted
        _ =
          variation aux +
            auxCoefficient *
              ((Fintype.card τ : ℝ)⁻¹ *
                (∑ m ∈ Finset.range (M + 1),
                  ∑ t : τ,
                    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                      K target variation m (target t))) := by
          rw [Finset.sum_range_succ]
          dsimp [vM]
          ring

/-- A strict row bound on the scanned pullback kernel therefore gives a uniform
resolvent bound on every unscanned auxiliary coordinate whose incoming
eligible influences have a uniform pointwise bound. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_aux_le_resolvent
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
    (aux : ι)
    (hAux : ∀ t : τ, aux ≠ target t)
    (auxCoefficient : ℝ)
    (hAuxCoefficientNonneg : 0 ≤ auxCoefficient)
    (hAuxInfluence : ∀ t : τ, K.influence (target t) aux ≤ auxCoefficient)
    (variation : ι → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (hVariationAuxZero : variation aux = 0)
    (M : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target variation M aux ≤
      auxCoefficient *
        ((∑ t : τ, variation (target t)) * (1 - rowCoefficient)⁻¹) := by
  have hAuxAccum :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_aux_le_initial_add_normalizedAccumulatedEligible
      K target hCard aux hAux auxCoefficient hAuxCoefficientNonneg
      hAuxInfluence variation hVariationNonneg M
  have hEligible :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_normalized_sum_eligibleTotal_le_resolvent
      K target hTarget hCard rowCoefficient hRowNonneg hRowLtOne hRowSum
      variation hVariationNonneg M
  rw [hVariationAuxZero, zero_add] at hAuxAccum
  exact hAuxAccum.trans
    (mul_le_mul_of_nonneg_left hEligible hAuxCoefficientNonneg)

end

end MathlibAnalytic
end MGAP4D
