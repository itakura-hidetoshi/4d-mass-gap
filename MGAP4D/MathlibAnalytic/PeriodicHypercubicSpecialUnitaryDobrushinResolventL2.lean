import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinSchurL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteSchurResolvent

/-- Weighted Young inequality in the exact form needed for a Schur-resolvent
estimate. -/
theorem two_mul_le_alpha_mul_sq_add_inv_mul_sq
    (alpha x y : ℝ)
    (hAlpha : 0 < alpha) :
    2 * x * y ≤ alpha * x ^ 2 + alpha⁻¹ * y ^ 2 := by
  have hAlphaNe : alpha ≠ 0 := ne_of_gt hAlpha
  have hRewrite :
      alpha * x ^ 2 + alpha⁻¹ * y ^ 2 =
        (alpha ^ 2 * x ^ 2 + y ^ 2) / alpha := by
    field_simp [hAlphaNe]
  rw [hRewrite]
  apply (le_div_iff₀ hAlpha).2
  nlinarith [sq_nonneg (alpha * x - y)]

/-- A finite real matrix with squared `ℓ²` operator bound `alpha²`, where
`0 ≤ alpha < 1`, has a quantitatively coercive residual `I - matrix`.

This is the finite resolvent estimate needed after a Dobrushin martingale-defect
identity has produced an `I - C` residual profile. -/
theorem residual_l2_sq_lower_bound
    {ι : Type*}
    [Fintype ι]
    (matrix : ι → ι → ℝ)
    (alpha : ℝ)
    (hAlphaNonneg : 0 ≤ alpha)
    (hAlphaLtOne : alpha < 1)
    (hSchur : ∀ vector : ι → ℝ,
      (∑ i, (∑ j, matrix i j * vector j) ^ 2) ≤
        alpha ^ 2 * ∑ i, vector i ^ 2)
    (vector : ι → ℝ) :
    (1 - alpha) ^ 2 * ∑ i, vector i ^ 2 ≤
      ∑ i, (vector i - ∑ j, matrix i j * vector j) ^ 2 := by
  classical
  let action : ι → ℝ := fun i => ∑ j, matrix i j * vector j
  let energy : ℝ := ∑ i, vector i ^ 2
  let actionEnergy : ℝ := ∑ i, action i ^ 2
  let cross : ℝ := ∑ i, vector i * action i
  let residualEnergy : ℝ := ∑ i, (vector i - action i) ^ 2
  have hEnergyNonneg : 0 ≤ energy := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (vector i)
  have hActionEnergyNonneg : 0 ≤ actionEnergy := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (action i)
  have hActionEnergy : actionEnergy ≤ alpha ^ 2 * energy := by
    simpa [actionEnergy, action, energy] using hSchur vector
  have hResidualExpand :
      residualEnergy = energy + actionEnergy - 2 * cross := by
    dsimp [residualEnergy, energy, actionEnergy, cross]
    calc
      (∑ i, (vector i - action i) ^ 2) =
          ∑ i, (vector i ^ 2 + action i ^ 2 -
            2 * (vector i * action i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, vector i ^ 2) + (∑ i, action i ^ 2) -
          2 * ∑ i, vector i * action i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
  by_cases hAlphaZero : alpha = 0
  · subst alpha
    have hActionEnergyLe : actionEnergy ≤ 0 := by
      simpa using hActionEnergy
    have hActionEnergyZero : actionEnergy = 0 :=
      le_antisymm hActionEnergyLe hActionEnergyNonneg
    have hActionZero (i : ι) : action i = 0 := by
      have hTerm : action i ^ 2 ≤ actionEnergy := by
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg (action j)) (Finset.mem_univ i)
      rw [hActionEnergyZero] at hTerm
      nlinarith [sq_nonneg (action i)]
    have hCrossZero : cross = 0 := by
      dsimp [cross]
      apply Finset.sum_eq_zero
      intro i _
      rw [hActionZero]
      ring
    change (1 - 0) ^ 2 * energy ≤ residualEnergy
    rw [hResidualExpand, hActionEnergyZero, hCrossZero]
    simp
  · have hAlphaPos : 0 < alpha :=
      lt_of_le_of_ne hAlphaNonneg (Ne.symm hAlphaZero)
    have hYoung (i : ι) :
        2 * vector i * action i ≤
          alpha * vector i ^ 2 + alpha⁻¹ * action i ^ 2 :=
      two_mul_le_alpha_mul_sq_add_inv_mul_sq
        alpha (vector i) (action i) hAlphaPos
    have hCrossBound :
        2 * cross ≤ alpha * energy + alpha⁻¹ * actionEnergy := by
      calc
        2 * cross = ∑ i, 2 * vector i * action i := by
          dsimp [cross]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ ∑ i,
            (alpha * vector i ^ 2 + alpha⁻¹ * action i ^ 2) :=
          Finset.sum_le_sum fun i _ => hYoung i
        _ = alpha * energy + alpha⁻¹ * actionEnergy := by
          dsimp [energy, actionEnergy]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
    have hAlphaInvMul : alpha * alpha⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hAlphaPos)
    have hInvOne : 1 ≤ alpha⁻¹ := by
      by_contra hNot
      have hInvLt : alpha⁻¹ < 1 := lt_of_not_ge hNot
      have hMulLt := mul_lt_mul_of_pos_left hInvLt hAlphaPos
      rw [hAlphaInvMul] at hMulLt
      have hOneLtAlpha : 1 < alpha := by
        simpa using hMulLt
      exact (not_lt_of_ge hAlphaLtOne.le) hOneLtAlpha
    have hCoeffNonpos : 1 - alpha⁻¹ ≤ 0 := by
      linarith
    have hScaledAction :
        (1 - alpha⁻¹) * (alpha ^ 2 * energy) ≤
          (1 - alpha⁻¹) * actionEnergy :=
      mul_le_mul_of_nonpos_left hActionEnergy hCoeffNonpos
    have hResidualLower :
        energy + actionEnergy -
            (alpha * energy + alpha⁻¹ * actionEnergy) ≤
          residualEnergy := by
      rw [hResidualExpand]
      exact sub_le_sub_left hCrossBound (energy + actionEnergy)
    calc
      (1 - alpha) ^ 2 * energy =
          (1 - alpha) * energy +
            (1 - alpha⁻¹) * (alpha ^ 2 * energy) := by
        field_simp [ne_of_gt hAlphaPos]
        ring
      _ ≤ (1 - alpha) * energy +
          (1 - alpha⁻¹) * actionEnergy := by
        linarith
      _ = energy + actionEnergy -
          (alpha * energy + alpha⁻¹ * actionEnergy) := by
        ring
      _ ≤ residualEnergy := hResidualLower

end FiniteSchurResolvent

/-- The actual periodic compact-Haar `SU(N)` Dobrushin matrix has a uniformly
coercive finite `ℓ²` resolvent throughout the explicit strict Dobrushin region. -/
theorem periodicHypercubicSpecialUnitaryDobrushinInfluence_residual_l2_sq_lower_bound
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (vector : PeriodicHypercubicEdge n → ℝ) :
    (1 - periodicHypercubicSpecialUnitaryDobrushinCoefficient beta) ^ 2 *
        ∑ target, vector target ^ 2 ≤
      ∑ target,
        (vector target -
          ∑ source,
            periodicHypercubicSpecialUnitaryDobrushinInfluence
              n N hN beta beta_nonneg target source * vector source) ^ 2 := by
  apply FiniteSchurResolvent.residual_l2_sq_lower_bound
    (periodicHypercubicSpecialUnitaryDobrushinInfluence
      n N hN beta beta_nonneg)
    (periodicHypercubicSpecialUnitaryDobrushinCoefficient beta)
  · unfold periodicHypercubicSpecialUnitaryDobrushinCoefficient
    exact mul_nonneg (by norm_num)
      (compactHaarOscillationInfluence_nonneg (by positivity))
  · simpa [periodicHypercubicSpecialUnitaryDobrushinCoefficient] using
      periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
        beta hBetaLt
  · exact periodicHypercubicSpecialUnitaryDobrushinInfluence_l2_sq_le
      n N hn hN beta beta_nonneg

end

end MathlibAnalytic
end MGAP4D
