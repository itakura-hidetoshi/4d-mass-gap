import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralSeventhCoefficientV5_PZ37M
import Mathlib.Tactic

/-!
# PZ37N — literal Wilson minor is nonzero at small positive coupling

For nonminimal even period, three genuinely distinct original half-spatial Wilson
action values force the seventh coefficient to be nonzero. PZ37M's *actual*
one/two-slab Wilson determinant then remains nonzero for every sufficiently
small positive coupling. This does not assert that three distinct physical
boundaries have already been constructed, or any volume-uniform estimate.
-/

namespace MGAP4D.MathlibAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

/-- The *literal* one- and two-slab Wilson minor is nonzero throughout a small
positive interval whenever the three physical boundary action values differ.
The radius may depend on H and all three boundaries. No new hypothesis
concerning a Haar moment, endpoint, or posterior is introduced. -/
theorem p4Q2PZ37N_originalNonminimalLiteralMinor_nonzero_smallPositive
    (hH : 1 ≤ H) (A B C : Cfg)
    (hAB : w A ≠ w B)
    (hAC : w A ≠ w C)
    (hBC : w B ≠ w C) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ beta : ℝ, 0 < beta → beta < epsilon →
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  let c : ℝ :=
    -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512
  have hV :
      PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C) ≠ 0 := by
    unfold PZ37VandermondeAlgebra.vandermonde
    exact mul_ne_zero
      (mul_ne_zero
        (sub_ne_zero.mpr hAB.symm)
        (sub_ne_zero.mpr hAC.symm))
      (sub_ne_zero.mpr hBC.symm)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact div_ne_zero (neg_ne_zero.mpr hV) (by norm_num)
  have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨K, hK, hTaylor⟩ :=
    p4Q2PZ37M_originalLiteralWilsonMinor_nonminimal_vandermonde H hH A B C
  have hKp : 0 < K + 1 := by linarith
  have hMp : 0 < 1 + ‖2 * M‖ := by positivity
  let epsilon : ℝ :=
    min 1 (min (1 / (1 + ‖2 * M‖)) (‖c‖ / (K + 1)))
  have heps : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (by norm_num)
      (lt_min (div_pos (by norm_num) hMp) (div_pos hcNorm hKp))
  have hepsOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    exact min_le_left _ _
  have hepsM : epsilon ≤ 1 / (1 + ‖2 * M‖) := by
    dsimp only [epsilon]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hepsC : epsilon ≤ ‖c‖ / (K + 1) := by
    dsimp only [epsilon]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨epsilon, heps, ?_⟩
  intro beta hb0 hbEps
  have hBeta : ‖beta‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hb0]
    exact (lt_of_lt_of_le hbEps hepsOne).le
  have hbM : beta * (1 + ‖2 * M‖) < 1 :=
    (lt_div_iff₀ hMp).mp (lt_of_lt_of_le hbEps hepsM)
  have hSmall : ‖beta * (2 * M)‖ ≤ 1 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hb0]
    nlinarith
  have hUpper : beta * (K + 1) < ‖c‖ :=
    (lt_div_iff₀ hKp).mp (lt_of_lt_of_le hbEps hepsC)
  have hKsmall : K * beta < ‖c‖ := by
    nlinarith
  have hHigher : K * ‖beta‖ ^ 8 < ‖beta ^ 7 * c‖ := by
    calc
      K * ‖beta‖ ^ 8 = beta ^ 7 * (K * beta) := by
        rw [Real.norm_eq_abs, abs_of_pos hb0]
        ring
      _ < beta ^ 7 * ‖c‖ :=
        mul_lt_mul_of_pos_left hKsmall (pow_pos hb0 7)
      _ = ‖beta ^ 7 * c‖ := by
        rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hb0]
  have hApprox :
      ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
        beta ^ 7 * c‖ ≤ K * ‖beta‖ ^ 8 := by
    simpa only [c] using hTaylor beta hBeta hSmall
  intro hzero
  rw [hzero, zero_sub, norm_neg] at hApprox
  exact (not_lt_of_ge hApprox) hHigher

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37N_originalNonminimalLiteralMinor_nonzero_smallPositive
