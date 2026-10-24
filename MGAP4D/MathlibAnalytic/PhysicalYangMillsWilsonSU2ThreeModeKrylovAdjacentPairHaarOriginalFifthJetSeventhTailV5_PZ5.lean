import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralSixthRowRemainderV5_PZ4
import Mathlib.Tactic

/-!
# P4-Q2-PZ5 — genuine fifth Wilson-moment jet, explicit seventh-order tail

The EXACT original fifth-action-moment Wilson minor has the
genuine sixth jet coefficient D6 after the PY9D fifth Ward vanishing,
with algebraic terms of degree seven through ten only.

For |beta| <= 1 the full jet remainder is bounded by |beta|^7 times
the actual norms of D7, D8, D9 and D10. Those coefficients come from
the unchanged one- and two-slab original Wilson Haar moments.

The analytic literal Wilson-minor seventh-order stability is a
separate step. No fabricated spectral gap or nonzero coefficient,
new axiom, sorry/admit, or independently factorized posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section OriginalFifthMomentJetSeventhTail
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "J5₁" => p4Q2PZ1_originalOneSlabFormalTaylor5 H
local notation "J5₂" => p4Q2PZ1_originalTwoSlabFormalTaylor5 H
local notation "D6" => p4Q2PZ1_originalSixthFifthJetCoefficient H
local notation "D7" => p4Q2PZ1_originalSeventhFifthJetCoefficient H
local notation "D8" => p4Q2PZ1_originalEighthFifthJetCoefficient H
local notation "D9" => p4Q2PZ1_originalNinthFifthJetCoefficient H
local notation "D10" => p4Q2PZ1_originalTenthFifthJetCoefficient H

/-- The complete fifth-moment Wilson jet has its EXACT corrected
sixth coefficient D6 and an algebraic seventh-order remainder.
All coefficients are built from genuine original Wilson action
moments, and the period-two exceptional case is included. -/
theorem p4Q2PZ5_originalFifthMomentJetMinor_seventhRemainder
    (beta : ℝ) (hsmall : ‖beta‖ ≤ 1) (A B C : Cfg) :
    ‖(J5₁ beta B - J5₁ beta A) * (J5₂ beta C - J5₂ beta A) -
      (J5₁ beta C - J5₁ beta A) * (J5₂ beta B - J5₂ beta A) -
      beta ^ 6 * D6 A B C‖ ≤
        ‖beta‖ ^ 7 *
          (‖D7 A B C‖ + ‖D8 A B C‖ +
           ‖D9 A B C‖ + ‖D10 A B C‖) := by
  rw [p4Q2PZ1_originalFifthMomentJetMinor_afterUniversalWard H beta A B C]
  have hPoly :
      beta ^ 6 * D6 A B C + beta ^ 7 * D7 A B C +
        beta ^ 8 * D8 A B C + beta ^ 9 * D9 A B C +
        beta ^ 10 * D10 A B C -
        beta ^ 6 * D6 A B C =
        beta ^ 7 * D7 A B C + beta ^ 8 * D8 A B C +
          beta ^ 9 * D9 A B C + beta ^ 10 * D10 A B C := by ring
  rw [hPoly]
  have h8 : ‖beta‖ ^ 8 ≤ ‖beta‖ ^ 7 := by
    calc
      ‖beta‖ ^ 8 = ‖beta‖ ^ 7 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 7 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 7)
      _ = ‖beta‖ ^ 7 := by ring
  have h9 : ‖beta‖ ^ 9 ≤ ‖beta‖ ^ 7 := by
    calc
      ‖beta‖ ^ 9 = ‖beta‖ ^ 8 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 8 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 8)
      _ = ‖beta‖ ^ 8 := by ring
      _ ≤ ‖beta‖ ^ 7 := h8
  have h10 : ‖beta‖ ^ 10 ≤ ‖beta‖ ^ 7 := by
    calc
      ‖beta‖ ^ 10 = ‖beta‖ ^ 9 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 9 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 9)
      _ = ‖beta‖ ^ 9 := by ring
      _ ≤ ‖beta‖ ^ 7 := h9
  have h1 := norm_add_le
    (beta ^ 7 * D7 A B C + beta ^ 8 * D8 A B C +
      beta ^ 9 * D9 A B C)
    (beta ^ 10 * D10 A B C)
  have h2 := norm_add_le
    (beta ^ 7 * D7 A B C + beta ^ 8 * D8 A B C)
    (beta ^ 9 * D9 A B C)
  have h3 := norm_add_le
    (beta ^ 7 * D7 A B C) (beta ^ 8 * D8 A B C)
  calc
    ‖beta ^ 7 * D7 A B C + beta ^ 8 * D8 A B C +
        beta ^ 9 * D9 A B C + beta ^ 10 * D10 A B C‖ ≤
      ‖beta ^ 7 * D7 A B C‖ + ‖beta ^ 8 * D8 A B C‖ +
        ‖beta ^ 9 * D9 A B C‖ + ‖beta ^ 10 * D10 A B C‖ := by
      linarith
    _ = ‖beta‖ ^ 7 * ‖D7 A B C‖ +
        ‖beta‖ ^ 8 * ‖D8 A B C‖ +
          ‖beta‖ ^ 9 * ‖D9 A B C‖ +
            ‖beta‖ ^ 10 * ‖D10 A B C‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul,
        norm_pow, norm_pow, norm_pow, norm_pow]
    _ ≤ ‖beta‖ ^ 7 *
        (‖D7 A B C‖ + ‖D8 A B C‖ +
          ‖D9 A B C‖ + ‖D10 A B C‖) := by
      have h8' := mul_le_mul_of_nonneg_right h8 (norm_nonneg (D8 A B C))
      have h9' := mul_le_mul_of_nonneg_right h9 (norm_nonneg (D9 A B C))
      have h10' := mul_le_mul_of_nonneg_right h10 (norm_nonneg (D10 A B C))
      nlinarith

end OriginalFifthMomentJetSeventhTail
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ5_originalFifthMomentJetMinor_seventhRemainder
