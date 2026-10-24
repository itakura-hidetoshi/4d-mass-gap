import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralQuinticSixthRemainderV5_PX4
import Mathlib.Tactic

/-!
# P4-Q2-PX4S — real sixth-order determinant stability and true quartic jet tail

The original exact quartic Haar-moment jet has an authentic fifth coefficient.
A real two-by-two minor perturbation with O(beta^5) row errors and
O(beta) row differences has O(beta^6) determinant error.
The algebraic quartic jet tail begins at beta^6 after the authentic
Ward cancellation proved earlier. No rank or nonzero coefficient is postulated.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- If a determinant has a sixth-order approximation, its two
first-order columns retain that accuracy under sixth-order row
perturbations. This is a real-norm calculation, without new axioms. -/
theorem p4Q2PX4_realMinor_sixthOrder_stability
    (r L E₁ E₂ Q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (x y u v ex ey eu ev target : ℝ)
    (hx : ‖x‖ ≤ r * L) (hy : ‖y‖ ≤ r * L)
    (hu : ‖u‖ ≤ r * L) (hv : ‖v‖ ≤ r * L)
    (hex : ‖ex‖ ≤ r ^ 5 * E₁)
    (hey : ‖ey‖ ≤ r ^ 5 * E₁)
    (heu : ‖eu‖ ≤ r ^ 5 * E₂)
    (hev : ‖ev‖ ≤ r ^ 5 * E₂)
    (hDet : ‖x * u - y * v - target‖ ≤ r ^ 6 * Q) :
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
      r ^ 6 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hr0)]
  have hr4 : r ^ 4 ≤ 1 := by
    calc
      r ^ 4 = r ^ 2 * r ^ 2 := by ring
      _ ≤ 1 * 1 :=
        mul_le_mul hr2 hr2 (pow_nonneg hr0 2) (by norm_num)
      _ = 1 := by norm_num
  have hr10 : r ^ 10 ≤ r ^ 6 := by
    calc
      r ^ 10 = r ^ 6 * r ^ 4 := by ring
      _ ≤ r ^ 6 * 1 := mul_le_mul_of_nonneg_left hr4 (pow_nonneg hr0 6)
      _ = r ^ 6 := by ring
  have h51 (e z : ℝ)
      (he : ‖e‖ ≤ r ^ 5 * E₁) (hz : ‖z‖ ≤ r * L) :
      ‖e * z‖ ≤ r ^ 6 * E₁ * L := by
    calc
      ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
      _ ≤ (r ^ 5 * E₁) * (r * L) :=
        mul_le_mul he hz (norm_nonneg _) (by positivity)
      _ = r ^ 6 * E₁ * L := by ring
  have h15 (z e : ℝ)
      (hz : ‖z‖ ≤ r * L) (he : ‖e‖ ≤ r ^ 5 * E₂) :
      ‖z * e‖ ≤ r ^ 6 * E₂ * L := by
    calc
      ‖z * e‖ = ‖e * z‖ := by rw [mul_comm]
      _ ≤ r ^ 6 * E₂ * L := by
        calc
          ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
          _ ≤ (r ^ 5 * E₂) * (r * L) :=
            mul_le_mul he hz (norm_nonneg _) (by positivity)
          _ = r ^ 6 * E₂ * L := by ring
  have h55 (e f : ℝ)
      (he : ‖e‖ ≤ r ^ 5 * E₁) (hf : ‖f‖ ≤ r ^ 5 * E₂) :
      ‖e * f‖ ≤ r ^ 6 * E₁ * E₂ := by
    calc
      ‖e * f‖ = ‖e‖ * ‖f‖ := norm_mul _ _
      _ ≤ (r ^ 5 * E₁) * (r ^ 5 * E₂) :=
        mul_le_mul he hf (norm_nonneg _) (by positivity)
      _ = r ^ 10 * (E₁ * E₂) := by ring
      _ ≤ r ^ 6 * (E₁ * E₂) :=
        mul_le_mul_of_nonneg_right hr10 (mul_nonneg hE₁ hE₂)
      _ = r ^ 6 * E₁ * E₂ := by ring
  have hTerm₁ := h51 ex u hex hu
  have hTerm₂ := h15 x eu hx heu
  have hTerm₃ := h55 ex eu hex heu
  have hTerm₄ := h51 ey v hey hv
  have hTerm₅ := h15 y ev hy hev
  have hTerm₆ := h55 ey ev hey hev
  have hTri :
      ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
        ‖x * u - y * v - target‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := by
    have hEq :
        (x + ex) * (u + eu) - (y + ey) * (v + ev) - target =
          (x * u - y * v - target) +
            ((ex * u + x * eu + ex * eu) -
              (ey * v + y * ev + ey * ev)) := by ring
    rw [hEq]
    have h1 := norm_add_le (x * u - y * v - target)
      ((ex * u + x * eu + ex * eu) - (ey * v + y * ev + ey * ev))
    have h2 := norm_sub_le (ex * u + x * eu + ex * eu)
      (ey * v + y * ev + ey * ev)
    have h3 := norm_add_le (ex * u + x * eu) (ex * eu)
    have h4 := norm_add_le (ex * u) (x * eu)
    have h5 := norm_add_le (ey * v + y * ev) (ey * ev)
    have h6 := norm_add_le (ey * v) (y * ev)
    linarith
  calc
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
        ‖x * u - y * v - target‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := hTri
    _ ≤ r ^ 6 * Q +
          2 * (r ^ 6 * E₁ * L) + 2 * (r ^ 6 * E₂ * L) +
          2 * (r ^ 6 * E₁ * E₂) := by linarith
    _ = r ^ 6 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by ring


section OriginalFourthJetSixthTail
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "J1" => p4Q2PX_originalOneSlabFormalTaylor4 H
local notation "J2" => p4Q2PX_originalTwoSlabFormalTaylor4 H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "C7" => p4Q2PX_originalSeventhFourthJetCoefficient H
local notation "C8" => p4Q2PX_originalEighthFourthJetCoefficient H

/-- Full Ward-corrected genuine quartic-moment jet has precisely
the corrected fifth coefficient with sixth-order remainder. -/
theorem p4Q2PX4_originalFourthMomentJetMinor_sixthRemainder
    (beta : ℝ) (hsmall : ‖beta‖ ≤ 1) (A B C : Cfg) :
    ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
      (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A) -
      beta ^ 5 * C5 A B C‖ ≤
        ‖beta‖ ^ 6 *
          (‖C6 A B C‖ + ‖C7 A B C‖ + ‖C8 A B C‖) := by
  rw [p4Q2PX_originalFourthMomentJetMinor_afterActualWard H beta A B C]
  have hPoly :
      beta ^ 5 * C5 A B C + beta ^ 6 * C6 A B C +
        beta ^ 7 * C7 A B C + beta ^ 8 * C8 A B C -
          beta ^ 5 * C5 A B C =
        beta ^ 6 * C6 A B C +
          beta ^ 7 * C7 A B C + beta ^ 8 * C8 A B C := by ring
  rw [hPoly]
  have h7 : ‖beta‖ ^ 7 ≤ ‖beta‖ ^ 6 := by
    calc
      ‖beta‖ ^ 7 = ‖beta‖ ^ 6 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 6 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 6)
      _ = ‖beta‖ ^ 6 := by ring
  have h8 : ‖beta‖ ^ 8 ≤ ‖beta‖ ^ 6 := by
    calc
      ‖beta‖ ^ 8 = ‖beta‖ ^ 7 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 7 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 7)
      _ = ‖beta‖ ^ 7 := by ring
      _ ≤ ‖beta‖ ^ 6 := h7
  have h1 := norm_add_le
    (beta ^ 6 * C6 A B C + beta ^ 7 * C7 A B C)
    (beta ^ 8 * C8 A B C)
  have h2 := norm_add_le
    (beta ^ 6 * C6 A B C) (beta ^ 7 * C7 A B C)
  calc
    ‖beta ^ 6 * C6 A B C + beta ^ 7 * C7 A B C +
      beta ^ 8 * C8 A B C‖ ≤
        ‖beta ^ 6 * C6 A B C‖ +
          ‖beta ^ 7 * C7 A B C‖ + ‖beta ^ 8 * C8 A B C‖ := by linarith
    _ = ‖beta‖ ^ 6 * ‖C6 A B C‖ +
        ‖beta‖ ^ 7 * ‖C7 A B C‖ +
          ‖beta‖ ^ 8 * ‖C8 A B C‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    _ ≤ ‖beta‖ ^ 6 *
        (‖C6 A B C‖ + ‖C7 A B C‖ + ‖C8 A B C‖) := by
      have h7' := mul_le_mul_of_nonneg_right h7 (norm_nonneg (C7 A B C))
      have h8' := mul_le_mul_of_nonneg_right h8 (norm_nonneg (C8 A B C))
      nlinarith

end OriginalFourthJetSixthTail
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX4_realMinor_sixthOrder_stability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PX4_originalFourthMomentJetMinor_sixthRemainder
