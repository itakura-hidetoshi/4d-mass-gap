import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthJetSeventhTailV5_PZ5
import Mathlib.Tactic

/-!
# P4-Q2-PZ6 — real seventh-order determinant stability

An actual Wilson fifth-action-moment Taylor row differs from its
exact Haar-integrated literal row by O(beta^6), while both row
differences vanish at least to first order in beta. The resulting
TWO-BY-TWO determinant error is therefore O(beta^7), with all
quadratic sixth-error terms explicitly bounded.

This file proves the precise REAL-NORM algebraic stability theorem
needed for the original physical Wilson minor. It does not replace
either Haar posterior, add any unproved spectrum/rank assumption,
or claim that the sixth coefficient is nonzero.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Sixth-order errors on first-order real row differences give a
SEVENTH-order determinant error, retaining the product of both
sixth-order errors and its exact small-coupling bound. -/
theorem p4Q2PZ6_realMinor_seventhOrder_stability
    (r L E₁ E₂ Q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (x y u v ex ey eu ev target : ℝ)
    (hx : ‖x‖ ≤ r * L) (hy : ‖y‖ ≤ r * L)
    (hu : ‖u‖ ≤ r * L) (hv : ‖v‖ ≤ r * L)
    (hex : ‖ex‖ ≤ r ^ 6 * E₁)
    (hey : ‖ey‖ ≤ r ^ 6 * E₁)
    (heu : ‖eu‖ ≤ r ^ 6 * E₂)
    (hev : ‖ev‖ ≤ r ^ 6 * E₂)
    (hDet : ‖x * u - y * v - target‖ ≤ r ^ 7 * Q) :
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
      r ^ 7 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
  have hr5 : r ^ 5 ≤ 1 := by
    calc
      r ^ 5 ≤ (1 : ℝ) ^ 5 := pow_le_pow_left₀ hr0 hr1 5
      _ = 1 := by norm_num
  have hr12 : r ^ 12 ≤ r ^ 7 := by
    calc
      r ^ 12 = r ^ 7 * r ^ 5 := by ring
      _ ≤ r ^ 7 * 1 :=
        mul_le_mul_of_nonneg_left hr5 (pow_nonneg hr0 7)
      _ = r ^ 7 := by ring
  have h61 (e z : ℝ)
      (he : ‖e‖ ≤ r ^ 6 * E₁) (hz : ‖z‖ ≤ r * L) :
      ‖e * z‖ ≤ r ^ 7 * E₁ * L := by
    calc
      ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
      _ ≤ (r ^ 6 * E₁) * (r * L) :=
        mul_le_mul he hz (norm_nonneg _) (by positivity)
      _ = r ^ 7 * E₁ * L := by ring
  have h16 (z e : ℝ)
      (hz : ‖z‖ ≤ r * L) (he : ‖e‖ ≤ r ^ 6 * E₂) :
      ‖z * e‖ ≤ r ^ 7 * E₂ * L := by
    calc
      ‖z * e‖ = ‖e * z‖ := by rw [mul_comm]
      _ ≤ r ^ 7 * E₂ * L := by
        calc
          ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
          _ ≤ (r ^ 6 * E₂) * (r * L) :=
            mul_le_mul he hz (norm_nonneg _) (by positivity)
          _ = r ^ 7 * E₂ * L := by ring
  have h66 (e f : ℝ)
      (he : ‖e‖ ≤ r ^ 6 * E₁)
      (hf : ‖f‖ ≤ r ^ 6 * E₂) :
      ‖e * f‖ ≤ r ^ 7 * E₁ * E₂ := by
    calc
      ‖e * f‖ = ‖e‖ * ‖f‖ := norm_mul _ _
      _ ≤ (r ^ 6 * E₁) * (r ^ 6 * E₂) :=
        mul_le_mul he hf (norm_nonneg _) (by positivity)
      _ = r ^ 12 * (E₁ * E₂) := by ring
      _ ≤ r ^ 7 * (E₁ * E₂) :=
        mul_le_mul_of_nonneg_right hr12 (mul_nonneg hE₁ hE₂)
      _ = r ^ 7 * E₁ * E₂ := by ring
  have hTerm₁ := h61 ex u hex hu
  have hTerm₂ := h16 x eu hx heu
  have hTerm₃ := h66 ex eu hex heu
  have hTerm₄ := h61 ey v hey hv
  have hTerm₅ := h16 y ev hy hev
  have hTerm₆ := h66 ey ev hey hev
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
    _ ≤ r ^ 7 * Q +
          2 * (r ^ 7 * E₁ * L) + 2 * (r ^ 7 * E₂ * L) +
          2 * (r ^ 7 * E₁ * E₂) := by linarith
    _ = r ^ 7 *
      (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ6_realMinor_seventhOrder_stability
