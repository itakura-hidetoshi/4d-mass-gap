import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedCubicMomentsV5_PP3
import Mathlib.Tactic

/-!
# P4-Q2-PP4 — fifth-order stability for the genuine Wilson fourth coefficient

The original Wilson one- and two-slab cubic action jets, with the
unmodified full spatial Haar integral, have a complete fourth-order
three-boundary determinant coefficient (PP2). This file provides
quantitative fifth-order stability of real determinants when their
column Taylor errors are fourth order and the columns start at first
order. It also controls the entire fifth/sixth polynomial jet tail.
The bridge to the true Wilson minor follows by inserting PP3's genuine
quartic Haar remainder bounds, without any rank or nonvanishing axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PP4_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PP4_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PP4_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PP4_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PP4_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- If a determinant has a fifth-order approximation, its two
first-order columns retain that accuracy under fourth-order row
perturbations. This is a real-norm calculation, without new axioms. -/
theorem p4Q2PP4_realMinor_fifthOrder_stability
    (r L E₁ E₂ Q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL : 0 ≤ L) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (x y u v ex ey eu ev target : ℝ)
    (hx : ‖x‖ ≤ r * L) (hy : ‖y‖ ≤ r * L)
    (hu : ‖u‖ ≤ r * L) (hv : ‖v‖ ≤ r * L)
    (hex : ‖ex‖ ≤ r ^ 4 * E₁)
    (hey : ‖ey‖ ≤ r ^ 4 * E₁)
    (heu : ‖eu‖ ≤ r ^ 4 * E₂)
    (hev : ‖ev‖ ≤ r ^ 4 * E₂)
    (hDet : ‖x * u - y * v - target‖ ≤ r ^ 5 * Q) :
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev) - target‖ ≤
      r ^ 5 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hr0)]
  have hr3 : r ^ 3 ≤ 1 := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hr2 hr0
      _ ≤ 1 := by simpa only [mul_one] using hr1
  have hr8 : r ^ 8 ≤ r ^ 5 := by
    calc
      r ^ 8 = r ^ 5 * r ^ 3 := by ring
      _ ≤ r ^ 5 * 1 := mul_le_mul_of_nonneg_left hr3 (pow_nonneg hr0 5)
      _ = r ^ 5 := by ring
  have h41 (e z : ℝ)
      (he : ‖e‖ ≤ r ^ 4 * E₁) (hz : ‖z‖ ≤ r * L) :
      ‖e * z‖ ≤ r ^ 5 * E₁ * L := by
    calc
      ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
      _ ≤ (r ^ 4 * E₁) * (r * L) :=
        mul_le_mul he hz (norm_nonneg _) (by positivity)
      _ = r ^ 5 * E₁ * L := by ring
  have h14 (z e : ℝ)
      (hz : ‖z‖ ≤ r * L) (he : ‖e‖ ≤ r ^ 4 * E₂) :
      ‖z * e‖ ≤ r ^ 5 * E₂ * L := by
    calc
      ‖z * e‖ = ‖e * z‖ := by rw [mul_comm]
      _ ≤ r ^ 5 * E₂ * L := by
        calc
          ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
          _ ≤ (r ^ 4 * E₂) * (r * L) :=
            mul_le_mul he hz (norm_nonneg _) (by positivity)
          _ = r ^ 5 * E₂ * L := by ring
  have h44 (e f : ℝ)
      (he : ‖e‖ ≤ r ^ 4 * E₁) (hf : ‖f‖ ≤ r ^ 4 * E₂) :
      ‖e * f‖ ≤ r ^ 5 * E₁ * E₂ := by
    calc
      ‖e * f‖ = ‖e‖ * ‖f‖ := norm_mul _ _
      _ ≤ (r ^ 4 * E₁) * (r ^ 4 * E₂) :=
        mul_le_mul he hf (norm_nonneg _) (by positivity)
      _ = r ^ 8 * (E₁ * E₂) := by ring
      _ ≤ r ^ 5 * (E₁ * E₂) :=
        mul_le_mul_of_nonneg_right hr8 (mul_nonneg hE₁ hE₂)
      _ = r ^ 5 * E₁ * E₂ := by ring
  have hTerm₁ := h41 ex u hex hu
  have hTerm₂ := h14 x eu hx heu
  have hTerm₃ := h44 ex eu hex heu
  have hTerm₄ := h41 ey v hey hv
  have hTerm₅ := h14 y ev hy hev
  have hTerm₆ := h44 ey ev hey hev
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
    _ ≤ r ^ 5 * Q +
          2 * (r ^ 5 * E₁ * L) + 2 * (r ^ 5 * E₂ * L) +
          2 * (r ^ 5 * E₁ * E₂) := by linarith
    _ = r ^ 5 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by ring

section OriginalJetFifthBound
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "J1" => p4Q2PP2_originalOneSlabFormalTaylor3 H
local notation "J2" => p4Q2PP2_originalTwoSlabFormalTaylor3 H
local notation "C4" => p4Q2PP2_originalFourthCoefficient H
local notation "C5" => p4Q2PP2_originalFifthJetCoefficient H
local notation "C6" => p4Q2PP2_originalSixthJetCoefficient H

/-- After the genuine SU(2) Ward identity, the complete cubic-moment
jet determinant differs from beta^4 times the FULL correct coefficient
by at most a fifth-order term, for small real coupling. -/
theorem p4Q2PP4_originalCubicJetMinor_fifthOrderBound
    (beta : ℝ) (hsmall : ‖beta‖ ≤ 1) (A B C : Cfg) :
    ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
      (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A) -
      beta ^ 4 * C4 A B C‖ ≤
        ‖beta‖ ^ 5 * (‖C5 A B C‖ + ‖C6 A B C‖) := by
  rw [p4Q2PP2_originalCubicJetMinor_afterWard H beta A B C]
  have hPow : ‖beta‖ ^ 6 ≤ ‖beta‖ ^ 5 := by
    calc
      ‖beta‖ ^ 6 = ‖beta‖ ^ 5 * ‖beta‖ := by ring
      _ ≤ ‖beta‖ ^ 5 * 1 :=
        mul_le_mul_of_nonneg_left hsmall (pow_nonneg (norm_nonneg _) 5)
      _ = ‖beta‖ ^ 5 := by ring
  have hPoly :
      beta ^ 4 * C4 A B C + beta ^ 5 * C5 A B C +
        beta ^ 6 * C6 A B C - beta ^ 4 * C4 A B C =
          beta ^ 5 * C5 A B C + beta ^ 6 * C6 A B C := by ring
  rw [hPoly]
  calc
    ‖beta ^ 5 * C5 A B C + beta ^ 6 * C6 A B C‖ ≤
        ‖beta ^ 5 * C5 A B C‖ + ‖beta ^ 6 * C6 A B C‖ := norm_add_le _ _
    _ = ‖beta‖ ^ 5 * ‖C5 A B C‖ +
          ‖beta‖ ^ 6 * ‖C6 A B C‖ := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ ‖beta‖ ^ 5 * (‖C5 A B C‖ + ‖C6 A B C‖) := by
      have h := mul_le_mul_of_nonneg_right hPow (norm_nonneg (C6 A B C))
      nlinarith

end OriginalJetFifthBound
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP4_realMinor_fifthOrder_stability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP4_originalCubicJetMinor_fifthOrderBound
