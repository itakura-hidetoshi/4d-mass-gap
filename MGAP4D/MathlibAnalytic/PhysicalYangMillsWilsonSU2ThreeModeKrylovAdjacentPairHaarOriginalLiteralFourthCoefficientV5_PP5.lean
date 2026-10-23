import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourthCoefficientStabilityV5_PP4
import Mathlib.Tactic

/-!
# P4-Q2-PP5 — true Wilson integrated fourth coefficient, fifth-order error

PP and PP3 give fourth-order uniform remainders for the ORIGINAL
one- and two-slab SU(2) Wilson Haar kernels and identify their genuine
Haar-integrated third action moments. PP2 and PP4 give the exact
post-Ward determinant coefficient. Combining these facts with a
finite-volume real determinant perturbation estimate shows the literal
three-spatial-configuration Wilson minor equals beta^4 times that FULL
coefficient up to O(beta^5). The crucial cubic cross contribution
cannot be omitted. No assumed nonzero coefficient, fabricated witness,
rank-three axiom, spectral surrogate or changed Wilson posterior.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PP5_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PP5_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PP5_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PP5_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PP5_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalPhysicalFourthCoefficient
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "J1" => p4Q2PP2_originalOneSlabFormalTaylor3 H
local notation "J2" => p4Q2PP2_originalTwoSlabFormalTaylor3 H
local notation "F" => p4Q2IV_originalWilsonUnitHaarKernelSection H
local notation "G" => p4Q2PJ_originalWilsonLiteralTwoSlabKernel H
local notation "C4" => p4Q2PP2_originalFourthCoefficient H
local notation "C5" => p4Q2PP2_originalFifthJetCoefficient H
local notation "C6" => p4Q2PP2_originalSixthJetCoefficient H

private theorem p4Q2PP5_jetOne_difference
    (beta : ℝ) (A D : Cfg) :
    J1 beta D - J1 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A) +
          beta ^ 3 / 6 * (c D - c A) := by
  unfold p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PK_originalOneSlabFormalTaylor2
  ring

private theorem p4Q2PP5_jetTwo_difference
    (beta : ℝ) (A D : Cfg) :
    J2 beta D - J2 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
          beta ^ 3 / 6 * (g D - g A) := by
  unfold p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

/-- The ACTUAL original double-Haar three-configuration Wilson minor
has the FULL fourth coefficient, including third-jet cross terms,
with a fifth-order quantitative error at every fixed finite H and
triple A,B,C. The constant is finite and independent of beta. -/
theorem p4Q2PP5_originalLiteralWilsonMinor_fourthCoefficient
    (A B C : Cfg) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
            beta ^ 4 * C4 A B C‖ ≤ C₀ * ‖beta‖ ^ 5 := by
  let L : ℝ :=
    1 + (‖a B - a A‖ + ‖a C - a A‖) +
      (‖b B - b A‖ + ‖b C - b A‖) +
      (‖c B - c A‖ + ‖c C - c A‖) +
      2 * (‖d B - d A‖ + ‖d C - d A‖) +
      (‖g B - g A‖ + ‖g C - g A‖)
  let E₁ : ℝ := 2 * ‖M‖ ^ 4
  let E₂ : ℝ := 2 * ‖2 * M‖ ^ 4
  let Q : ℝ := ‖C5 A B C‖ + ‖C6 A B C‖
  let C₀ : ℝ :=
    Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro beta hBeta hSmall
  let r : ℝ := ‖beta‖
  have hr0 : 0 ≤ r := norm_nonneg beta
  have hSmallOne : ‖beta * M‖ ≤ 1 := by
    have heq : ‖beta * (2 * M)‖ = 2 * ‖beta * M‖ := by
      rw [show beta * (2 * M) = 2 * (beta * M) by ring, norm_mul]
      norm_num
    rw [heq] at hSmall
    linarith
  have hr2 : r ^ 2 ≤ r := by
    calc
      r ^ 2 = r * r := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hBeta hr0
      _ = r := by ring
  have hr3 : r ^ 3 ≤ r := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_left hr2 hr0
      _ = r ^ 2 := by ring
      _ ≤ r := hr2
  have hHalf : ‖beta ^ 2 / 2‖ ≤ r := by
    calc
      ‖beta ^ 2 / 2‖ = r ^ 2 / 2 := by
        simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr2, hr0]
  have hSixth : ‖beta ^ 3 / 6‖ ≤ r := by
    calc
      ‖beta ^ 3 / 6‖ = r ^ 3 / 6 := by
        simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr3, hr0]
  have hJ1 (D : Cfg) :
      ‖J1 beta D - J1 beta A‖ ≤
        r * (‖a D - a A‖ + ‖b D - b A‖ + ‖c D - c A‖) := by
    rw [p4Q2PP5_jetOne_difference H beta A D]
    have hTri :
        ‖beta * (a D - a A) +
          beta ^ 2 / 2 * (b D - b A) +
            beta ^ 3 / 6 * (c D - c A)‖ ≤
        ‖beta * (a D - a A)‖ +
          ‖beta ^ 2 / 2 * (b D - b A)‖ +
            ‖beta ^ 3 / 6 * (c D - c A)‖ := by
      have h1 := norm_add_le
        (beta * (a D - a A) + beta ^ 2 / 2 * (b D - b A))
        (beta ^ 3 / 6 * (c D - c A))
      have h2 := norm_add_le
        (beta * (a D - a A)) (beta ^ 2 / 2 * (b D - b A))
      linarith
    calc
      ‖beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A) +
          beta ^ 3 / 6 * (c D - c A)‖ ≤
        ‖beta * (a D - a A)‖ +
          ‖beta ^ 2 / 2 * (b D - b A)‖ +
          ‖beta ^ 3 / 6 * (c D - c A)‖ := hTri
      _ = r * ‖a D - a A‖ +
            ‖beta ^ 2 / 2‖ * ‖b D - b A‖ +
            ‖beta ^ 3 / 6‖ * ‖c D - c A‖ := by
        rw [norm_mul, norm_mul, norm_mul]
      _ ≤ r * (‖a D - a A‖ + ‖b D - b A‖ + ‖c D - c A‖) := by
        have h2 := mul_le_mul_of_nonneg_right hHalf (norm_nonneg (b D - b A))
        have h3 := mul_le_mul_of_nonneg_right hSixth (norm_nonneg (c D - c A))
        nlinarith
  have hJ2 (D : Cfg) :
      ‖J2 beta D - J2 beta A‖ ≤
        r * (‖a D - a A‖ + ‖b D - b A‖ +
          2 * ‖d D - d A‖ + ‖g D - g A‖) := by
    rw [p4Q2PP5_jetTwo_difference H beta A D]
    have hSum :
        ‖(b D - b A) + 2 * (d D - d A)‖ ≤
          ‖b D - b A‖ + 2 * ‖d D - d A‖ := by
      calc
        _ ≤ ‖b D - b A‖ + ‖2 * (d D - d A)‖ := norm_add_le _ _
        _ = ‖b D - b A‖ + 2 * ‖d D - d A‖ := by
          rw [norm_mul]
          norm_num
    have hTri :
        ‖beta * (a D - a A) +
          beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
            beta ^ 3 / 6 * (g D - g A)‖ ≤
          ‖beta * (a D - a A)‖ +
            ‖beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A))‖ +
            ‖beta ^ 3 / 6 * (g D - g A)‖ := by
      have h1 := norm_add_le
        (beta * (a D - a A) +
          beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)))
        (beta ^ 3 / 6 * (g D - g A))
      have h2 := norm_add_le
        (beta * (a D - a A))
        (beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)))
      linarith
    calc
      ‖beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
          beta ^ 3 / 6 * (g D - g A)‖ ≤
        ‖beta * (a D - a A)‖ +
          ‖beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A))‖ +
          ‖beta ^ 3 / 6 * (g D - g A)‖ := hTri
      _ = r * ‖a D - a A‖ +
            ‖beta ^ 2 / 2‖ *
              ‖(b D - b A) + 2 * (d D - d A)‖ +
            ‖beta ^ 3 / 6‖ * ‖g D - g A‖ := by
        rw [norm_mul, norm_mul, norm_mul]
      _ ≤ r * (‖a D - a A‖ + ‖b D - b A‖ +
            2 * ‖d D - d A‖ + ‖g D - g A‖) := by
        have h2 := mul_le_mul_of_nonneg_right hHalf
          (norm_nonneg ((b D - b A) + 2 * (d D - d A)))
        have h3 := mul_le_mul_of_nonneg_right hSixth (norm_nonneg (g D - g A))
        have hs := mul_le_mul_of_nonneg_left hSum hr0
        nlinarith
  have hLB₁ :
      ‖a B - a A‖ + ‖b B - b A‖ + ‖c B - c A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) +
        ‖a C - a A‖ + ‖b C - b A‖ + ‖c C - c A‖ +
        2 * (‖d B - d A‖ + ‖d C - d A‖) +
        (‖g B - g A‖ + ‖g C - g A‖) := by positivity
    calc
      ‖a B - a A‖ + ‖b B - b A‖ + ‖c B - c A‖ ≤
        (‖a B - a A‖ + ‖b B - b A‖ + ‖c B - c A‖) +
          ((1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ + ‖c C - c A‖ +
            2 * (‖d B - d A‖ + ‖d C - d A‖) +
            (‖g B - g A‖ + ‖g C - g A‖)) :=
        le_add_of_nonneg_right hExtra
      _ = L := by dsimp only [L]; ring
  have hLC₁ :
      ‖a C - a A‖ + ‖b C - b A‖ + ‖c C - c A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) +
        ‖a B - a A‖ + ‖b B - b A‖ + ‖c B - c A‖ +
        2 * (‖d B - d A‖ + ‖d C - d A‖) +
        (‖g B - g A‖ + ‖g C - g A‖) := by positivity
    calc
      ‖a C - a A‖ + ‖b C - b A‖ + ‖c C - c A‖ ≤
        (‖a C - a A‖ + ‖b C - b A‖ + ‖c C - c A‖) +
          ((1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ + ‖c B - c A‖ +
            2 * (‖d B - d A‖ + ‖d C - d A‖) +
            (‖g B - g A‖ + ‖g C - g A‖)) :=
        le_add_of_nonneg_right hExtra
      _ = L := by dsimp only [L]; ring
  have hLB₂ :
      ‖a B - a A‖ + ‖b B - b A‖ +
        2 * ‖d B - d A‖ + ‖g B - g A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) +
        ‖a C - a A‖ + ‖b C - b A‖ +
        (‖c B - c A‖ + ‖c C - c A‖) +
        2 * ‖d C - d A‖ + ‖g C - g A‖ := by positivity
    calc
      ‖a B - a A‖ + ‖b B - b A‖ +
        2 * ‖d B - d A‖ + ‖g B - g A‖ ≤
        (‖a B - a A‖ + ‖b B - b A‖ +
          2 * ‖d B - d A‖ + ‖g B - g A‖) +
          ((1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ +
            (‖c B - c A‖ + ‖c C - c A‖) +
            2 * ‖d C - d A‖ + ‖g C - g A‖) :=
        le_add_of_nonneg_right hExtra
      _ = L := by dsimp only [L]; ring
  have hLC₂ :
      ‖a C - a A‖ + ‖b C - b A‖ +
        2 * ‖d C - d A‖ + ‖g C - g A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) +
        ‖a B - a A‖ + ‖b B - b A‖ +
        (‖c B - c A‖ + ‖c C - c A‖) +
        2 * ‖d B - d A‖ + ‖g B - g A‖ := by positivity
    calc
      ‖a C - a A‖ + ‖b C - b A‖ +
        2 * ‖d C - d A‖ + ‖g C - g A‖ ≤
        (‖a C - a A‖ + ‖b C - b A‖ +
          2 * ‖d C - d A‖ + ‖g C - g A‖) +
          ((1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ +
            (‖c B - c A‖ + ‖c C - c A‖) +
            2 * ‖d B - d A‖ + ‖g B - g A‖) :=
        le_add_of_nonneg_right hExtra
      _ = L := by dsimp only [L]; ring
  have hJ1B :
      ‖J1 beta B - J1 beta A‖ ≤ r * L :=
    (hJ1 B).trans (mul_le_mul_of_nonneg_left hLB₁ hr0)
  have hJ1C :
      ‖J1 beta C - J1 beta A‖ ≤ r * L :=
    (hJ1 C).trans (mul_le_mul_of_nonneg_left hLC₁ hr0)
  have hJ2B :
      ‖J2 beta B - J2 beta A‖ ≤ r * L :=
    (hJ2 B).trans (mul_le_mul_of_nonneg_left hLB₂ hr0)
  have hJ2C :
      ‖J2 beta C - J2 beta A‖ ≤ r * L :=
    (hJ2 C).trans (mul_le_mul_of_nonneg_left hLC₂ hr0)
  have hErr1 (D : Cfg) :
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
        r ^ 4 * E₁ := by
    calc
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
        ‖F beta D - J1 beta D‖ + ‖F beta A - J1 beta A‖ :=
          norm_sub_le _ _
      _ ≤ ‖beta * M‖ ^ 4 + ‖beta * M‖ ^ 4 :=
        add_le_add
          (p4Q2PP3_originalOneSlabHaarRow_cubicJet_quarticRemainder_le
            H beta hSmallOne D)
          (p4Q2PP3_originalOneSlabHaarRow_cubicJet_quarticRemainder_le
            H beta hSmallOne A)
      _ = r ^ 4 * E₁ := by
        calc
          ‖beta * M‖ ^ 4 + ‖beta * M‖ ^ 4 =
              2 * (‖beta‖ ^ 4 * ‖M‖ ^ 4) := by
            rw [norm_mul]
            ring
          _ = r ^ 4 * E₁ := by dsimp [r, E₁]; ring
  have hErr2 (D : Cfg) :
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
        r ^ 4 * E₂ := by
    calc
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
        ‖G beta D - J2 beta D‖ + ‖G beta A - J2 beta A‖ :=
          norm_sub_le _ _
      _ ≤ ‖beta * (2 * M)‖ ^ 4 + ‖beta * (2 * M)‖ ^ 4 :=
        add_le_add
          (p4Q2PP3_originalTwoSlabHaarRow_cubicJet_quarticRemainder_le
            H beta hSmall D)
          (p4Q2PP3_originalTwoSlabHaarRow_cubicJet_quarticRemainder_le
            H beta hSmall A)
      _ = r ^ 4 * E₂ := by
        calc
          ‖beta * (2 * M)‖ ^ 4 + ‖beta * (2 * M)‖ ^ 4 =
              2 * (‖beta‖ ^ 4 * ‖2 * M‖ ^ 4) := by
            rw [norm_mul]
            ring
          _ = r ^ 4 * E₂ := by dsimp [r, E₂]; ring
  have hJet :
      ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
        (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A) -
        beta ^ 4 * C4 A B C‖ ≤ r ^ 5 * Q :=
    p4Q2PP4_originalCubicJetMinor_fifthOrderBound H beta hBeta A B C
  let x := J1 beta B - J1 beta A
  let y := J1 beta C - J1 beta A
  let u := J2 beta C - J2 beta A
  let v := J2 beta B - J2 beta A
  let ex := (F beta B - J1 beta B) - (F beta A - J1 beta A)
  let ey := (F beta C - J1 beta C) - (F beta A - J1 beta A)
  let eu := (G beta C - J2 beta C) - (G beta A - J2 beta A)
  let ev := (G beta B - J2 beta B) - (G beta A - J2 beta A)
  have hQuant :=
    p4Q2PP4_realMinor_fifthOrder_stability
      r L E₁ E₂ Q hr0 hBeta hE₁ hE₂
      x y u v ex ey eu ev (beta ^ 4 * C4 A B C)
      hJ1B hJ1C hJ2C hJ2B
      (hErr1 B) (hErr1 C) (hErr2 C) (hErr2 B) hJet
  have hLiteral :
      (x + ex) * (u + eu) - (y + ey) * (v + ev) =
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C := by
    dsimp [x, y, u, v, ex, ey, eu, ev,
      p4Q2PJ_originalWilsonLiteralThreeSpatialMinor]
    ring
  rw [hLiteral] at hQuant
  calc
    ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
      beta ^ 4 * C4 A B C‖ ≤
        r ^ 5 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := hQuant
    _ = C₀ * ‖beta‖ ^ 5 := by dsimp [C₀, r]; ring

end OriginalPhysicalFourthCoefficient
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PP5_originalLiteralWilsonMinor_fourthCoefficient
