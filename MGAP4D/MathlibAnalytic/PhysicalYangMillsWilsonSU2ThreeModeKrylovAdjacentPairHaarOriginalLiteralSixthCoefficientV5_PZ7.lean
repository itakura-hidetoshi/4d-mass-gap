import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSeventhMinorStabilityV5_PZ6
import Mathlib.Tactic

/-!
# P4-Q2-PZ7 — genuine literal original Wilson sixth coefficient

The original interacting SU(2) one/two-slab Wilson Haar rows have
sixth-order errors relative to the true fifth-moment Taylor jets
(PZ2–PZ4). PZ5 gives the genuine sixth jet coefficient with a
seventh-order remainder, and PZ6 supplies matching minor stability.

This proves an ACTUAL O(beta^7) estimate for the literal Wilson
minor after its corrected sixth-action-moment coefficient. The
original physical action, middle spatial plaquettes, and both Haar
integrations remain unchanged; the result is not a mass gap
or any unproved coefficient nonzero/rank assumption.
No new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ7_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ7_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ7_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ7_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ7_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- A real quartic Taylor difference starting with degree one is uniformly
O(beta), with all four coefficient norms retained. -/
private theorem p4Q2PZ7_realQuarticJet_difference_firstOrder
    (beta a b c d : ℝ) (hsmall : ‖beta‖ ≤ 1) :
    ‖beta * a + beta ^ 2 / 2 * b +
        beta ^ 3 / 6 * c + beta ^ 4 / 24 * d‖ ≤
      ‖beta‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let r : ℝ := ‖beta‖
  have hr0 : 0 ≤ r := norm_nonneg beta
  have hr2 : r ^ 2 ≤ r := by
    calc
      r ^ 2 = r * r := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hsmall hr0
      _ = r := by ring
  have hr3 : r ^ 3 ≤ r := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_left hr2 hr0
      _ = r ^ 2 := by ring
      _ ≤ r := hr2
  have hr4 : r ^ 4 ≤ r := by
    calc
      r ^ 4 = r * r ^ 3 := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_left hr3 hr0
      _ = r ^ 2 := by ring
      _ ≤ r := hr2
  have h2 : ‖beta ^ 2 / 2‖ ≤ r := by
    calc
      ‖beta ^ 2 / 2‖ = r ^ 2 / 2 := by simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr2, hr0]
  have h3 : ‖beta ^ 3 / 6‖ ≤ r := by
    calc
      ‖beta ^ 3 / 6‖ = r ^ 3 / 6 := by simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr3, hr0]
  have h4 : ‖beta ^ 4 / 24‖ ≤ r := by
    calc
      ‖beta ^ 4 / 24‖ = r ^ 4 / 24 := by simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr4, hr0]
  have hTri :
      ‖beta * a + beta ^ 2 / 2 * b +
        beta ^ 3 / 6 * c + beta ^ 4 / 24 * d‖ ≤
      ‖beta * a‖ + ‖beta ^ 2 / 2 * b‖ +
        ‖beta ^ 3 / 6 * c‖ + ‖beta ^ 4 / 24 * d‖ := by
    have h1 := norm_add_le
      (beta * a + beta ^ 2 / 2 * b + beta ^ 3 / 6 * c)
      (beta ^ 4 / 24 * d)
    have h2' := norm_add_le
      (beta * a + beta ^ 2 / 2 * b)
      (beta ^ 3 / 6 * c)
    have h3' := norm_add_le (beta * a) (beta ^ 2 / 2 * b)
    linarith
  calc
    ‖beta * a + beta ^ 2 / 2 * b +
      beta ^ 3 / 6 * c + beta ^ 4 / 24 * d‖ ≤
        ‖beta * a‖ + ‖beta ^ 2 / 2 * b‖ +
          ‖beta ^ 3 / 6 * c‖ + ‖beta ^ 4 / 24 * d‖ := hTri
    _ = r * ‖a‖ + ‖beta ^ 2 / 2‖ * ‖b‖ +
          ‖beta ^ 3 / 6‖ * ‖c‖ +
            ‖beta ^ 4 / 24‖ * ‖d‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
    _ ≤ r * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
      have hb := mul_le_mul_of_nonneg_right h2 (norm_nonneg b)
      have hc := mul_le_mul_of_nonneg_right h3 (norm_nonneg c)
      have hd := mul_le_mul_of_nonneg_right h4 (norm_nonneg d)
      nlinarith

/-- The original degree-five Wilson moment rows remain first-order
in beta, with the real negative fifth exponential sign retained. -/
private theorem p4Q2PZ7_realQuinticJet_difference_firstOrder
    (beta a b c d e : ℝ) (hsmall : ‖beta‖ ≤ 1) :
    ‖beta * a + beta ^ 2 / 2 * b +
      beta ^ 3 / 6 * c + beta ^ 4 / 24 * d -
      beta ^ 5 / 120 * e‖ ≤
    ‖beta‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖) := by
  let r : ℝ := ‖beta‖
  have hr0 : 0 ≤ r := norm_nonneg beta
  have hr4 : r ^ 4 ≤ 1 := by
    simpa using (pow_le_pow_left₀ hr0 hsmall 4)
  have hr5 : r ^ 5 ≤ r := by
    calc
      r ^ 5 = r * r ^ 4 := by ring
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hr4 hr0
      _ = r := by ring
  have h5 : ‖beta ^ 5 / 120‖ ≤ r := by
    calc
      ‖beta ^ 5 / 120‖ = r ^ 5 / 120 := by
        simp [r, norm_div, norm_pow]
      _ ≤ r := by nlinarith [hr5, hr0]
  have h4 :=
    p4Q2PZ7_realQuarticJet_difference_firstOrder beta a b c d hsmall
  have he :
      ‖beta ^ 5 / 120 * e‖ ≤ r * ‖e‖ := by
    calc
      ‖beta ^ 5 / 120 * e‖ =
          ‖beta ^ 5 / 120‖ * ‖e‖ := norm_mul _ _
      _ ≤ r * ‖e‖ :=
        mul_le_mul_of_nonneg_right h5 (norm_nonneg e)
  calc
    ‖beta * a + beta ^ 2 / 2 * b +
      beta ^ 3 / 6 * c + beta ^ 4 / 24 * d -
      beta ^ 5 / 120 * e‖ ≤
      ‖beta * a + beta ^ 2 / 2 * b +
        beta ^ 3 / 6 * c + beta ^ 4 / 24 * d‖ +
        ‖beta ^ 5 / 120 * e‖ := norm_sub_le _ _
    _ ≤ r * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) + r * ‖e‖ := by
      exact add_le_add h4 he
    _ = ‖beta‖ * (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖) := by
      dsimp [r]
      ring

section OriginalLiteralSixthCoefficient
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "F" => p4Q2IV_originalWilsonUnitHaarKernelSection H
local notation "G" => p4Q2PJ_originalWilsonLiteralTwoSlabKernel H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "J1" => p4Q2PZ1_originalOneSlabFormalTaylor5 H
local notation "J2" => p4Q2PZ1_originalTwoSlabFormalTaylor5 H
local notation "D6" => p4Q2PZ1_originalSixthFifthJetCoefficient H
local notation "D7" => p4Q2PZ1_originalSeventhFifthJetCoefficient H
local notation "D8" => p4Q2PZ1_originalEighthFifthJetCoefficient H
local notation "D9" => p4Q2PZ1_originalNinthFifthJetCoefficient H
local notation "D10" => p4Q2PZ1_originalTenthFifthJetCoefficient H
local notation "m" => p4Q2PZ1_originalOneSlabFifthActionMoment H
local notation "n" => p4Q2PZ1_originalTwoSlabFifthActionMoment H

private theorem p4Q2PZ7_jetOne_difference
    (beta : ℝ) (A D : Cfg) :
    J1 beta D - J1 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A) +
          beta ^ 3 / 6 * (c D - c A) +
            beta ^ 4 / 24 * (u D - u A) -
              beta ^ 5 / 120 * (m D - m A) := by
  unfold p4Q2PZ1_originalOneSlabFormalTaylor5
    p4Q2PX_originalOneSlabFormalTaylor4
    p4Q2PP2_originalOneSlabFormalTaylor3
    p4Q2PK_originalOneSlabFormalTaylor2
  ring

private theorem p4Q2PZ7_jetTwo_difference
    (beta : ℝ) (A D : Cfg) :
    J2 beta D - J2 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) +
          beta ^ 3 / 6 * (g D - g A) +
            beta ^ 4 / 24 * (v D - v A) -
              beta ^ 5 / 120 * (n D - n A) := by
  unfold p4Q2PZ1_originalTwoSlabFormalTaylor5
    p4Q2PX_originalTwoSlabFormalTaylor4
    p4Q2PP2_originalTwoSlabFormalTaylor3
    p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

theorem p4Q2PZ7_originalLiteralWilsonMinor_sixthCoefficient
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
            beta ^ 6 * D6 A B C‖ ≤ K * ‖beta‖ ^ 7 := by
  let L₁ : Cfg → ℝ := fun D =>
    ‖a D - a A‖ + ‖b D - b A‖ +
      ‖c D - c A‖ + ‖u D - u A‖ + ‖m D - m A‖
  let L₂ : Cfg → ℝ := fun D =>
    ‖a D - a A‖ +
      ‖(b D - b A) + 2 * (d D - d A)‖ +
        ‖g D - g A‖ + ‖v D - v A‖ + ‖n D - n A‖
  let L : ℝ := 1 + L₁ B + L₁ C + L₂ B + L₂ C
  let E₁ : ℝ := 2 * ‖M‖ ^ 6
  let E₂ : ℝ := 2 * ‖2 * M‖ ^ 6
  let Q : ℝ := ‖D7 A B C‖ + ‖D8 A B C‖ + ‖D9 A B C‖ + ‖D10 A B C‖
  let K : ℝ := Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂
  have hL₁ (D : Cfg) : 0 ≤ L₁ D := by dsimp [L₁]; positivity
  have hL₂ (D : Cfg) : 0 ≤ L₂ D := by dsimp [L₂]; positivity
  have hL : 0 ≤ L := by
    dsimp only [L]
    have hB₁ := hL₁ B
    have hC₁ := hL₁ C
    have hB₂ := hL₂ B
    have hC₂ := hL₂ C
    linarith
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro beta hBeta hSmall
  let r : ℝ := ‖beta‖
  have hr0 : 0 ≤ r := norm_nonneg beta
  have hSmallOne : ‖beta * M‖ ≤ 1 := by
    have heq : ‖beta * (2 * M)‖ = 2 * ‖beta * M‖ := by
      rw [show beta * (2 * M) = 2 * (beta * M) by ring, norm_mul]
      norm_num
    rw [heq] at hSmall
    linarith
  have hBoundOne (D : Cfg) :
      ‖J1 beta D - J1 beta A‖ ≤ r * L₁ D := by
    rw [p4Q2PZ7_jetOne_difference H beta A D]
    exact p4Q2PZ7_realQuinticJet_difference_firstOrder
      beta (a D - a A) (b D - b A)
        (c D - c A) (u D - u A) (m D - m A) hBeta
  have hBoundTwo (D : Cfg) :
      ‖J2 beta D - J2 beta A‖ ≤ r * L₂ D := by
    rw [p4Q2PZ7_jetTwo_difference H beta A D]
    exact p4Q2PZ7_realQuinticJet_difference_firstOrder
      beta (a D - a A)
        ((b D - b A) + 2 * (d D - d A))
        (g D - g A) (v D - v A) (n D - n A) hBeta
  have hLB₁ : L₁ B ≤ L := by
    dsimp only [L]
    have hc := hL₁ C
    have hb := hL₂ B
    have hd := hL₂ C
    linarith
  have hLC₁ : L₁ C ≤ L := by
    dsimp only [L]
    have hc := hL₁ B
    have hb := hL₂ B
    have hd := hL₂ C
    linarith
  have hLB₂ : L₂ B ≤ L := by
    dsimp only [L]
    have hc := hL₁ B
    have hb := hL₁ C
    have hd := hL₂ C
    linarith
  have hLC₂ : L₂ C ≤ L := by
    dsimp only [L]
    have hc := hL₁ B
    have hb := hL₁ C
    have hd := hL₂ B
    linarith
  have hJ1B :
      ‖J1 beta B - J1 beta A‖ ≤ r * L :=
    (hBoundOne B).trans (mul_le_mul_of_nonneg_left hLB₁ hr0)
  have hJ1C :
      ‖J1 beta C - J1 beta A‖ ≤ r * L :=
    (hBoundOne C).trans (mul_le_mul_of_nonneg_left hLC₁ hr0)
  have hJ2B :
      ‖J2 beta B - J2 beta A‖ ≤ r * L :=
    (hBoundTwo B).trans (mul_le_mul_of_nonneg_left hLB₂ hr0)
  have hJ2C :
      ‖J2 beta C - J2 beta A‖ ≤ r * L :=
    (hBoundTwo C).trans (mul_le_mul_of_nonneg_left hLC₂ hr0)
  have hErr1 (D : Cfg) :
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
        r ^ 6 * E₁ := by
    calc
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
          ‖F beta D - J1 beta D‖ + ‖F beta A - J1 beta A‖ :=
            norm_sub_le _ _
      _ ≤ ‖beta * M‖ ^ 6 + ‖beta * M‖ ^ 6 :=
        add_le_add
          (p4Q2PZ4_originalOneSlabHaarRow_quinticJet_sixthRemainder_le
            H beta hSmallOne D)
          (p4Q2PZ4_originalOneSlabHaarRow_quinticJet_sixthRemainder_le
            H beta hSmallOne A)
      _ = r ^ 6 * E₁ := by
        calc
          ‖beta * M‖ ^ 6 + ‖beta * M‖ ^ 6 =
              2 * (‖beta‖ ^ 7 * ‖M‖ ^ 6) := by
            rw [norm_mul]
            ring
          _ = r ^ 6 * E₁ := by dsimp [r, E₁]; ring
  have hErr2 (D : Cfg) :
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
        r ^ 6 * E₂ := by
    calc
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
          ‖G beta D - J2 beta D‖ + ‖G beta A - J2 beta A‖ :=
            norm_sub_le _ _
      _ ≤ ‖beta * (2 * M)‖ ^ 6 + ‖beta * (2 * M)‖ ^ 6 :=
        add_le_add
          (p4Q2PZ4_originalTwoSlabHaarRow_quinticJet_sixthRemainder_le
            H beta hSmall D)
          (p4Q2PZ4_originalTwoSlabHaarRow_quinticJet_sixthRemainder_le
            H beta hSmall A)
      _ = r ^ 6 * E₂ := by
        calc
          ‖beta * (2 * M)‖ ^ 6 + ‖beta * (2 * M)‖ ^ 6 =
              2 * (‖beta‖ ^ 7 * ‖2 * M‖ ^ 6) := by
            rw [norm_mul]
            ring
          _ = r ^ 6 * E₂ := by dsimp [r, E₂]; ring
  have hJet :
      ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
        (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A) -
        beta ^ 6 * D6 A B C‖ ≤ r ^ 7 * Q :=
    p4Q2PZ5_originalFifthMomentJetMinor_seventhRemainder H beta hBeta A B C
  let x := J1 beta B - J1 beta A
  let y := J1 beta C - J1 beta A
  let u₀ := J2 beta C - J2 beta A
  let v₀ := J2 beta B - J2 beta A
  let ex := (F beta B - J1 beta B) - (F beta A - J1 beta A)
  let ey := (F beta C - J1 beta C) - (F beta A - J1 beta A)
  let eu := (G beta C - J2 beta C) - (G beta A - J2 beta A)
  let ev := (G beta B - J2 beta B) - (G beta A - J2 beta A)
  have hQuant :=
    p4Q2PZ6_realMinor_seventhOrder_stability
      r L E₁ E₂ Q hr0 hBeta hE₁ hE₂
      x y u₀ v₀ ex ey eu ev (beta ^ 6 * D6 A B C)
      hJ1B hJ1C hJ2C hJ2B
      (hErr1 B) (hErr1 C) (hErr2 C) (hErr2 B) hJet
  have hLiteral :
      (x + ex) * (u₀ + eu) - (y + ey) * (v₀ + ev) =
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C := by
    dsimp [x, y, u₀, v₀, ex, ey, eu, ev,
      p4Q2PJ_originalWilsonLiteralThreeSpatialMinor]
    ring
  rw [hLiteral] at hQuant
  calc
    ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
      beta ^ 6 * D6 A B C‖ ≤
        r ^ 7 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := hQuant
    _ = K * ‖beta‖ ^ 7 := by dsimp [K, r]; ring

end OriginalLiteralSixthCoefficient
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ7_originalLiteralWilsonMinor_sixthCoefficient
