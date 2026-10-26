import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthJetEighthTailV5_PZ37M
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMinimalOverlapEvaluationV5_PZ37L

/-!
# PZ37M — actual original Wilson seventh coefficient and eighth-order remainder

The literal interacting minor now has the evaluated seventh coefficient with
an analytic O(|beta|^8) remainder. Constants may depend on finite H and the three
boundaries. This is not a volume-uniform U0, rank-three or continuum mass gap.
-/
namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "F" => p4Q2IV_originalWilsonUnitHaarKernelSection H
local notation "G" => p4Q2PJ_originalWilsonLiteralTwoSlabKernel H
local notation "J1" => p4Q2PZ37B_originalOneSlabTaylor6 H
local notation "J2" => p4Q2PZ37B_originalTwoSlabTaylor6 H
local notation "P7" => p4Q2PZ37B_originalPhysicalSeventhCoefficient H
local notation "w" => p4Q2PS_originalHalfSpatialAction H

/-- Actual one/two-slab Wilson minor, on the original finite-action small-coupling domain. -/
theorem p4Q2PZ37M_originalLiteralWilsonMinor_seventhCoefficient
    (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
            beta ^ 7 * P7 A B C‖ ≤ K * ‖beta‖ ^ 8 := by
  let L₁ : Cfg → ℝ := fun D =>
    ∑ i : Fin 6, ‖p4Q2PZ37M_originalOneJetCoefficients H A D i‖
  let L₂ : Cfg → ℝ := fun D =>
    ∑ i : Fin 6, ‖p4Q2PZ37M_originalTwoJetCoefficients H A D i‖
  let L : ℝ := 1 + L₁ B + L₁ C + L₂ B + L₂ C
  let E₁ : ℝ := 2 * ‖M‖ ^ 7
  let E₂ : ℝ := 2 * ‖2 * M‖ ^ 7
  let Q : ℝ := ∑ i : Fin 5, ‖p4Q2PZ37M_originalJetTailCoefficients H A B C i‖
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
  have hBoundOne (D : Cfg) : ‖J1 beta D-J1 beta A‖ ≤ r*L₁ D :=
    p4Q2PZ37M_originalOneJet_difference_firstOrder H beta hBeta A D
  have hBoundTwo (D : Cfg) : ‖J2 beta D-J2 beta A‖ ≤ r*L₂ D :=
    p4Q2PZ37M_originalTwoJet_difference_firstOrder H beta hBeta A D
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
        r ^ 7 * E₁ := by
    calc
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
          ‖F beta D - J1 beta D‖ + ‖F beta A - J1 beta A‖ :=
            norm_sub_le _ _
      _ ≤ ‖beta * M‖ ^ 7 + ‖beta * M‖ ^ 7 :=
        add_le_add
          (p4Q2PZ37M_originalOneSlabHaarRow_sexticJet_seventhRemainder_le
            H beta hSmallOne D)
          (p4Q2PZ37M_originalOneSlabHaarRow_sexticJet_seventhRemainder_le
            H beta hSmallOne A)
      _ = r ^ 7 * E₁ := by
        calc
          ‖beta * M‖ ^ 7 + ‖beta * M‖ ^ 7 =
              2 * (‖beta‖ ^ 7 * ‖M‖ ^ 7) := by
            rw [norm_mul]
            ring
          _ = r ^ 7 * E₁ := by dsimp [r, E₁]; ring
  have hErr2 (D : Cfg) :
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
        r ^ 7 * E₂ := by
    calc
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
          ‖G beta D - J2 beta D‖ + ‖G beta A - J2 beta A‖ :=
            norm_sub_le _ _
      _ ≤ ‖beta * (2 * M)‖ ^ 7 + ‖beta * (2 * M)‖ ^ 7 :=
        add_le_add
          (p4Q2PZ37M_originalTwoSlabHaarRow_sexticJet_seventhRemainder_le
            H beta hSmall D)
          (p4Q2PZ37M_originalTwoSlabHaarRow_sexticJet_seventhRemainder_le
            H beta hSmall A)
      _ = r ^ 7 * E₂ := by
        calc
          ‖beta * (2 * M)‖ ^ 7 + ‖beta * (2 * M)‖ ^ 7 =
              2 * (‖beta‖ ^ 7 * ‖2 * M‖ ^ 7) := by
            rw [norm_mul]
            ring
          _ = r ^ 7 * E₂ := by dsimp [r, E₂]; ring
  have hJet :
      ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
        (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A) -
        beta ^ 7 * P7 A B C‖ ≤ r ^ 8 * Q :=
    p4Q2PZ37M_originalSixthMomentJetMinor_eighthRemainder H beta hBeta A B C
  let x := J1 beta B - J1 beta A
  let y := J1 beta C - J1 beta A
  let u₀ := J2 beta C - J2 beta A
  let v₀ := J2 beta B - J2 beta A
  let ex := (F beta B - J1 beta B) - (F beta A - J1 beta A)
  let ey := (F beta C - J1 beta C) - (F beta A - J1 beta A)
  let eu := (G beta C - J2 beta C) - (G beta A - J2 beta A)
  let ev := (G beta B - J2 beta B) - (G beta A - J2 beta A)
  have hQuant :=
    PZ37MEstimates.minor_eighthOrder_stability
      r L E₁ E₂ Q hr0 hBeta hE₁ hE₂
      x y u₀ v₀ ex ey eu ev (beta ^ 7 * P7 A B C)
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
      beta ^ 7 * P7 A B C‖ ≤
        r ^ 8 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := hQuant
    _ = K * ‖beta‖ ^ 8 := by dsimp [K, r]; ring

/-- For every nonminimal period the evaluated Vandermonde is the actual seventh coefficient. -/
theorem p4Q2PZ37M_originalLiteralWilsonMinor_nonminimal_vandermonde
    (hH : 1 ≤ H) (A B C : Cfg) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ beta : ℝ, ‖beta‖ ≤ 1 → ‖beta*(2*M)‖ ≤ 1 →
      ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C -
        beta^7 * (-(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512)‖ ≤
          K*‖beta‖^8 := by
  simpa only [p4Q2PZ37K_originalPhysicalSeventhJet_nonminimal_vandermonde H hH A B C]
    using p4Q2PZ37M_originalLiteralWilsonMinor_seventhCoefficient H A B C

/-- Period two retains its exact boundary-loop correction in the actual minor. -/
theorem p4Q2PZ37M_originalLiteralWilsonMinor_minimal_loopCorrection
    (A B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 0 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ beta : ℝ, ‖beta‖ ≤ 1 →
      ‖beta*(2*periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget 0)‖ ≤ 1 →
      ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor 0 beta A B C - beta^7 *
        (-(PZ37VandermondeAlgebra.vandermonde
          (p4Q2PS_originalHalfSpatialAction 0 A)
          (p4Q2PS_originalHalfSpatialAction 0 B)
          (p4Q2PS_originalHalfSpatialAction 0 C))/512 -
          (3/8192 : ℝ)*p4Q2PZ37B_originalBoundaryWedge 0
            (p4Q2PS_originalHalfSpatialAction 0)
            p4Q2PZ37L_originalMinimalBoundaryLoopSum A B C)‖ ≤ K*‖beta‖^8 := by
  simpa only [p4Q2PZ37L_originalMinimalPhysicalSeventhJet_exact A B C]
    using p4Q2PZ37M_originalLiteralWilsonMinor_seventhCoefficient 0 A B C
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalLiteralWilsonMinor_seventhCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalLiteralWilsonMinor_nonminimal_vandermonde
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalLiteralWilsonMinor_minimal_loopCorrection
