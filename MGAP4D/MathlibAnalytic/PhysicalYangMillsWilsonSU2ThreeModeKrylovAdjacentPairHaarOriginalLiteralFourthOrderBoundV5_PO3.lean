import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalIntegratedTwoSlabV5_PO2
import Mathlib.Tactic

/-!
# P4-Q2-PO3 — fourth-order bound for the LITERAL original Wilson minor

PO and PO2 identify both original one- and two-slab Haar-integrated
degree-two Taylor jets, each with a uniform cubic error. PM proves
that the cubic determinant coefficient of those genuine moment jets
vanishes for ALL original SU(2) configurations, by the spatial-Wilson
Haar Ward identity. A quantitative determinant perturbation argument
therefore bounds the exact original literal three-point minor by
C(H,A,B,C) * |beta|^4, for sufficiently small two-sided coupling.

The coefficient C is finite and independent of beta, for each fixed
finite volume and original physical configuration triple. This does
NOT assert a nonzero quartic coefficient, a nonzero triple witness,
D3>0, rank-three independence or a continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PO3_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PO3_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PO3_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PO3_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PO3_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Quantitative stability of a 2×2 determinant: if its unperturbed
minor is fourth-order, both columns are first-order and their errors
third-order, then the exact perturbed determinant is fourth-order.
The final order-six error product is controlled by 0 ≤ r ≤ 1. -/
theorem p4Q2PO3_realMinor_fourthOrder_stability
    (r L E₁ E₂ Q : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (x y u v ex ey eu ev : ℝ)
    (hx : ‖x‖ ≤ r * L) (hy : ‖y‖ ≤ r * L)
    (hu : ‖u‖ ≤ r * L) (hv : ‖v‖ ≤ r * L)
    (hex : ‖ex‖ ≤ r ^ 3 * E₁)
    (hey : ‖ey‖ ≤ r ^ 3 * E₁)
    (heu : ‖eu‖ ≤ r ^ 3 * E₂)
    (hev : ‖ev‖ ≤ r ^ 3 * E₂)
    (hDet : ‖x * u - y * v‖ ≤ r ^ 4 * Q) :
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev)‖ ≤
      r ^ 4 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
  have hr2 : r ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hr0)]
  have hr6 : r ^ 6 ≤ r ^ 4 := by
    calc
      r ^ 6 = r ^ 4 * r ^ 2 := by ring
      _ ≤ r ^ 4 * 1 := mul_le_mul_of_nonneg_left hr2 (pow_nonneg hr0 4)
      _ = r ^ 4 := by ring
  have h31 (e z : ℝ)
      (he : ‖e‖ ≤ r ^ 3 * E₁) (hz : ‖z‖ ≤ r * L) :
      ‖e * z‖ ≤ r ^ 4 * E₁ * L := by
    calc
      ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
      _ ≤ (r ^ 3 * E₁) * (r * L) :=
        mul_le_mul he hz (norm_nonneg _) (by positivity)
      _ = r ^ 4 * E₁ * L := by ring
  have h13 (z e : ℝ)
      (hz : ‖z‖ ≤ r * L) (he : ‖e‖ ≤ r ^ 3 * E₂) :
      ‖z * e‖ ≤ r ^ 4 * E₂ * L := by
    calc
      ‖z * e‖ = ‖e * z‖ := by rw [mul_comm]
      _ ≤ r ^ 4 * E₂ * L := by
        calc
          ‖e * z‖ = ‖e‖ * ‖z‖ := norm_mul _ _
          _ ≤ (r ^ 3 * E₂) * (r * L) :=
            mul_le_mul he hz (norm_nonneg _) (by positivity)
          _ = r ^ 4 * E₂ * L := by ring
  have h33 (e f : ℝ)
      (he : ‖e‖ ≤ r ^ 3 * E₁) (hf : ‖f‖ ≤ r ^ 3 * E₂) :
      ‖e * f‖ ≤ r ^ 4 * E₁ * E₂ := by
    calc
      ‖e * f‖ = ‖e‖ * ‖f‖ := norm_mul _ _
      _ ≤ (r ^ 3 * E₁) * (r ^ 3 * E₂) :=
        mul_le_mul he hf (norm_nonneg _) (by positivity)
      _ = r ^ 6 * (E₁ * E₂) := by ring
      _ ≤ r ^ 4 * (E₁ * E₂) :=
        mul_le_mul_of_nonneg_right hr6 (mul_nonneg hE₁ hE₂)
      _ = r ^ 4 * E₁ * E₂ := by ring
  have hTerm₁ := h31 ex u hex hu
  have hTerm₂ := h13 x eu hx heu
  have hTerm₃ := h33 ex eu hex heu
  have hTerm₄ := h31 ey v hey hv
  have hTerm₅ := h13 y ev hy hev
  have hTerm₆ := h33 ey ev hey hev
  have hTri :
      ‖(x + ex) * (u + eu) - (y + ey) * (v + ev)‖ ≤
        ‖x * u - y * v‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := by
    have hEq :
        (x + ex) * (u + eu) - (y + ey) * (v + ev) =
          (x * u - y * v) +
            ((ex * u + x * eu + ex * eu) -
              (ey * v + y * ev + ey * ev)) := by ring
    rw [hEq]
    have h1 := norm_add_le (x * u - y * v)
      ((ex * u + x * eu + ex * eu) - (ey * v + y * ev + ey * ev))
    have h2 := norm_sub_le (ex * u + x * eu + ex * eu)
      (ey * v + y * ev + ey * ev)
    have h3 := norm_add_le (ex * u + x * eu) (ex * eu)
    have h4 := norm_add_le (ex * u) (x * eu)
    have h5 := norm_add_le (ey * v + y * ev) (ey * ev)
    have h6 := norm_add_le (ey * v) (y * ev)
    linarith
  calc
    ‖(x + ex) * (u + eu) - (y + ey) * (v + ev)‖ ≤
        ‖x * u - y * v‖ +
          ‖ex * u‖ + ‖x * eu‖ + ‖ex * eu‖ +
          ‖ey * v‖ + ‖y * ev‖ + ‖ey * ev‖ := hTri
    _ ≤ r ^ 4 * Q +
          2 * (r ^ 4 * E₁ * L) + 2 * (r ^ 4 * E₂ * L) +
          2 * (r ^ 4 * E₁ * E₂) := by
      linarith
    _ = r ^ 4 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := by
      ring

section OriginalLiteralMinorOrderFour
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "M" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "J1" => p4Q2PK_originalOneSlabFormalTaylor2 H
local notation "J2" => p4Q2PK_originalTwoSlabFormalTaylor2 H
local notation "F" => p4Q2IV_originalWilsonUnitHaarKernelSection H
local notation "G" => p4Q2PJ_originalWilsonLiteralTwoSlabKernel H

private theorem p4Q2PO3_jetOne_difference
    (beta : ℝ) (A D : Cfg) :
    J1 beta D - J1 beta A =
      beta * (a D - a A) + beta ^ 2 / 2 * (b D - b A) := by
  unfold p4Q2PK_originalOneSlabFormalTaylor2
  ring

private theorem p4Q2PO3_jetTwo_difference
    (beta : ℝ) (A D : Cfg) :
    J2 beta D - J2 beta A =
      beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A)) := by
  unfold p4Q2PK_originalTwoSlabFormalTaylor2
  dsimp only
  ring

/-- Fixed finite-volume original physical three-boundary literal
Wilson determinant has a genuine coupling-independent fourth-order
bound, directly from PO/PO2 and PM. -/
theorem p4Q2PO3_originalLiteralWilsonMinor_fourthOrder
    (A B C : Cfg) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ beta : ℝ, ‖beta‖ ≤ 1 →
        ‖beta * (2 * M)‖ ≤ 1 →
          ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
            C₀ * ‖beta‖ ^ 4 := by
  let L : ℝ :=
    1 + (‖a B - a A‖ + ‖a C - a A‖) +
      (‖b B - b A‖ + ‖b C - b A‖) +
      2 * (‖d B - d A‖ + ‖d C - d A‖)
  let E₁ : ℝ := 2 * ‖M‖ ^ 3
  let E₂ : ℝ := 2 * ‖2 * M‖ ^ 3
  let R : ℝ :=
    ((b B - b A) * (d C - d A) -
      (b C - b A) * (d B - d A)) / 2
  let Q : ℝ := ‖R‖
  let C₀ : ℝ :=
    Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hE₁ : 0 ≤ E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 ≤ E₂ := by dsimp [E₂]; positivity
  have hQ : 0 ≤ Q := norm_nonneg R
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
  have hHalf : ‖beta ^ 2 / 2‖ ≤ r := by
    have hr2 : r ^ 2 ≤ r := by
      calc
        r ^ 2 = r * r := by ring
        _ ≤ r * 1 := mul_le_mul_of_nonneg_left hBeta hr0
        _ = r := by ring
    calc
      ‖beta ^ 2 / 2‖ = r ^ 2 / 2 := by
        simp [r, norm_div, norm_pow]
      _ ≤ r := by linarith [hr2, hr0]
  have hJ1 (D : Cfg) :
      ‖J1 beta D - J1 beta A‖ ≤
        r * (‖a D - a A‖ + ‖b D - b A‖) := by
    rw [p4Q2PO3_jetOne_difference H beta A D]
    calc
      ‖beta * (a D - a A) +
        beta ^ 2 / 2 * (b D - b A)‖ ≤
          ‖beta * (a D - a A)‖ +
            ‖(beta ^ 2 / 2) * (b D - b A)‖ := norm_add_le _ _
      _ = r * ‖a D - a A‖ +
            ‖beta ^ 2 / 2‖ * ‖b D - b A‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ r * ‖a D - a A‖ +
            r * ‖b D - b A‖ := by
        have h := mul_le_mul_of_nonneg_right hHalf
          (norm_nonneg (b D - b A))
        linarith
      _ = r * (‖a D - a A‖ + ‖b D - b A‖) := by ring
  have hJ2 (D : Cfg) :
      ‖J2 beta D - J2 beta A‖ ≤
        r * (‖a D - a A‖ + ‖b D - b A‖ +
          2 * ‖d D - d A‖) := by
    rw [p4Q2PO3_jetTwo_difference H beta A D]
    have hSum :
        ‖(b D - b A) + 2 * (d D - d A)‖ ≤
          ‖b D - b A‖ + 2 * ‖d D - d A‖ := by
      calc
        _ ≤ ‖b D - b A‖ + ‖2 * (d D - d A)‖ := norm_add_le _ _
        _ = ‖b D - b A‖ + 2 * ‖d D - d A‖ := by
          rw [norm_mul]
          norm_num
    calc
      ‖beta * (a D - a A) +
        beta ^ 2 / 2 * ((b D - b A) + 2 * (d D - d A))‖ ≤
          ‖beta * (a D - a A)‖ +
            ‖(beta ^ 2 / 2) * ((b D - b A) + 2 * (d D - d A))‖ :=
        norm_add_le _ _
      _ = r * ‖a D - a A‖ +
            ‖beta ^ 2 / 2‖ *
              ‖(b D - b A) + 2 * (d D - d A)‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ r * ‖a D - a A‖ +
            r * ‖(b D - b A) + 2 * (d D - d A)‖ := by
        have h := mul_le_mul_of_nonneg_right hHalf
          (norm_nonneg ((b D - b A) + 2 * (d D - d A)))
        linarith
      _ ≤ r * (‖a D - a A‖ + ‖b D - b A‖ +
            2 * ‖d D - d A‖) := by
        nlinarith [mul_le_mul_of_nonneg_left hSum hr0]
  -- Explicit nonnegative additive slack avoids unfolding norm into abs
  -- on only one side of a linarith comparison.
  have hLB₁ : ‖a B - a A‖ + ‖b B - b A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ +
        2 * (‖d B - d A‖ + ‖d C - d A‖) := by positivity
    calc
      ‖a B - a A‖ + ‖b B - b A‖ ≤
          (‖a B - a A‖ + ‖b B - b A‖) +
            ((1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ +
              2 * (‖d B - d A‖ + ‖d C - d A‖)) :=
        le_add_of_nonneg_right hExtra
      _ = L := by
        dsimp only [L]
        ring
  have hLC₁ : ‖a C - a A‖ + ‖b C - b A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ +
        2 * (‖d B - d A‖ + ‖d C - d A‖) := by positivity
    calc
      ‖a C - a A‖ + ‖b C - b A‖ ≤
          (‖a C - a A‖ + ‖b C - b A‖) +
            ((1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ +
              2 * (‖d B - d A‖ + ‖d C - d A‖)) :=
        le_add_of_nonneg_right hExtra
      _ = L := by
        dsimp only [L]
        ring
  have hLB₂ :
      ‖a B - a A‖ + ‖b B - b A‖ + 2 * ‖d B - d A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ +
        2 * ‖d C - d A‖ := by positivity
    calc
      ‖a B - a A‖ + ‖b B - b A‖ + 2 * ‖d B - d A‖ ≤
          (‖a B - a A‖ + ‖b B - b A‖ + 2 * ‖d B - d A‖) +
            ((1 : ℝ) + ‖a C - a A‖ + ‖b C - b A‖ +
              2 * ‖d C - d A‖) :=
        le_add_of_nonneg_right hExtra
      _ = L := by
        dsimp only [L]
        ring
  have hLC₂ :
      ‖a C - a A‖ + ‖b C - b A‖ + 2 * ‖d C - d A‖ ≤ L := by
    have hExtra : 0 ≤ (1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ +
        2 * ‖d B - d A‖ := by positivity
    calc
      ‖a C - a A‖ + ‖b C - b A‖ + 2 * ‖d C - d A‖ ≤
          (‖a C - a A‖ + ‖b C - b A‖ + 2 * ‖d C - d A‖) +
            ((1 : ℝ) + ‖a B - a A‖ + ‖b B - b A‖ +
              2 * ‖d B - d A‖) :=
        le_add_of_nonneg_right hExtra
      _ = L := by
        dsimp only [L]
        ring
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
        r ^ 3 * E₁ := by
    calc
      ‖(F beta D - J1 beta D) - (F beta A - J1 beta A)‖ ≤
          ‖F beta D - J1 beta D‖ +
            ‖F beta A - J1 beta A‖ := norm_sub_le _ _
      _ ≤ ‖beta * M‖ ^ 3 + ‖beta * M‖ ^ 3 :=
        add_le_add
          (p4Q2PO_originalOneSlabHaarRow_eqFormal_cubicRemainder
            H beta hSmallOne D)
          (p4Q2PO_originalOneSlabHaarRow_eqFormal_cubicRemainder
            H beta hSmallOne A)
      _ = r ^ 3 * E₁ := by
        calc
          ‖beta * M‖ ^ 3 + ‖beta * M‖ ^ 3 =
              2 * (‖beta‖ ^ 3 * ‖M‖ ^ 3) := by
            rw [norm_mul]
            ring
          _ = r ^ 3 * E₁ := by dsimp [r, E₁]; ring
  have hErr2 (D : Cfg) :
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
        r ^ 3 * E₂ := by
    calc
      ‖(G beta D - J2 beta D) - (G beta A - J2 beta A)‖ ≤
          ‖G beta D - J2 beta D‖ +
            ‖G beta A - J2 beta A‖ := norm_sub_le _ _
      _ ≤ ‖beta * (2 * M)‖ ^ 3 + ‖beta * (2 * M)‖ ^ 3 :=
        add_le_add
          (p4Q2PO2_originalTwoSlabHaarRow_eqFormal_cubicRemainder
            H beta hSmall D)
          (p4Q2PO2_originalTwoSlabHaarRow_eqFormal_cubicRemainder
            H beta hSmall A)
      _ = r ^ 3 * E₂ := by
        calc
          ‖beta * (2 * M)‖ ^ 3 + ‖beta * (2 * M)‖ ^ 3 =
              2 * (‖beta‖ ^ 3 * ‖2 * M‖ ^ 3) := by
            rw [norm_mul]
            ring
          _ = r ^ 3 * E₂ := by dsimp [r, E₂]; ring
  have hJetDet :
      ‖(J1 beta B - J1 beta A) * (J2 beta C - J2 beta A) -
        (J1 beta C - J1 beta A) * (J2 beta B - J2 beta A)‖ ≤
          r ^ 4 * Q := by
    rw [p4Q2PM_originalWilsonFormalTaylorMinor_quarticOnly H beta A B C]
    have hFac :
        beta ^ 4 / 2 *
          ((b B - b A) * (d C - d A) -
            (b C - b A) * (d B - d A)) = beta ^ 4 * R := by
      dsimp [R]
      ring
    rw [hFac, norm_mul, norm_pow]
  let x := J1 beta B - J1 beta A
  let y := J1 beta C - J1 beta A
  let u := J2 beta C - J2 beta A
  let v := J2 beta B - J2 beta A
  let ex := (F beta B - J1 beta B) - (F beta A - J1 beta A)
  let ey := (F beta C - J1 beta C) - (F beta A - J1 beta A)
  let eu := (G beta C - J2 beta C) - (G beta A - J2 beta A)
  let ev := (G beta B - J2 beta B) - (G beta A - J2 beta A)
  have hQuant :=
    p4Q2PO3_realMinor_fourthOrder_stability
      r L E₁ E₂ Q hr0 hBeta hE₁ hE₂
      x y u v ex ey eu ev
      hJ1B hJ1C hJ2C hJ2B
      (hErr1 B) (hErr1 C) (hErr2 C) (hErr2 B) hJetDet
  have hLiteral :
      (x + ex) * (u + eu) - (y + ey) * (v + ev) =
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C := by
    dsimp [x, y, u, v, ex, ey, eu, ev,
      p4Q2PJ_originalWilsonLiteralThreeSpatialMinor]
    ring
  rw [hLiteral] at hQuant
  calc
    ‖p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C‖ ≤
        r ^ 4 * (Q + 2 * E₁ * L + 2 * E₂ * L + 2 * E₁ * E₂) := hQuant
    _ = C₀ * ‖beta‖ ^ 4 := by dsimp [C₀, r]; ring

end OriginalLiteralMinorOrderFour
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO3_realMinor_fourthOrder_stability
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PO3_originalLiteralWilsonMinor_fourthOrder
