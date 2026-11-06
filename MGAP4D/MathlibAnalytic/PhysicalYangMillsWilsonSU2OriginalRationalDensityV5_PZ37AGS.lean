import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalStereographicCentersV5_PZ37AGR
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGS — genuine rational stereographic chart geometry

This leaf establishes continuity and exact inverse coordinates of the
stereographic rational SU(2) center family from AGR, using the SAME
original four real coordinates, unit S³ and original SU(2) matrices.

The excluded stereographic pole is explicit; finite rational covers
and all-center density will follow separately after these exact facts.
No new geometry proxy, Haar model, transfer, or physical sign is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1

def p4Q2PZ37AGS_realSphereCoordinates (u : Fin 3 → ℝ) : Fin 4 → ℝ :=
  let s := (u 0)^2 + (u 1)^2 + (u 2)^2
  ![(1 - s) / (1 + s), 2 * u 0 / (1 + s),
    2 * u 1 / (1 + s), 2 * u 2 / (1 + s)]

def p4Q2PZ37AGS_realStereographicVector (u : Fin 3 → ℝ) : E4 :=
  WithLp.toLp 2 (p4Q2PZ37AGS_realSphereCoordinates u)

/-- Original AGR rational inverse stereographic formula commutes with the
exact casts into the already existing Euclidean S³ coordinates. -/
theorem p4Q2PZ37AGS_rationalVector_exact (t : Fin 3 → ℚ) :
    p4Q2PZ37AGS_realStereographicVector (fun j => (t j : ℝ)) =
      (p4Q2PZ37AGR_rationalSphere t : E4) := by
  change WithLp.toLp 2 (p4Q2PZ37AGS_realSphereCoordinates
      (fun j : Fin 3 => (t j : ℝ))) =
    WithLp.toLp 2 (fun j : Fin 4 =>
      (p4Q2PZ37AGR_rationalSphereCoordinates t j : ℝ))
  congr 1
  funext j
  fin_cases j <;>
    simp [p4Q2PZ37AGS_realSphereCoordinates,
      p4Q2PZ37AGR_rationalSphereCoordinates] <;> push_cast <;> ring

/-- The real stereographic family is continuous in all three parameters.
Its denominator is strictly positive, independently of the chart point. -/
theorem p4Q2PZ37AGS_realStereographicVector_continuous :
    Continuous p4Q2PZ37AGS_realStereographicVector := by
  let s : (Fin 3 → ℝ) → ℝ := fun u => (u 0)^2 + (u 1)^2 + (u 2)^2
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hden : Continuous (fun u : Fin 3 → ℝ => 1 + s u) :=
    continuous_const.add hs
  have hden_ne (u : Fin 3 → ℝ) : 1 + s u ≠ 0 := by
    have h : 0 ≤ s u := by dsimp [s]; positivity
    linarith only [h]
  have hc0 : Continuous (fun u : Fin 3 → ℝ => (1 - s u) / (1 + s u)) :=
    (continuous_const.sub hs).div hden hden_ne
  have hc1 : Continuous (fun u : Fin 3 → ℝ => (2 * u 0) / (1 + s u)) :=
    (continuous_const.mul (continuous_apply (0 : Fin 3))).div hden hden_ne
  have hc2 : Continuous (fun u : Fin 3 → ℝ => (2 * u 1) / (1 + s u)) :=
    (continuous_const.mul (continuous_apply (1 : Fin 3))).div hden hden_ne
  have hc3 : Continuous (fun u : Fin 3 → ℝ => (2 * u 2) / (1 + s u)) :=
    (continuous_const.mul (continuous_apply (2 : Fin 3))).div hden hden_ne
  have hc (j : Fin 4) :
      Continuous (fun u : Fin 3 → ℝ => p4Q2PZ37AGS_realSphereCoordinates u j) := by
    fin_cases j
    · simpa [p4Q2PZ37AGS_realSphereCoordinates, s] using hc0
    · simpa [p4Q2PZ37AGS_realSphereCoordinates, s] using hc1
    · simpa [p4Q2PZ37AGS_realSphereCoordinates, s] using hc2
    · simpa [p4Q2PZ37AGS_realSphereCoordinates, s] using hc3
  change Continuous (fun u : Fin 3 → ℝ =>
    (WithLp.toLp 2 (p4Q2PZ37AGS_realSphereCoordinates u) : E4))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hc)

/-- The exact 4-real-coordinate inverse formula, on the genuine sphere
away from the single excluded stereographic pole (-1,0,0,0). -/
theorem p4Q2PZ37AGS_chartAlgebra (a b c d : ℝ)
    (h : a^2 + b^2 + c^2 + d^2 = 1) (ha : 1 + a ≠ 0) :
    p4Q2PZ37AGS_realStereographicVector
      ![b / (1 + a), c / (1 + a), d / (1 + a)] =
      (WithLp.toLp 2 (![a, b, c, d] : Fin 4 → ℝ) : E4) := by
  let D : ℝ := 1 + a
  let u : Fin 3 → ℝ := ![b / D, c / D, d / D]
  let s : ℝ := (u 0)^2 + (u 1)^2 + (u 2)^2
  have hd : D ≠ 0 := ha
  have hS : s = (1 - a) / D := by
    dsimp [s, u]
    field_simp
    dsimp [D]
    nlinarith only [h]
  have hD : (1 + s) * D = 2 := by
    rw [hS]
    field_simp
    dsimp [D]
    ring
  have hN : (1 - s) * D = 2 * a := by
    rw [hS]
    field_simp
    dsimp [D]
    ring
  have hS_ne : 1 + s ≠ 0 := by
    have hpos : 0 ≤ s := by dsimp [s]; positivity
    linarith only [hpos]
  have h0 : (1 - s) / (1 + s) = a := by
    apply (div_eq_iff hS_ne).2
    have hh : ((1 - s) - a * (1 + s)) * D = 0 := by
      calc
        ((1 - s) - a * (1 + s)) * D =
          (1 - s) * D - a * ((1 + s) * D) := by ring
        _ = 2 * a - a * 2 := by rw [hN, hD]
        _ = 0 := by ring
    have heq := (mul_eq_zero.mp hh).resolve_right hd
    linarith only [heq]
  have hRest (z : ℝ) : 2 * (z / D) / (1 + s) = z := by
    apply (div_eq_iff hS_ne).2
    have hz : (z / D) * D = z := by field_simp
    have hh : (2 * (z / D) - z * (1 + s)) * D = 0 := by
      calc
        (2 * (z / D) - z * (1 + s)) * D =
          2 * ((z / D) * D) - z * ((1 + s) * D) := by ring
        _ = 2 * z - z * 2 := by rw [hz, hD]
        _ = 0 := by ring
    have heq := (mul_eq_zero.mp hh).resolve_right hd
    linarith only [heq]
  change (WithLp.toLp 2 (p4Q2PZ37AGS_realSphereCoordinates u) : E4) =
    WithLp.toLp 2 (![a, b, c, d] : Fin 4 → ℝ)
  congr 1
  funext j
  fin_cases j
  · change (1 - s) / (1 + s) = a
    exact h0
  · change 2 * (b / D) / (1 + s) = b
    exact hRest b
  · change 2 * (c / D) / (1 + s) = c
    exact hRest c
  · change 2 * (d / D) / (1 + s) = d
    exact hRest d

/-- The whole genuine sphere except the excluded pole admits this real
stereographic chart, with original first-column coordinate convention. -/
theorem p4Q2PZ37AGS_chart_surjective_offPole (x : S3)
    (hx0 : (x : E4) 0 ≠ -1) :
    ∃ u : Fin 3 → ℝ,
      p4Q2PZ37AGS_realStereographicVector u = (x : E4) := by
  let a : ℝ := (x : E4) 0
  let b : ℝ := (x : E4) 1
  let c : ℝ := (x : E4) 2
  let d : ℝ := (x : E4) 3
  have hn : ‖(x : E4)‖ = 1 := by
    have hx := x.property
    change dist (x : E4) (0 : E4) = 1 at hx
    simpa only [dist_zero_right] using hx
  have hsq : ‖(x : E4)‖ ^ 2 = 1 := by rw [hn]; norm_num
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  have h : a^2 + b^2 + c^2 + d^2 = 1 := by
    simpa [a, b, c, d, Fin.sum_univ_four] using hsq
  have ha : 1 + a ≠ 0 := by
    intro heq
    apply hx0
    dsimp [a] at heq
    linarith only [heq]
  refine ⟨![b / (1 + a), c / (1 + a), d / (1 + a)], ?_⟩
  calc
    p4Q2PZ37AGS_realStereographicVector
        ![b / (1 + a), c / (1 + a), d / (1 + a)] =
      (WithLp.toLp 2 (![a, b, c, d] : Fin 4 → ℝ) : E4) :=
        p4Q2PZ37AGS_chartAlgebra a b c d h ha
    _ = (x : E4) := by
      ext j
      fin_cases j <;> rfl

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGS_rationalVector_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGS_realStereographicVector_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGS_chartAlgebra
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGS_chart_surjective_offPole
