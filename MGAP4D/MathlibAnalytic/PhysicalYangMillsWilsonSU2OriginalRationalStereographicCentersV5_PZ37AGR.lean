import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMassBudgetGridDataV5_PZ37AGQ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGR — rational stereographic centers in the genuine original SU(2)

The inverse stereographic rational formula gives exact points of the genuine
four-real-coordinate unit three-sphere.  ADS maps those exact sphere points to
the SAME original 2x2 special-unitary matrices, and AGL supplies the
proof-carrying rational-coordinate interface.

This is a constructive algebraic center family; the density and finite-cover
statements need their own topological proof and must not be inferred from the
formula alone. No proxy Haar measure or physical transfer is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S3" => Metric.sphere (0 : E4) 1

/-- Stereographic inverse denominator, positive for every rational
parameter; no square root or normalized floating point approximation. -/
def p4Q2PZ37AGR_rationalDenominator (t : Fin 3 → ℚ) : ℚ :=
  1 + (t 0)^2 + (t 1)^2 + (t 2)^2

theorem p4Q2PZ37AGR_rationalDenominator_pos (t : Fin 3 → ℚ) :
    0 < p4Q2PZ37AGR_rationalDenominator t := by
  unfold p4Q2PZ37AGR_rationalDenominator
  positivity

/-- Rational stereographic inverse into the ACTUAL four real coordinates
of the unit 3-sphere; the north-pole convention matches ADR and ADS. -/
def p4Q2PZ37AGR_rationalSphereCoordinates (t : Fin 3 → ℚ) : Fin 4 → ℚ :=
  let s := (t 0)^2 + (t 1)^2 + (t 2)^2
  ![(1 - s) / (1 + s), 2 * t 0 / (1 + s),
    2 * t 1 / (1 + s), 2 * t 2 / (1 + s)]

/-- The exact Pythagorean rational identity behind stereographic
projection, with its denominator proved nonzero. -/
theorem p4Q2PZ37AGR_rationalSphereCoordinates_sq_sum (t : Fin 3 → ℚ) :
    (∑ j : Fin 4, (p4Q2PZ37AGR_rationalSphereCoordinates t j)^2) = 1 := by
  let s : ℚ := (t 0)^2 + (t 1)^2 + (t 2)^2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hd : (1 + s : ℚ) ≠ 0 := by linarith only [hs]
  simp only [Fin.sum_univ_four]
  change ((1 - s) / (1 + s))^2 +
      (2 * t 0 / (1 + s))^2 +
      (2 * t 1 / (1 + s))^2 +
      (2 * t 2 / (1 + s))^2 = 1
  field_simp
  dsimp [s]
  ring

/-- A genuine point of the existing Mathlib sphere, obtained from only
three rational parameters and the exact rational Pythagorean identity. -/
def p4Q2PZ37AGR_rationalSphere (t : Fin 3 → ℚ) : S3 := by
  let v : E4 := WithLp.toLp 2
    (fun j : Fin 4 => (p4Q2PZ37AGR_rationalSphereCoordinates t j : ℝ))
  have hsq : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := p4Q2PZ37AGR_rationalSphereCoordinates_sq_sum t
    have hReal : (∑ j : Fin 4,
        (p4Q2PZ37AGR_rationalSphereCoordinates t j : ℝ)^2) = 1 := by
      exact_mod_cast h
    simpa [v] using hReal
  have hnorm : ‖v‖ = 1 := by
    nlinarith only [hsq, norm_nonneg v]
  exact ⟨v, by change dist v (0 : E4) = 1
               simpa only [dist_zero_right] using hnorm⟩

/-- The rational stereographic sphere point is mapped into the SAME
original SU(2) gauge group as Wilson transfer, not another quaternion
group or a replacement finite-point model. -/
def p4Q2PZ37AGR_originalRationalCenter (t : Fin 3 → ℚ) : G :=
  p4Q2PZ37ADS_originalSphereToSU2
    (p4Q2PZ37AGR_rationalSphere t)

/-- Recover exact rational witnesses in AGL's ORIGINAL four matrix
coordinates, by ADS's proven two-sided inverse. -/
def p4Q2PZ37AGR_originalRationalCenter_coordinates (t : Fin 3 → ℚ) :
    p4Q2PZ37AGL_rationalCoordinates
      (p4Q2PZ37AGR_originalRationalCenter t) where
  value := p4Q2PZ37AGR_rationalSphereCoordinates t
  hValue := by
    intro j
    have h := congrArg (fun x : S3 => (x : E4) j)
      (p4Q2PZ37ADS_sphere_roundtrip (p4Q2PZ37AGR_rationalSphere t))
    simpa [p4Q2PZ37ADR_originalSU2ToSphere,
      p4Q2PZ37AGR_originalRationalCenter,
      p4Q2PZ37AGR_rationalSphere,
      p4Q2PZ37ADR_originalFourCoordinates] using h

/-- Every one of these authentic rational SU(2) centers has an
exactly rational, zero-width original Wilson plaquette energy. -/
theorem p4Q2PZ37AGR_originalCenter_energy_exact (t : Fin 3 → ℚ) :
    specialUnitaryWilsonPlaquetteEnergy 2
      (p4Q2PZ37AGR_originalRationalCenter t) =
        (1 - p4Q2PZ37AGR_rationalSphereCoordinates t 0 : ℚ) := by
  exact (p4Q2PZ37AGR_originalRationalCenter_coordinates t).energy_exact

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGR_rationalDenominator_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGR_rationalSphereCoordinates_sq_sum
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGR_rationalSphere
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGR_originalRationalCenter_coordinates
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGR_originalCenter_energy_exact
