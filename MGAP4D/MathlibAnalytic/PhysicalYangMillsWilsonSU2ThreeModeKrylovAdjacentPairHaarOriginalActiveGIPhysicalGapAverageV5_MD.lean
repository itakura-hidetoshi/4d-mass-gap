import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalActiveGIPhysicalCoerciveDensityV5_MC
import Mathlib.Tactic

/-!
# P4-Q2-MD — active genuine Wilson plaquettes control average physical gap squares

MB extracts the actual energy-active subset from the original SU(2)
Wilson spatial plaquette carrier, and MC proves the ORIGINAL unscaled
Gauss-law physical two-source coercivity at EVERY element of that set.

This module sums those already established physical inequalities at
the very same true interacting-Wilson boundary contexts. For b>0
and positive finite-H original GI square energy Q, let
  n = true number of original spatial plaquettes,
  E = original positive Harnack contrast scale,
  M = (4 E²)²,
  A = {p original | Q/(2n) <= genuine compensated minor(p)²}.
Then, for any real physical coefficients x,y, the ACTUAL ORIGINAL
two-posterior expectation-gap squares obey

  [ Q/n / (2M) ] * [ (Q/(2n))/(10 E²) ] * (x²+y²)
    <= (1/n) sum_(p in A) original_gap_square(p,x,y).

The proof uses the pointwise true physical source inequality and a
literal Finset.sum over MB's original plaquette filter. In particular,
no independent-Haar posterior, substitute source, synthetic detector,
rank postulate, or auxiliary probability law is introduced.

At LY's authentic interacting-Wilson witness contexts this provides
a strictly positive coefficient whenever x²+y²>0, still at finite H.
No H-uniform positive lower bound for Q/n, H1-C3 closure, continuum
Yang-Mills, or positive mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MD_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MD_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MD_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MD_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MD_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb
local notation "active" => p4Q2MB_originalActiveGISpatialPlaquettes H b hb

/-- This is *exactly* the sum of squares of the TWO original signed
interacting-Wilson physical posterior expectation gaps evaluated at
the true Gauss-law source associated with the genuine plaquette p.
It is not an artificial detector or a new posterior. -/
noncomputable def p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) (x y : ℝ) : ℝ :=
  (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
  (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
    H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2

local notation "R" =>
  p4Q2MD_originalPlaquettePhysicalTwoSourceGapSquare H b hb

/-- The spatial AVERAGE over genuinely active original Wilson
plaquettes of their real original physical Gauss-law gap squares
dominates the product of MB's density floor and MC's local physical
coercivity floor. The averaging denominator is the actual total
original plaquette count (not the random active count). -/
theorem p4Q2MD_originalActivePhysicalGapAverage_ge_energyDensitySquare
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') (x y : ℝ) :
    ((Q e e' z z' / n) / (2 * (4 * E^2)^2)) *
      ((Q e e' z z' / (2 * n)) / (10 * E^2)) *
        (x^2 + y^2) ≤
      (∑ p ∈ active e e' z z', R e e' z z' p x y) / n := by
  classical
  let A : Finset Plaq := active e e' z z'
  let c : ℝ := (Q e e' z z' / (2 * n)) / (10 * E^2)
  let δ : ℝ := (Q e e' z z' / n) / (2 * (4 * E^2)^2)
  let S : ℝ := x^2 + y^2
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hN : 0 < 2 * n := mul_pos (by norm_num) hcount
  have hC : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (div_pos hQ hN) hC
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hDensity :=
    p4Q2MB_originalActiveGI_density_ge_energy_fraction
      H b hb hpos hcount e e' z z'
  change δ ≤ (A.card : ℝ) / n at hDensity
  have hPointwise : ∀ p ∈ A, c * S ≤ R e e' z z' p x y := by
    intro p hp
    obtain ⟨_, hFloor, hPhysical⟩ :=
      p4Q2MC_originalEveryActiveGI_hasPhysicalCoercivity
        H b hb hpos hcount e e' z z' hQ p hp
    calc
      c * S ≤ kappa e e' z z' p * S :=
        mul_le_mul_of_nonneg_right hFloor hS
      _ ≤ R e e' z z' p x y := hPhysical x y
  have hSum :
      (A.card : ℝ) * (c * S) ≤
        (∑ p ∈ A, R e e' z z' p x y) := by
    have hEach :
        (∑ p ∈ A, c * S) ≤
          (∑ p ∈ A, R e e' z z' p x y) :=
      Finset.sum_le_sum (fun p hp => hPointwise p hp)
    have hConst :
        (∑ p ∈ A, c * S) = (A.card : ℝ) * (c * S) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hConst] at hEach
    exact hEach
  have hScale :
      δ * (c * S) ≤ ((A.card : ℝ) / n) * (c * S) :=
    mul_le_mul_of_nonneg_right hDensity
      (mul_nonneg hc.le hS)
  have hDiv :
      ((A.card : ℝ) / n) * (c * S) ≤
        (∑ p ∈ A, R e e' z z' p x y) / n := by
    calc
      ((A.card : ℝ) / n) * (c * S) =
          ((A.card : ℝ) * (c * S)) / n := by ring
      _ ≤ (∑ p ∈ A, R e e' z z' p x y) / n :=
        (div_le_div_iff_of_pos_right hcount).2 hSum
  change δ * c * S ≤
    (∑ p ∈ A, R e e' z z' p x y) / n
  calc
    δ * c * S = δ * (c * S) := by ring
    _ ≤ ((A.card : ℝ) / n) * (c * S) := hScale
    _ ≤ (∑ p ∈ A, R e e' z z' p x y) / n := hDiv

/-- The real LY original interacting-Wilson witness contexts satisfy
the finite-volume averaged ORIGINAL Gauss-law physical gap-square
lower bound for any real physical-source coefficients. No uniform
lower bound over H is inserted or inferred. -/
theorem p4Q2MD_originalPhysicalGI_exists_activePhysicalGapAverage
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg)
    (x y : ℝ) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      ((Q e e' z z' / n) / (2 * (4 * E^2)^2)) *
        ((Q e e' z z' / (2 * n)) / (10 * E^2)) *
          (x^2 + y^2) ≤
        (∑ p ∈ active e e' z z', R e e' z z' p x y) / n := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hBound :=
    p4Q2MD_originalActivePhysicalGapAverage_ge_energyDensitySquare
      H b hb hpos hn e e' z z' hQ x y
  exact ⟨z, z', hn, div_pos hQ hn, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MD_originalActivePhysicalGapAverage_ge_energyDensitySquare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MD_originalPhysicalGI_exists_activePhysicalGapAverage
