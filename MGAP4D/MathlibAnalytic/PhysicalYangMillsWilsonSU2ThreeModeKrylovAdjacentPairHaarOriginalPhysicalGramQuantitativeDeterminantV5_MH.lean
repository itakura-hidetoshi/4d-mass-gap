import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalGramDeterminantV5_MG
import Mathlib.Tactic

/-!
# P4-Q2-MH — quantitative determinant of the genuine Wilson physical Gram

MG formalized the exact full-original-spatial Gram of the original
p-dependent Gauss-law source family x U + y W_{H,p} U, evaluated with
the true interacting SU(2) Wilson signed posterior expectation gaps.
It proved strict positivity of the Gram determinant at authentic
finite-volume Wilson witness contexts.

MH strengthens MG to EXPLICIT quantitative estimates, derived only
from the already proved MF linear physical response floor. Write

  k = [Q_{H,b}(e,e',z,z') / N_H] / (10 E_b²),

where Q is the exact original compensated local GI minor-square energy,
N_H is the true original spatial plaquette count and E_b is the
existing original positive Wilson Harnack-contrast envelope.

At every fixed H with N_H>0, original b>0, and genuine Q>0, the
original physical two-source response Gram (A B; B C) satisfies

  A >= k,  C >= k,
  A*C - B² >= k*A >= k² > 0.

The quantitative determinant inequality is purely a consequence of
the GENUINE original Wilson physical response frame lower bound.
The elementary real proof evaluates that lower bound at the
specific real source coefficients (B,-A), then uses A>=k>0.
It introduces NO independent Haar law, new rank/source/posterior,
Dobrushin assumption, physical hypothesis or new axiom.

The LY authentic original interacting-Wilson witness contexts make
all these bounds simultaneously available at finite H. The
coefficient k is still H-dependent: MH neither establishes a
positive volume-uniform lower bound on Q/N nor a single global
endpoint-source coercivity theorem, H1-C3, the continuum 4D Yang-Mills
construction, or its positive mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Elementary quantitative real two-dimensional frame determinant
bound. The key test vector is (u,-a), and cancellation is exact. -/
private theorem p4Q2MH_realGram_det_ge_floor_times_first
    (a u c k : ℝ) (hk : 0 < k)
    (hFrame : ∀ x y : ℝ,
      k * (x^2 + y^2) ≤ a*x^2 + 2*u*x*y + c*y^2) :
    k*a ≤ a*c - u^2 := by
  have ha : k ≤ a := by
    have h := hFrame 1 0
    nlinarith
  have haPos : 0 < a := lt_of_lt_of_le hk ha
  have hBound : k * (u^2 + a^2) ≤ a * (a*c - u^2) := by
    calc
      k * (u^2 + a^2) = k * (u^2 + (-a)^2) := by ring
      _ ≤ a*u^2 + 2*u*u*(-a) + c*(-a)^2 := hFrame u (-a)
      _ = a * (a*c-u^2) := by ring
  have hSquares : a^2 ≤ u^2 + a^2 := by
    nlinarith [sq_nonneg u]
  have hMult : a*(k*a) ≤ a*(a*c-u^2) := by
    calc
      a*(k*a) = k*a^2 := by ring
      _ ≤ k*(u^2+a^2) :=
        mul_le_mul_of_nonneg_left hSquares hk.le
      _ ≤ a*(a*c-u^2) := hBound
  exact (mul_le_mul_iff_of_pos_left haPos).mp hMult

end GroundStatePosteriorJoint

local instance p4Q2MH_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MH_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MH_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MH_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MH_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "A" => p4Q2MG_originalPhysicalGramUU H b hb
local notation "B" => p4Q2MG_originalPhysicalGramUW H b hb
local notation "C" => p4Q2MG_originalPhysicalGramWW H b hb

/-- Both exact true Wilson physical spatial Gram diagonal entries
dominate the original MF linear density floor, with NO Q>0 premise. -/
theorem p4Q2MH_originalPhysicalGram_diagonals_ge_linearGI
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg) :
    (Q e e' z z' / n) / (10 * E^2) ≤ A e e' z z' ∧
    (Q e e' z z' / n) / (10 * E^2) ≤ C e e' z z' := by
  constructor
  · have h := p4Q2MG_originalPhysicalGram_ge_linearGIFloor
      H b hb hpos hcount e e' z z' 1 0
    nlinarith
  · have h := p4Q2MG_originalPhysicalGram_ge_linearGIFloor
      H b hb hpos hcount e e' z z' 0 1
    nlinarith

/-- Explicit lower bound for the GENUINE physical Wilson spatial
two-source Gram determinant: k*A <= AC-B². It is stronger than k²
when A>=k, and all quantities come from the original posterior. -/
theorem p4Q2MH_originalPhysicalGram_det_ge_floor_times_UU
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    ((Q e e' z z' / n) / (10 * E^2)) *
      A e e' z z' ≤
      A e e' z z' * C e e' z z' -
        (B e e' z z')^2 := by
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hK : 0 < (Q e e' z z' / n) / (10 * E^2) :=
    div_pos (div_pos hQ hcount)
      (mul_pos (by norm_num) (sq_pos_of_pos hE))
  exact p4Q2MH_realGram_det_ge_floor_times_first
    (A e e' z z') (B e e' z z') (C e e' z z')
    ((Q e e' z z' / n) / (10 * E^2)) hK
    (fun x y =>
      p4Q2MG_originalPhysicalGram_ge_linearGIFloor
        H b hb hpos hcount e e' z z' x y)

/-- Quantitative positive determinant of the ACTUAL original Wilson
two-source physical Gram, bounded below by the SQUARE of MF's
genuine linear GI energy-density coefficient. -/
theorem p4Q2MH_originalPhysicalGram_det_ge_linearGIFloor_sq
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hQ : 0 < Q e e' z z') :
    ((Q e e' z z' / n) / (10 * E^2))^2 ≤
      A e e' z z' * C e e' z z' -
        (B e e' z z')^2 := by
  let k : ℝ := (Q e e' z z' / n) / (10 * E^2)
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hk : 0 < k := by
    dsimp [k]
    exact div_pos (div_pos hQ hcount)
      (mul_pos (by norm_num) (sq_pos_of_pos hE))
  have hA : k ≤ A e e' z z' :=
    (p4Q2MH_originalPhysicalGram_diagonals_ge_linearGI
      H b hb hpos hcount e e' z z').1
  have hKA : k * A e e' z z' ≤
      A e e' z z' * C e e' z z' - (B e e' z z')^2 :=
    p4Q2MH_originalPhysicalGram_det_ge_floor_times_UU
      H b hb hpos hcount e e' z z' hQ
  change k^2 ≤
    A e e' z z' * C e e' z z' - (B e e' z z')^2
  calc
    k^2 = k*k := by ring
    _ ≤ k*A e e' z z' := mul_le_mul_of_nonneg_left hA hk.le
    _ ≤ A e e' z z' * C e e' z z' - (B e e' z z')^2 := hKA

/-- At the authentic LY original interacting-Wilson finite-H witness
contexts, the full spatial physical Gram determinant enjoys a
concrete strictly positive lower bound k², not merely positivity. -/
theorem p4Q2MH_originalPhysicalGI_exists_quantitativeGramDetFloor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      0 < n ∧
      0 < Q e e' z z' / n ∧
      ((Q e e' z z' / n) / (10 * E^2))^2 ≤
        A e e' z z' * C e e' z z' -
          (B e e' z z')^2 := by
  obtain ⟨z, z', _, _, hn, hQ, _, _, _, _, _⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  exact ⟨z, z', hn, div_pos hQ hn,
    p4Q2MH_originalPhysicalGram_det_ge_linearGIFloor_sq
      H b hb hpos hn e e' z z' hQ⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MH_originalPhysicalGram_diagonals_ge_linearGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MH_originalPhysicalGram_det_ge_floor_times_UU
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MH_originalPhysicalGram_det_ge_linearGIFloor_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MH_originalPhysicalGI_exists_quantitativeGramDetFloor
