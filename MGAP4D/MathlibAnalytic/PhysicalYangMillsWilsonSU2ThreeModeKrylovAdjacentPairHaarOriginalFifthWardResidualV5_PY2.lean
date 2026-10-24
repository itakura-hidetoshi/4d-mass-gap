import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthWardSlopeV5_PY
import Mathlib.Tactic

/-!
# P4-Q2-PY2 — genuine fifth Wilson coefficient as a single Ward minor

PY proves the authentic quartic-Ward profile R3 = g-c-3*m*b
has a COMPLETELY EXPLICIT slope s = 3∫b dHaar - 6 J(identity)
along the original first-moment profile a.

Insert that proved identity and PM's exact mixed-action Ward
d(B)-d(A)=m*(a(B)-a(A)) into PX's corrected genuine fifth jet:
  C5(A,B,C) = det(Δa, ΔR5)/24,
  R5(B)=v(B)-u(B)-2*s*b(B)-4*m*c(B).
u and v are ORIGINAL SU(2) fourth action moments, with the
full interacting two-slab middle Wilson spatial plaquettes intact.

The genuinely physical fifth-order coefficient is nonzero for
some triple IF AND ONLY IF the new true R5 profile is NOT globally
affine in a. Neither alternative is postulated. The literal analytic
interpretation and O(beta^6) remainder are already PX4.

No new axiom, sorry/admit, posterior replacement, surrogate
spectral measure, Dobrushin, or unconditional third Hankel assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY2_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY2_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY2_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY2_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY2_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTrueFifthWardResidual
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "v" => p4Q2PX_originalTwoSlabFourthActionMoment H
local notation "m" => p4Q2PQ_originalFirstActionMean H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "C5" => p4Q2PX_originalFifthFourthJetCoefficient H

/-- The ACTUAL fifth-order Ward residual in the unchanged
full SU(2) spatial Wilson Haar model. In particular, v includes
the complete intermediate spatial-slice plaquette interaction. -/
noncomputable def p4Q2PY_originalFifthWardResidual (B : Cfg) : ℝ :=
  v B - u B - 2 * s * b B - 4 * m * c B

local notation "R5" => p4Q2PY_originalFifthWardResidual H

/-- The genuine fourth-moment fifth Wilson coefficient is EXACTLY
a two-by-two minor of the true first moment and the new Ward-normalized
FOURTH-MOMENT profile, divided by 24. There is no nonzero assumption. -/
theorem p4Q2PY_originalFifthCoefficient_eq_residualMinor
    (A B C : Cfg) :
    C5 A B C =
      ((a B - a A) * (R5 C - R5 A) -
        (a C - a A) * (R5 B - R5 A)) / 24 := by
  have hD (D : Cfg) :
      d D - d A = m * (a D - a A) := by
    exact p4Q2PM_originalMixedMoment_difference_proportional H A D
  have hG (D : Cfg) :
      g D - g A =
        (c D - c A) + 3 * m * (b D - b A) +
          s * (a D - a A) := by
    have hR :=
      p4Q2PY_originalQuarticWardResidual_difference_explicit H A D
    unfold p4Q2PQ_originalQuarticWardResidual at hR
    linear_combination hR
  unfold p4Q2PX_originalFifthFourthJetCoefficient
    p4Q2PP2_originalFifthJetCoefficient
    p4Q2PY_originalFifthWardResidual
  rw [hD B, hD C, hG B, hG C]
  ring

/-- Denominator-free version suited to exact geometric rank tests. -/
theorem p4Q2PY_originalFifthCoefficient_twentyfour_mul
    (A B C : Cfg) :
    24 * C5 A B C =
      (a B - a A) * (R5 C - R5 A) -
        (a C - a A) * (R5 B - R5 A) := by
  rw [p4Q2PY_originalFifthCoefficient_eq_residualMinor H A B C]
  ring

/-- If the true fourth-moment Ward residual is affine in the actual
first Wilson action profile, every original fifth coefficient vanishes. -/
theorem p4Q2PY_originalFifthCoefficient_zero_of_residual_affine
    (s₅ t₅ : ℝ)
    (hAffine : ∀ X : Cfg, R5 X = s₅ * a X + t₅)
    (A B C : Cfg) :
    C5 A B C = 0 := by
  rw [p4Q2PY_originalFifthCoefficient_eq_residualMinor H A B C]
  rw [hAffine A, hAffine B, hAffine C]
  ring

/-- For the ORIGINAL SU(2) model, global vanishing of the genuine
analytic fifth coefficient is EQUIVALENT to the true R5 profile
being affine in the first Wilson action profile. This uses the
PROVED nonconstant one-slab Wilson first variation, not a rank axiom. -/
theorem p4Q2PY_allFifthCoefficients_zero_iff_residual_affine :
    (∀ A B C : Cfg, C5 A B C = 0) ↔
      ∃ s₅ t₅ : ℝ, ∀ X : Cfg, R5 X = s₅ * a X + t₅ := by
  constructor
  · intro hZero
    obtain ⟨A, B, hAB⟩ := p4Q2PQ_originalFirstMoment_nonconstant H
    have hDenom : a B - a A ≠ 0 := sub_ne_zero.mpr hAB.symm
    let s₅ : ℝ := (R5 B - R5 A) / (a B - a A)
    let t₅ : ℝ := R5 A - s₅ * a A
    refine ⟨s₅, t₅, ?_⟩
    intro X
    have hDet :
        (a B - a A) * (R5 X - R5 A) -
          (a X - a A) * (R5 B - R5 A) = 0 := by
      calc
        _ = 24 * C5 A B X :=
          (p4Q2PY_originalFifthCoefficient_twentyfour_mul H A B X).symm
        _ = 0 := by rw [hZero A B X]; ring
    have hSlope : (a B - a A) * s₅ = R5 B - R5 A := by
      dsimp [s₅]
      field_simp [hDenom]
    have hFactor :
        (a B - a A) * (R5 X - R5 A - s₅ * (a X - a A)) = 0 := by
      calc
        _ = (a B - a A) * (R5 X - R5 A) -
              (a X - a A) * ((a B - a A) * s₅) := by ring
        _ = (a B - a A) * (R5 X - R5 A) -
              (a X - a A) * (R5 B - R5 A) := by rw [hSlope]
        _ = 0 := hDet
    have hLinear : R5 X - R5 A - s₅ * (a X - a A) = 0 :=
      (mul_eq_zero.mp hFactor).resolve_left hDenom
    dsimp only [t₅]
    linear_combination hLinear
  · rintro ⟨s₅, t₅, hAffine⟩ A B C
    exact p4Q2PY_originalFifthCoefficient_zero_of_residual_affine
      H s₅ t₅ hAffine A B C

/-- Physical nonzero fifth coefficient at some genuine spatial
boundary triple is EXACTLY the failure of Ward-normalized
fourth moment residual to be globally affine in a. -/
theorem p4Q2PY_exists_nonzeroFifthCoefficient_iff_not_affine :
    (∃ A B C : Cfg, C5 A B C ≠ 0) ↔
      ¬ ∃ s₅ t₅ : ℝ, ∀ X : Cfg, R5 X = s₅ * a X + t₅ := by
  rw [← p4Q2PY_allFifthCoefficients_zero_iff_residual_affine H]
  push Not
  rfl

end OriginalTrueFifthWardResidual
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalFifthCoefficient_eq_residualMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalFifthCoefficient_twentyfour_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalFifthCoefficient_zero_of_residual_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_allFifthCoefficients_zero_iff_residual_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_exists_nonzeroFifthCoefficient_iff_not_affine
