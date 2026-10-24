import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLiteralFifthCoefficientV5_PX4F
import Mathlib.Tactic

/-!
# P4-Q2-PY — true SU(2) fourth Ward slope is explicit

PX4 proves that the complete original literal Wilson three-boundary minor
has the fourth-moment fifth coefficient modulo an O(beta^6) error.
For the NEXT Ward obstruction, first compute the exact affine slope of
the genuine cubic-action Ward residual. PS reduces that residual to a
gauge-variant right spatial half-action plus the stripped Haar profile.
PT3 says the stripped profile's boundary difference is precisely the
two-crossing centered Haar integral. PW3 PROVES this double-crossing
Haar profile vanishes in the original full spatial SU(2) Wilson model.

Consequently the original cubic Ward residual is explicitly affine
in the original first action moment, not just existentially so.
No new axiom, posterior replacement, Dobrushin path, sorry/admit,
nonzero fifth-order coefficient or third-Hankel claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ExplicitTrueFourthWardSlope
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "F" => p4Q2PS_originalStrippedWardProfile H
local notation "R" => p4Q2PQ_originalQuarticWardResidual H
local notation "J₀" =>
  p4Q2PS_originalCenteredMixedHaar H (fun _ => 1)

/-- The EXACT original Ward slope, with no unspecified existence witness:
s_H = 3∫b dHaar - 6 J(identity). J is the genuine centered Wilson
one-slab crossing Haar integral, whose boundary invariance is proved. -/
noncomputable def p4Q2PY_originalQuarticWardSlope : ℝ :=
  3 * (∫ X : Cfg, b X ∂haar) - 6 * J₀

local notation "s" => p4Q2PY_originalQuarticWardSlope H

/-- The whole non-affine stripped SU(2) Wilson crossing profile has
NO boundary variation after PW3's true two-crossing Ward cancellation.
Not even a rank condition is used. -/
theorem p4Q2PY_originalStrippedWardProfile_constant
    (A B : Cfg) : F B = F A := by
  have hDiff : F B - F A = 0 := by
    rw [p4Q2PT3_originalStrippedWard_difference_eq_twoCrossing H A B,
      p4Q2PW3_originalTwoCrossingCenteredHaar_zero H B,
      p4Q2PW3_originalTwoCrossingCenteredHaar_zero H A]
    ring
  exact sub_eq_zero.mp hDiff

/-- Explicit (not merely existential) original fourth-Ward residual
slope. Original middle spatial Wilson plaquettes and full Haar remain
inside all constituent physical action-moment profiles. -/
theorem p4Q2PY_originalQuarticWardResidual_difference_explicit
    (A B : Cfg) :
    R B - R A = s * (a B - a A) := by
  have hConst := p4Q2PY_originalStrippedWardProfile_constant H A B
  rw [p4Q2PS_originalQuarticWardResidual_rightStrip H B,
    p4Q2PS_originalQuarticWardResidual_rightStrip H A,
    p4Q2PM_originalFirstMoment_spatialWilson H B,
    p4Q2PM_originalFirstMoment_spatialWilson H A,
    hConst]
  unfold p4Q2PY_originalQuarticWardSlope
    p4Q2PS_originalHalfSpatialAction
  ring

/-- The TRUE cubic-action Ward residual is globally affine with the
explicit SU(2)-Haar-determined slope, at every fixed finite H. -/
theorem p4Q2PY_originalQuarticWardResidual_affine_explicit :
    ∃ t : ℝ, ∀ B : Cfg, R B = s * a B + t := by
  let A₀ : Cfg := fun _ => 1
  let t : ℝ := R A₀ - s * a A₀
  refine ⟨t, ?_⟩
  intro B
  have hDiff :=
    p4Q2PY_originalQuarticWardResidual_difference_explicit H A₀ B
  dsimp only [t]
  linear_combination hDiff

end ExplicitTrueFourthWardSlope
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalStrippedWardProfile_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalQuarticWardResidual_difference_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY_originalQuarticWardResidual_affine_explicit
