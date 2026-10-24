import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalMomentTowerV5_PZ16
import Mathlib.Tactic

/-!
# P4-Q2-PZ17 — genuine Haar-selected conditional moments and sixth Ward gate

Connect PZ16's ORIGINAL left-Haar moment tower to previously proved
SU(2) Wilson action moments. Crucially the physical first Taylor
coefficient a(B) is the NEGATIVE of the first action moment M1(B).

The genuine spatial Haar/temporal-crossing Ward results already proved
in PY6 and PY6B reduce M1 to a monic affine polynomial in the actual
spatial Wilson half-action w(A), and M2 to a monic quadratic polynomial
in w(A). M3 and M4 remain the TRUE higher original one-slab action
moments -c(A), u(A), with odd Taylor signs correctly retained; no presumed gauge cancellation is added.

The PZ12 genuine cubic-crossing Haar selection, used in PZ13–PZ16,
continues to remove only right-boundary-invariant sectors. The resulting
selected moment tower is still integrated against the exact physical
outer Haar measure with all intermediate spatial Wilson plaquettes.

Finally expose a concrete signed sixth-Ward balance and prove its exact
zero/nonzero gate, sign criteria and transfer to the ORIGINAL literal
interacting Wilson minor for small positive physical coupling. These
are conditional, verifiable inequalities of genuine moment functionals;
no unproved nonzero witness, mass gap, surrogate, independent posterior,
Dobrushin shortcut, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ17_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ17_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ17_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ17_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ17_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ17_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ17_productProbability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalHaarSelectedMomentWard

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "M" => p4Q2PZ16_originalLeftSlabMoment H
local notation "K" => p4Q2PZ16_originalConditionalFourthTower H
local notation "P4" => p4Q2PZ15_originalFourthPolarization
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u4" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- The physical first Taylor coefficient is NEGATIVE first action
moment, whereas the second, third and fourth Taylor action moments
agree directly with the genuine PZ16 left Haar moments. -/
theorem p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst (A : Cfg) :
    M 1 A = -(a A) := by
  simp only [p4Q2PZ16_originalLeftSlabMoment,
    p4Q2PK_originalOneSlabFirstActionMoment, pow_one, neg_neg]

theorem p4Q2PZ17_originalSecondMoment_eq_actionSecond (A : Cfg) :
    M 2 A = b A := rfl

theorem p4Q2PZ17_originalThirdFourthMoments_eq_actionMoments (A : Cfg) :
    M 3 A = -(c A) ∧ M 4 A = u4 A := by
  constructor
  · simp only [p4Q2PZ16_originalLeftSlabMoment,
      p4Q2PP2_originalOneSlabThirdActionMoment, neg_neg]
  · rfl

/-- True first conditional Haar moment has precisely the right spatial
Wilson boundary difference; all left plaquettes and the original
temporal crossing remain inside its defining integral. -/
theorem p4Q2PZ17_originalFirstMoment_boundaryDifference (A B : Cfg) :
    M 1 B - M 1 A = w B - w A := by
  have hB := p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H B
  have hA := p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H A
  unfold p4Q2PS_originalCenteredFirstMoment at hB hA
  rw [p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst H B,
    p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst H A]
  linarith [hB, hA]

/-- A fixed genuine SU(2) Haar constant, computed at the original
identity spatial configuration (no replacement measure). -/
noncomputable def p4Q2PZ17_originalFirstMomentHaarOffset : ℝ :=
  M 1 (fun _ => 1) - w (fun _ => 1)

local notation "κ" => p4Q2PZ17_originalFirstMomentHaarOffset H

theorem p4Q2PZ17_originalFirstMoment_affine (A : Cfg) :
    M 1 A = w A + κ := by
  unfold p4Q2PZ17_originalFirstMomentHaarOffset
  have h := p4Q2PZ17_originalFirstMoment_boundaryDifference
    H (fun _ => 1) A
  linarith

/-- Reuse the PREVIOUSLY PROVED original SU(2) Haar selection
for the complete squared temporal crossing and the spatial-Wilson
weighted first crossing: the second conditional moment is monic. -/
theorem p4Q2PZ17_originalSecondMoment_quadratic (A : Cfg) :
    M 2 A = (w A)^2 + 2 * α * w A + θ := by
  exact p4Q2PY6_originalSecondActionMoment_quadratic H A

/-- The already proved actual centered-cubic crossing Haar sector
has equal value at ANY two true right boundaries. It is NOT asserted
that the higher-order Ward obstruction itself vanishes. -/
theorem p4Q2PZ17_originalCenteredCubicHaar_boundaryInvariant
    (B C : Cfg) :
    p4Q2PZ13_originalCenteredCubicHaar H B =
      p4Q2PZ13_originalCenteredCubicHaar H C := by
  rw [p4Q2PZ13_originalCenteredCubicHaar_invariant H B,
    p4Q2PZ13_originalCenteredCubicHaar_invariant H C]

/-- PZ16's true conditional Haar tower after the SU(2) selections:
M1 is affine, M2 quadratic, while M3=-c and M4=u4 remain authentic
genuine higher Wilson action Haar moments at the SAME middle slice. -/
noncomputable def p4Q2PZ17_originalHaarSelectedFourthTower
    (A : Cfg) (t u : ℝ) : ℝ :=
  ((((5 * u4 A - 10 * (t+u) * c A) +
      10 * (t^2+t*u+u^2) * ((w A)^2+2*α*w A+θ)) +
      5 * (t^3+t^2*u+t*u^2+u^3) * (w A+κ)) + P4 t u)

local notation "Ksel" => p4Q2PZ17_originalHaarSelectedFourthTower H

theorem p4Q2PZ17_originalConditionalTower_eq_selected
    (A : Cfg) (t u : ℝ) :
    K A t u = Ksel A t u := by
  unfold p4Q2PZ16_originalConditionalFourthTower
    p4Q2PZ17_originalHaarSelectedFourthTower
  rw [(p4Q2PZ17_originalThirdFourthMoments_eq_actionMoments H A).1,
    (p4Q2PZ17_originalThirdFourthMoments_eq_actionMoments H A).2,
    p4Q2PZ17_originalSecondMoment_quadratic H A,
    p4Q2PZ17_originalFirstMoment_affine H A]
  ring

/-- Genuine two-slab response, still integrated against the actual
intermediate SU(2) spatial Haar with its Wilson spatial action. -/
noncomputable def p4Q2PZ17_originalHaarSelectedTwoSlabResponse
    (B C : Cfg) : ℝ :=
  ∫ A : Cfg, (S A B - S A C) *
    Ksel A (S A B) (S A C) ∂haar

local notation "Tsel" => p4Q2PZ17_originalHaarSelectedTwoSlabResponse H

theorem p4Q2PZ17_originalTwoSlabResponse_eq_selected
    (B C : Cfg) :
    p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse H B C =
      Tsel B C := by
  unfold p4Q2PZ16_originalTwoSlabMomentTowerBoundaryResponse
    p4Q2PZ17_originalHaarSelectedTwoSlabResponse
  apply integral_congr_ae
  filter_upwards with A
  rw [p4Q2PZ17_originalConditionalTower_eq_selected
    H A (S A B) (S A C)]

/-- Exact selected genuine outer-Haar alternating determinant. -/
noncomputable def p4Q2PZ17_originalSelectedBoundaryDeterminant
    (A B C : Cfg) : ℝ :=
  (a B-a A) * (Tsel C A-J1 C A) -
    (a C-a A) * (Tsel B A-J1 B A)

local notation "Dsel" => p4Q2PZ17_originalSelectedBoundaryDeterminant H

/-- Sixth Wilson Ward BALANCE with the authentic PZ16 left Haar tower
replaced only by the PROVED SU(2) Haar-selected polynomial identity. -/
noncomputable def p4Q2PZ17_originalSixthWardSelectedBalance
    (A B C : Cfg) : ℝ :=
  120 * C6 A B C - Dsel A B C

local notation "Balance" => p4Q2PZ17_originalSixthWardSelectedBalance H

theorem p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance
    (A B C : Cfg) :
    W6 A B C = 6 * Balance A B C := by
  rw [p4Q2PZ16_originalSixthWard_conditionalMomentTower H A B C]
  rw [p4Q2PZ17_originalTwoSlabResponse_eq_selected H C A,
    p4Q2PZ17_originalTwoSlabResponse_eq_selected H B A]
  unfold p4Q2PZ17_originalSixthWardSelectedBalance
    p4Q2PZ17_originalSelectedBoundaryDeterminant
  ring

/-- Exact six-Ward zero/nonzero decision using only original SU(2)
one/two-slab moments and the Haar-selected conditional tower. -/
theorem p4Q2PZ17_originalSixthWard_zero_iff_selectedBalance
    (A B C : Cfg) :
    W6 A B C = 0 ↔ Balance A B C = 0 := by
  rw [p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance H A B C]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro h
    rw [h, mul_zero]

/-- A *strict verified inequality* between two genuine original
Haar functionals is sufficient for a POSITIVE sixth Ward obstruction.
No inequality or physical witness is presumed. -/
theorem p4Q2PZ17_originalSixthWard_positive_of_selectedStrict
    (A B C : Cfg)
    (h : Dsel A B C < 120 * C6 A B C) :
    0 < W6 A B C := by
  have hbal : 0 < Balance A B C := by
    unfold p4Q2PZ17_originalSixthWardSelectedBalance
    linarith
  rw [p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance]
  positivity

theorem p4Q2PZ17_originalSixthWard_negative_of_selectedStrict
    (A B C : Cfg)
    (h : 120 * C6 A B C < Dsel A B C) :
    W6 A B C < 0 := by
  have hbal : Balance A B C < 0 := by
    unfold p4Q2PZ17_originalSixthWardSelectedBalance
    linarith
  rw [p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance]
  nlinarith

/-- Physical small-positive-coupling transfer: if the ORIGINAL
selected Haar Ward balance is eventually shown nonzero for an
actual finite-volume spatial triple, PZ8 already gives a real
nonzero interacting Wilson three-configuration minor. -/
theorem p4Q2PZ17_originalLiteralMinor_smallPositive_of_selectedBalance
    (A B C : Cfg) (hBalance : Balance A B C ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ beta : ℝ, 0 < beta → beta < delta →
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  have hWard : W6 A B C ≠ 0 := by
    rw [p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance H A B C]
    exact mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) hBalance
  exact p4Q2PZ8_originalLiteralMinor_smallPositive_nonzero_of_Ward
    H A B C hWard

end OriginalHaarSelectedMomentWard
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalFirstMoment_eq_negTaylorFirst
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSecondMoment_eq_actionSecond
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalThirdFourthMoments_eq_actionMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalFirstMoment_boundaryDifference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalFirstMoment_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSecondMoment_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalCenteredCubicHaar_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalConditionalTower_eq_selected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalTwoSlabResponse_eq_selected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSixthWard_eq_sixSelectedBalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSixthWard_zero_iff_selectedBalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSixthWard_positive_of_selectedStrict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalSixthWard_negative_of_selectedStrict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ17_originalLiteralMinor_smallPositive_of_selectedBalance
