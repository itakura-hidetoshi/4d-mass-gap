import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTemporalWilsonSpanDualObstructionV5_NJ
import Mathlib.Tactic

/-!
# P4-Q2-NK — exact rank-two genuine SU(2) Wilson temporal kernel certificate

NJ reduced the genuine signed physical receiver obstruction to the
REAL linear span of the ACTUAL fixed-positive-beta SU(2) Wilson
temporal kernel sections. The full span density is a separate, as yet
unproved, harmonic-analysis claim, not an axiom.

NK starts a constructive finite-section analysis on the TRUE original
SU(2) group, not on a synthetic two-state substitute. Use the original
physical identity and genuine SU(2) pi-rotation only as two TEST POINTS
of the unchanged continuous full-group kernel, at arbitrary b>0.
The exact table is
    [ exp(b)   exp(-b) ]
    [ exp(-b)  exp(b)  ].
Its determinant is strictly positive for every b>0, proving genuine
two-point nonsingularity, rank >=2 and distinct true group sections.
This is not a claim that a pair of SU(2) points replaces Haar,
posterior laws, the physical Gauss-law source or Perron half-density.

No unproved nonzero receiver determinant is inserted: the two-point
temporal kernel determinant here is NOT NH's signed posterior moment
determinant. Extending the finite test to ALL modes, then linear-span
density, remains open. No Dobrushin, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The existing, genuinely physical SU(2) pi-rotation, not a
discrete model or new random variable. -/
private noncomputable def p4Q2NK_R : Gauge :=
  specialUnitaryTwoRotation Real.pi

/-- At genuine SU(2) identity source and identity target,
the ORIGINAL normalized fundamental Wilson temporal character is 1. -/
theorem p4Q2NK_originalTemporalCharacter_one_one :
    p4Q2NG_originalSU2TemporalCharacter (1 : Gauge) 1 = 1 := by
  unfold p4Q2NG_originalSU2TemporalCharacter
  simp only [inv_one, one_mul]
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  ring

/-- At identity source and the TRUE physical pi-rotation target,
the ORIGINAL normalized Wilson temporal character is -1. -/
theorem p4Q2NK_originalTemporalCharacter_one_rotation :
    p4Q2NG_originalSU2TemporalCharacter (1 : Gauge)
      (specialUnitaryTwoRotation Real.pi) = -1 := by
  unfold p4Q2NG_originalSU2TemporalCharacter
  simp only [inv_one, one_mul]
  rw [originalWilsonExplicitPiRotation_energy_eq_two]
  ring

/-- Reversing original SU(2) source and target preserves the exact
negative character at the pi-rotation. -/
theorem p4Q2NK_originalTemporalCharacter_rotation_one :
    p4Q2NG_originalSU2TemporalCharacter
      (specialUnitaryTwoRotation Real.pi) (1 : Gauge) = -1 := by
  unfold p4Q2NG_originalSU2TemporalCharacter
  simp only [mul_one]
  rw [specialUnitaryWilsonPlaquetteEnergy_inv]
  rw [originalWilsonExplicitPiRotation_energy_eq_two]
  ring

/-- Both source and target at the same ORIGINAL physical pi-rotation
give the identity temporal holonomy and normalized character +1. -/
theorem p4Q2NK_originalTemporalCharacter_rotation_rotation :
    p4Q2NG_originalSU2TemporalCharacter
      (specialUnitaryTwoRotation Real.pi)
      (specialUnitaryTwoRotation Real.pi) = 1 := by
  unfold p4Q2NG_originalSU2TemporalCharacter
  rw [inv_mul_cancel]
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)]
  ring

/-- Exact first diagonal kernel entry for the REAL original
SU(2) Wilson temporal exponential section. -/
theorem p4Q2NK_originalWilsonSection_one_one (b : ℝ) :
    p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge) 1 =
      Real.exp b := by
  change Real.exp
    (b * p4Q2NG_originalSU2TemporalCharacter (1 : Gauge) 1) = _
  rw [p4Q2NK_originalTemporalCharacter_one_one]
  ring

/-- Exact genuine off-diagonal source/target Wilson kernel entry. -/
theorem p4Q2NK_originalWilsonSection_one_rotation (b : ℝ) :
    p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge)
      (specialUnitaryTwoRotation Real.pi) = Real.exp (-b) := by
  change Real.exp
    (b * p4Q2NG_originalSU2TemporalCharacter
      (1 : Gauge) (specialUnitaryTwoRotation Real.pi)) = _
  rw [p4Q2NK_originalTemporalCharacter_one_rotation]
  ring

/-- Exact reversed genuine off-diagonal Wilson kernel entry. -/
theorem p4Q2NK_originalWilsonSection_rotation_one (b : ℝ) :
    p4Q2NJ_originalSU2WilsonTemporalSection b
      (specialUnitaryTwoRotation Real.pi) (1 : Gauge) = Real.exp (-b) := by
  change Real.exp
    (b * p4Q2NG_originalSU2TemporalCharacter
      (specialUnitaryTwoRotation Real.pi) (1 : Gauge)) = _
  rw [p4Q2NK_originalTemporalCharacter_rotation_one]
  ring

/-- Exact second diagonal original Wilson temporal kernel entry. -/
theorem p4Q2NK_originalWilsonSection_rotation_rotation (b : ℝ) :
    p4Q2NJ_originalSU2WilsonTemporalSection b
      (specialUnitaryTwoRotation Real.pi)
      (specialUnitaryTwoRotation Real.pi) = Real.exp b := by
  change Real.exp
    (b * p4Q2NG_originalSU2TemporalCharacter
      (specialUnitaryTwoRotation Real.pi)
      (specialUnitaryTwoRotation Real.pi)) = _
  rw [p4Q2NK_originalTemporalCharacter_rotation_rotation]
  ring

/-- The 2-by-2 evaluation matrix of the UNCHANGED continuous SU(2)
temporal Wilson kernel at the two genuine physical group elements.
It is a finite test of the full group, not a replacement posterior. -/
noncomputable def p4Q2NK_originalTemporalTwoPointMatrix (b : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    p4Q2NJ_originalSU2WilsonTemporalSection b
      (if i = 0 then (1 : Gauge) else specialUnitaryTwoRotation Real.pi)
      (if j = 0 then (1 : Gauge) else specialUnitaryTwoRotation Real.pi)

/-- The exact determinant of the genuine SU(2) Wilson temporal
two-point evaluation matrix. -/
theorem p4Q2NK_originalTemporalTwoPointMatrix_det (b : ℝ) :
    (p4Q2NK_originalTemporalTwoPointMatrix b).det =
      Real.exp b ^ 2 - Real.exp (-b) ^ 2 := by
  rw [Matrix.det_fin_two]
  change
    p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge) 1 *
      p4Q2NJ_originalSU2WilsonTemporalSection b
        (specialUnitaryTwoRotation Real.pi)
        (specialUnitaryTwoRotation Real.pi) -
      p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge)
        (specialUnitaryTwoRotation Real.pi) *
      p4Q2NJ_originalSU2WilsonTemporalSection b
        (specialUnitaryTwoRotation Real.pi) (1 : Gauge) = _
  rw [p4Q2NK_originalWilsonSection_one_one,
    p4Q2NK_originalWilsonSection_rotation_rotation,
    p4Q2NK_originalWilsonSection_one_rotation,
    p4Q2NK_originalWilsonSection_rotation_one]
  ring

/-- All strictly positive couplings have a TRUE original SU(2)
Wilson temporal rank-two certificate. No synthetic rank axiom. -/
theorem p4Q2NK_originalTemporalTwoPointMatrix_det_pos
    (b : ℝ) (hb : 0 < b) :
    0 < (p4Q2NK_originalTemporalTwoPointMatrix b).det := by
  rw [p4Q2NK_originalTemporalTwoPointMatrix_det]
  have hLt : Real.exp (-b) < Real.exp b :=
    Real.exp_lt_exp.mpr (by linarith)
  have hDiff : 0 < Real.exp b - Real.exp (-b) :=
    sub_pos.mpr hLt
  have hSum : 0 < Real.exp b + Real.exp (-b) :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  nlinarith [mul_pos hDiff hSum]

/-- Even at arbitrarily small positive beta, the two actual Wilson
kernel sections at 1 and the physical pi-rotation are DISTINCT on
the original infinite SU(2) group. -/
theorem p4Q2NK_originalWilsonSection_identity_ne_rotation
    (b : ℝ) (hb : 0 < b) :
    p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge) ≠
      p4Q2NJ_originalSU2WilsonTemporalSection b
        (specialUnitaryTwoRotation Real.pi) := by
  intro hEq
  have hAt :
      p4Q2NJ_originalSU2WilsonTemporalSection b (1 : Gauge) 1 =
        p4Q2NJ_originalSU2WilsonTemporalSection b
          (specialUnitaryTwoRotation Real.pi) 1 := by
    rw [hEq]
  rw [p4Q2NK_originalWilsonSection_one_one,
    p4Q2NK_originalWilsonSection_rotation_one] at hAt
  have hLt : Real.exp (-b) < Real.exp b :=
    Real.exp_lt_exp.mpr (by linarith)
  exact (ne_of_gt hLt) hAt

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalCharacter_one_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalCharacter_one_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalCharacter_rotation_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalCharacter_rotation_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalWilsonSection_one_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalWilsonSection_one_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalWilsonSection_rotation_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalWilsonSection_rotation_rotation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalTwoPointMatrix_det
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalTemporalTwoPointMatrix_det_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NK_originalWilsonSection_identity_ne_rotation
