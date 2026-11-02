import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalQuaternionLinearActionV5_PZ37ADW
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADX — original SU(2) sphere action is ambient-real orthogonal

ADW established the actual SU(2) monoid homomorphism into Mathlib's
unit quaternions and its four-dimensional REAL linear isometry action.
ADT and ADV established the concrete original S³ coordinates and the
transported genuine SU(2) left action.

The original matrix first-column convention differs from the standard
Mathlib quaternion coordinates by a MINUS SIGN in exactly coordinate 3.
This file corrects that sign using the genuine coordinatewise PiLp
linear isometry equivalence, then conjugates the ADW quaternion left
linear isometry through Mathlib's quaternion Euclidean-space isometry.

The resulting map of the ORIGINAL ambient EuclideanSpace ℝ (Fin 4)
agrees ON THE NOSE with ADV's original S³ left action on ALL sphere
points. No alternate physical gauge group, Haar measure or source.

The remaining independent obstruction is the invariance of
(Measure.toSphere volume) under these real-linear isometries.
No unconditional normalized-surface-Haar equality or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "H4" => Quaternion ℝ
local notation "S3" => Metric.sphere (0 : E4) 1
local notation "V" => p4Q2PZ37ADR_originalFourCoordinates
local notation "Φ" => p4Q2PZ37ADR_originalSU2ToSphere
local notation "Ψ" => p4Q2PZ37ADS_originalSphereToSU2
local notation "Q" => p4Q2PZ37ADW_originalQuaternion
local notation "act" => p4Q2PZ37ADU_originalLeftActionOnSphere

/-- A genuine one-coordinate real linear isometry, not a sign
convention imposed by proof simplification. -/
noncomputable def p4Q2PZ37ADX_coordinateReflection (i : Fin 4) :
    ℝ ≃ₗᵢ[ℝ] ℝ :=
  if i = 3 then LinearIsometryEquiv.neg ℝ
  else LinearIsometryEquiv.refl ℝ ℝ

/-- A real-linear orthogonal reflection in the FOURTH coordinate,
implemented using the fixed Mathlib PiLp isometry constructor. -/
noncomputable def p4Q2PZ37ADX_fourthSignFlip : E4 ≃ₗᵢ[ℝ] E4 :=
  LinearIsometryEquiv.piLpCongrRight 2
    p4Q2PZ37ADX_coordinateReflection

theorem p4Q2PZ37ADX_fourthSignFlip_apply (x : E4) (i : Fin 4) :
    p4Q2PZ37ADX_fourthSignFlip x i =
      if i = 3 then -(x i) else x i := by
  by_cases hi : i = 3
  · subst i
    simp [p4Q2PZ37ADX_fourthSignFlip,
      p4Q2PZ37ADX_coordinateReflection]
  · simp [p4Q2PZ37ADX_fourthSignFlip,
      p4Q2PZ37ADX_coordinateReflection, hi]

/-- The actual ADW quaternion coordinates, re-expressed as ADR's
unmodified first-column real-four SU(2) coordinates. -/
noncomputable def p4Q2PZ37ADX_quaternionToOriginalFour : H4 ≃ₗᵢ[ℝ] E4 :=
  Quaternion.linearIsometryEquivTuple.trans p4Q2PZ37ADX_fourthSignFlip

/-- Exact compatibility of BOTH existing original presentations:
the ADS/ADR Euclidean first-column map equals the corrected ADW
unit quaternion coordinates, including the crucial fourth sign. -/
theorem p4Q2PZ37ADX_originalQuaternionCoordinates_eq (g : G) :
    p4Q2PZ37ADX_quaternionToOriginalFour (Q g) = V g := by
  ext i
  fin_cases i <;>
    simp [p4Q2PZ37ADX_quaternionToOriginalFour,
      p4Q2PZ37ADX_fourthSignFlip_apply,
      p4Q2PZ37ADW_originalQuaternion,
      p4Q2PZ37ADR_originalFourCoordinates]

/-- The actual original SU(2) left action has a GENUINE
real-four-dimensional LINEAR ISOMETRY EQUIVALENCE extension. -/
noncomputable def p4Q2PZ37ADX_originalAmbientLinearIsometry (g : G) :
    E4 ≃ₗᵢ[ℝ] E4 :=
  (p4Q2PZ37ADX_quaternionToOriginalFour.symm.trans
    (p4Q2PZ37ADW_originalQuaternionLeftLinearIsometryEquiv g)).trans
      p4Q2PZ37ADX_quaternionToOriginalFour

/-- The actual orthogonal map sends the ORIGINAL coordinate vector
of h to the ORIGINAL coordinate vector of g*h. -/
theorem p4Q2PZ37ADX_ambient_mul_coordinates (g h : G) :
    p4Q2PZ37ADX_originalAmbientLinearIsometry g (V h) = V (g * h) := by
  have hBack :
      p4Q2PZ37ADX_quaternionToOriginalFour.symm (V h) = Q h := by
    rw [← p4Q2PZ37ADX_originalQuaternionCoordinates_eq h,
      LinearIsometryEquiv.symm_apply_apply]
  calc
    p4Q2PZ37ADX_originalAmbientLinearIsometry g (V h) =
        p4Q2PZ37ADX_quaternionToOriginalFour
          (Q g * p4Q2PZ37ADX_quaternionToOriginalFour.symm (V h)) := by
            rfl
    _ = p4Q2PZ37ADX_quaternionToOriginalFour (Q g * Q h) := by
      rw [hBack]
    _ = p4Q2PZ37ADX_quaternionToOriginalFour (Q (g * h)) := by
      rw [p4Q2PZ37ADW_originalQuaternion_mul]
    _ = V (g * h) := p4Q2PZ37ADX_originalQuaternionCoordinates_eq (g * h)

/-- The linear Euclidean-space extension agrees ON THE NOSE with
ADV's original sphere action at EVERY actual S³ point. -/
theorem p4Q2PZ37ADX_originalAmbient_eq_originalSphereAction
    (g : G) (x : S3) :
    p4Q2PZ37ADX_originalAmbientLinearIsometry g (x : E4) =
      (act g x : E4) := by
  have hr : V (Ψ x) = (x : E4) := by
    exact congrArg Subtype.val (p4Q2PZ37ADS_sphere_roundtrip x)
  calc
    p4Q2PZ37ADX_originalAmbientLinearIsometry g (x : E4) =
        p4Q2PZ37ADX_originalAmbientLinearIsometry g (V (Ψ x)) := by
          rw [hr]
    _ = V (g * Ψ x) := p4Q2PZ37ADX_ambient_mul_coordinates g (Ψ x)
    _ = (act g x : E4) := rfl

/-- The original physical action extends to a linear orthogonal
transformation that preserves the literal Mathlib unit sphere. -/
theorem p4Q2PZ37ADX_originalAmbient_preservesSphere
    (g : G) (x : S3) :
    p4Q2PZ37ADX_originalAmbientLinearIsometry g (x : E4) ∈
      Metric.sphere (0 : E4) 1 := by
  rw [p4Q2PZ37ADX_originalAmbient_eq_originalSphereAction g x]
  exact (act g x).property

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADX_fourthSignFlip_apply
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADX_originalQuaternionCoordinates_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADX_ambient_mul_coordinates
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADX_originalAmbient_eq_originalSphereAction
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADX_originalAmbient_preservesSphere
