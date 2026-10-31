import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyInfiniteRange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionWilsonHaarContractionV5_PZ35D4

/-!
# P4-Q2-PZ37ACL — an actual SU(2) path from identity to the original center

Use the existing original SU(2) rotation family. Its matrix entries are
the real sine and cosine coordinates already certified to be special
unitary. Direct coordinate proofs expose its continuity and identify its
values at zero and pi with the actual group identity and the SAME center
element used by the original gauge-transport theorems.

This leaf concerns only genuine SU(2) elements. It introduces no physical
source, boundary density, posterior law, or positivity assumption.
-/

namespace MGAP4D.MathlibAnalytic
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- The existing original rotation family, with its original SU(2) carrier. -/
def p4Q2PZ37ACL_originalCenterPath (t : ℝ) : G :=
  specialUnitaryTwoRotation t

/-- Continuity follows directly from the four original matrix coordinates. -/
theorem p4Q2PZ37ACL_originalCenterPath_continuous :
    Continuous p4Q2PZ37ACL_originalCenterPath := by
  change Continuous (specialUnitaryTwoRotation : ℝ → G)
  refine Continuous.subtype_mk ?_ (fun t => (specialUnitaryTwoRotation t).property)
  change Continuous (fun t : ℝ => specialUnitaryTwoRotationMatrix t)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [specialUnitaryTwoRotationMatrix] <;>
    fun_prop

/-- At zero the original rotation is exactly the original group identity. -/
theorem p4Q2PZ37ACL_originalCenterPath_zero :
    p4Q2PZ37ACL_originalCenterPath 0 = (1 : G) := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix 0 = (1 : Mat)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply]

/-- At pi the endpoint is exactly the center element used by ACC and ACK. -/
theorem p4Q2PZ37ACL_originalCenterPath_pi :
    p4Q2PZ37ACL_originalCenterPath Real.pi = p4Q2PZ35D4_centralMinusOne := by
  apply Subtype.ext
  change specialUnitaryTwoRotationMatrix Real.pi =
    ((p4Q2PZ35D4_centralMinusOne : G) : Mat)
  rw [p4Q2PZ35D4_centralMinusOne_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [specialUnitaryTwoRotationMatrix, Matrix.one_apply, Real.cos_pi, Real.sin_pi]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACL_originalCenterPath_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACL_originalCenterPath_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ACL_originalCenterPath_pi
