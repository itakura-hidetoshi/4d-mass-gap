import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuaternionHaarAverageV5_PZ35C
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# P4-Q2-PZ35D — actual SU(2) trace is real (2×2 adjugate route)

A finite quaternion orbit identity must use the ORIGINAL real Wilson
character, not unqualified complex traces. For the actual compact SU(2)
group, `det g=1` forces `tr (g⁻¹)=tr g` in dimension two via mathlib's
adjugate, while unitarity gives `tr (g⁻¹)=conj (tr g)`. Hence the
complex trace belongs to the real subfield.

This is an unconditional group/matrix theorem, independent of any Schur
integral hypothesis. Later PZ35D stages will prove the four-term orbit
identity by the PZ35A trace-dual decomposition.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

/-- Any complex 2x2 matrix has the same trace as its adjugate.
A pure ring identity; no determinant or unitarity assumption. -/
theorem p4Q2PZ35D_trace_adjugate_fin_two (A : Mat) :
    Matrix.trace A.adjugate = Matrix.trace A := by
  rw [Matrix.adjugate_fin_two]
  simp [Matrix.trace_fin_two, add_comm]

/-- The actual SU(2) group inverse has the usual underlying
nonsingular 2x2 matrix inverse; this is derived from group structure. -/
theorem p4Q2PZ35D_groupInverse_coe (g : G) :
    (((g⁻¹ : G) : Mat)) = (g : Mat)⁻¹ := by
  symmetry
  apply Matrix.inv_eq_left_inv
  change ((g⁻¹ * g : G) : Mat) = (1 : Mat)
  simp

/-- Determinant one plus the Fin 2 adjugate identity gives
trace(g⁻¹)=trace(g) for the ORIGINAL SU(2) group. -/
theorem p4Q2PZ35D_trace_inverse_eq (g : G) :
    Matrix.trace (((g⁻¹ : G) : Mat)) = Matrix.trace (g : Mat) := by
  have hdet : Matrix.det (g : Mat) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  rw [p4Q2PZ35D_groupInverse_coe, Matrix.inv_def, hdet]
  simpa using p4Q2PZ35D_trace_adjugate_fin_two (g : Mat)

/-- The complex trace of every genuine SU(2) matrix is real.
This prevents accidental use of complex character orthogonality
without an explicit real-part transport. -/
theorem p4Q2PZ35D_SU2_trace_eq_real (g : G) :
    ((Matrix.trace (g : Mat)).re : ℂ) = Matrix.trace (g : Mat) := by
  have hStarInv :
      (((g⁻¹ : G) : Mat)) = (g : Mat).conjTranspose := by
    calc
      (((g⁻¹ : G) : Mat)) = ((star g : G) : Mat) := by
        rw [Matrix.star_eq_inv]
      _ = star (g : Mat) := Matrix.specialUnitaryGroup.coe_star g
      _ = (g : Mat).conjTranspose := rfl
  have hStar :
      star (Matrix.trace (g : Mat)) = Matrix.trace (g : Mat) := by
    calc
      star (Matrix.trace (g : Mat)) =
          Matrix.trace (g : Mat).conjTranspose :=
        (Matrix.trace_conjTranspose (g : Mat)).symm
      _ = Matrix.trace (((g⁻¹ : G) : Mat)) := by
        rw [hStarInv]
      _ = Matrix.trace (g : Mat) :=
        p4Q2PZ35D_trace_inverse_eq g
  exact (Complex.conj_eq_iff_re).mp (by
    simpa only [Complex.star_def] using hStar)

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D_trace_adjugate_fin_two
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D_groupInverse_coe
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D_trace_inverse_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ35D_SU2_trace_eq_real
