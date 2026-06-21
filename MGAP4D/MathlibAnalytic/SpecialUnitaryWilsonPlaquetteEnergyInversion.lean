import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The real-trace Wilson plaquette energy is unchanged by reversing the
orientation of an `SU(N)` plaquette holonomy. -/
theorem specialUnitaryWilsonPlaquetteEnergy_inv
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N U⁻¹ =
      specialUnitaryWilsonPlaquetteEnergy N U := by
  unfold specialUnitaryWilsonPlaquetteEnergy
  have hInv :
      (((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)) =
        star (U : Matrix (Fin N) (Fin N) ℂ) := by
    rw [← Matrix.specialUnitaryGroup.coe_star]
    exact congrArg Subtype.val (Matrix.star_eq_inv U).symm
  rw [hInv, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  simp

end

end MathlibAnalytic
end MGAP4D
