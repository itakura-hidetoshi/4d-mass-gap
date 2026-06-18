import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Standard `SU(N)` Wilson plaquette energy is invariant under conjugation. -/
theorem specialUnitaryWilsonPlaquetteEnergy_conjInvariant
    {N : ℕ}
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N (h * g * h⁻¹) =
      specialUnitaryWilsonPlaquetteEnergy N g := by
  unfold specialUnitaryWilsonPlaquetteEnergy
  congr 2
  apply congrArg Complex.re
  change Matrix.trace
      ((h : Matrix (Fin N) (Fin N) ℂ) *
        (g : Matrix (Fin N) (Fin N) ℂ) *
        ((h⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ)) =
    Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)
  rw [Matrix.trace_mul_cycle]
  simp

end

end MathlibAnalytic
end MGAP4D
