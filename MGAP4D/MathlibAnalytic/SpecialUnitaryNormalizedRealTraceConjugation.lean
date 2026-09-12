import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation

/-!
# Conjugation invariance of the normalized real trace

The canonical Wilson-energy layer already proves conjugation invariance of the `SU(N)` plaquette
energy.  Since this energy is exactly `1 - normalizedSpecialUnitaryRealTrace`, the normalized real
trace itself is conjugation invariant.

This is the scalar receipt needed when a lattice symmetry preserves a plaquette only up to cyclic
rebasing of its boundary word, hence up to group conjugation.  No new matrix, lattice, continuum,
or spectral assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The normalized real trace is invariant under `SU(N)` conjugation. -/
theorem normalizedSpecialUnitaryRealTrace_conjInvariant
    {N : ℕ}
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N (h * g * h⁻¹) =
      normalizedSpecialUnitaryRealTrace N g := by
  have hEnergy := specialUnitaryWilsonPlaquetteEnergy_conjInvariant h g
  have hSub :
      1 - normalizedSpecialUnitaryRealTrace N (h * g * h⁻¹) =
        1 - normalizedSpecialUnitaryRealTrace N g := by
    simpa only [specialUnitaryWilsonPlaquetteEnergy_eq] using hEnergy
  linarith

end

end MathlibAnalytic
end MGAP4D
