import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion

/-!
# Orientation inversion invariance of the normalized real trace

The canonical Wilson-energy layer already proves that reversing an `SU(N)` plaquette holonomy,
`U ↦ U⁻¹`, leaves the real-trace Wilson plaquette energy unchanged.  Since that energy is exactly
`1 - normalizedSpecialUnitaryRealTrace`, the normalized real trace itself is invariant under
orientation reversal.

This small theorem is the orientation-correction receipt needed by later spatial permutation and
parity layers for the all-spatial zero-momentum glueball precursor.  No lattice symmetry, continuum
spin label, spectral premise, or new physical assumption is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The normalized real trace of an `SU(N)` matrix is unchanged by inversion.  In lattice language,
reversing the orientation of a plaquette holonomy does not change the scalar Wilson trace
observable. -/
theorem normalizedSpecialUnitaryRealTrace_inv
    {N : ℕ}
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTrace N U⁻¹ =
      normalizedSpecialUnitaryRealTrace N U := by
  have hEnergy := specialUnitaryWilsonPlaquetteEnergy_inv U
  have hSub :
      1 - normalizedSpecialUnitaryRealTrace N U⁻¹ =
        1 - normalizedSpecialUnitaryRealTrace N U := by
    simpa only [specialUnitaryWilsonPlaquetteEnergy_eq] using hEnergy
  linarith

end

end MathlibAnalytic
end MGAP4D
