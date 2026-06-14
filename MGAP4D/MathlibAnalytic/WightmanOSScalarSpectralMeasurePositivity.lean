import MGAP4D.MathlibAnalytic.WightmanOSScalarSpectralMeasureBase

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem scalar_spectral_measure_singleton_mass_pos_of_projection_ne_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (psi : M.H) (E : ℝ)
    (hProjection : M.spectralPVM.projection ({E} : Set ℝ) psi ≠ 0) :
    0 < (R.scalarMeasure psi).real ({E} : Set ℝ) := by
  rw [R.singletonMass_eq_squaredProjectionNorm psi E]
  exact sq_pos_of_pos (norm_pos_iff.mpr hProjection)

end

end MathlibAnalytic
end MGAP4D
