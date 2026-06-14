import MGAP4D.MathlibAnalytic.EuclideanYangMillsSpectralMeasureLaplaceRepresentation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure ExplicitWightmanOSScalarSpectralMeasureRealization
    (M : ExplicitWightmanOSReconstructedModel) where
  scalarMeasure : M.H → Measure ℝ
  singletonMass_eq_squaredProjectionNorm :
    ∀ (psi : M.H) (E : ℝ),
      (scalarMeasure psi).real ({E} : Set ℝ) =
        ‖M.spectralPVM.projection ({E} : Set ℝ) psi‖ ^ 2

end

end MathlibAnalytic
end MGAP4D
