import MGAP4D.MathlibAnalytic.WightmanOSLaplaceSemigroupIdentification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def EuclideanYangMillsOSLaplaceSemigroupIdentification.toPositiveSpectralMeasure
    {C : EuclideanYangMillsConnectedObservableCore}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel}
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R) :
    EuclideanYangMillsPositiveSpectralMeasureRepresentation C :=
  { spectralMeasure := fun e => R.scalarMeasure (C.sourceVector e)
    laplaceIntegrable := L.laplaceIntegrable
    correlation_eq_laplaceIntegral := L.correlation_eq_laplaceIntegral
    singletonMass_eq_squaredProjectionNorm := by
      intro e
      exact R.singletonMass_eq_squaredProjectionNorm
        (C.sourceVector e) (e : ℝ) }

end

end MathlibAnalytic
end MGAP4D
