import MGAP4D.MathlibAnalytic.WightmanOSScalarToPositiveSpectralMeasure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

def EuclideanYangMillsOSLaplaceSemigroupIdentification.toOSSpectralLaplace
    {C : EuclideanYangMillsConnectedObservableCore}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel}
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification C R) :
    EuclideanYangMillsOSSpectralLaplaceRepresentation C :=
  L.toPositiveSpectralMeasure.toOSSpectralLaplace

end

end MathlibAnalytic
end MGAP4D
