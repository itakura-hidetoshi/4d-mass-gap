import MGAP4D.MathlibAnalytic.WightmanOSScalarSpectralMeasurePositivity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

structure EuclideanYangMillsOSLaplaceSemigroupIdentification
    (C : EuclideanYangMillsConnectedObservableCore)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel) where
  laplaceIntegrable :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ),
      0 ≤ t →
        Integrable
          (fun E : ℝ => Real.exp (-E * t))
          (R.scalarMeasure (C.sourceVector e))
  correlation_eq_laplaceIntegral :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ),
      0 ≤ t →
        C.connectedCorrelation e t =
          MeasureTheory.integral
            (R.scalarMeasure (C.sourceVector e))
            (fun E : ℝ => Real.exp (-E * t))

end

end MathlibAnalytic
end MGAP4D
