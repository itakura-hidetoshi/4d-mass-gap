import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticReflectionLimitTransfer
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitOSPropertyTransfer
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators ENNReal

noncomputable section

noncomputable def FiniteLatticeWilsonSystem.gibbsExpectationFixed
    (L : FiniteLatticeWilsonSystem)
    (O : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, (L.gibbsPMF A).toReal * O A

structure FiniteLatticeWilsonEuclideanSymmetryCertificateFixed
    (L : FiniteLatticeWilsonSystem) where
  Transformation : Type
  configurationEquiv : Transformation → Equiv L.Configuration L.Configuration
  wilsonAction_invariant :
    ∀ (g : Transformation) (A : L.Configuration),
      L.wilsonAction (configurationEquiv g A) = L.wilsonAction A

end

end MathlibAnalytic
end MGAP4D
