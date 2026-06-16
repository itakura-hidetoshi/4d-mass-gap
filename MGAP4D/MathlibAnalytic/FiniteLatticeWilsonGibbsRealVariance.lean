import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBath

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real-valued probability of a finite Wilson link configuration. -/
def FiniteLatticeWilsonSystem.gibbsProbabilityReal
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  (L.gibbsPMF A).toReal

/-- Gibbs expectation of a real observable on finite link configurations. -/
def FiniteLatticeWilsonSystem.gibbsExpectationReal
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A

/-- Every real finite Wilson Gibbs probability is nonnegative. -/
theorem finite_lattice_gibbsProbabilityReal_nonneg
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.gibbsProbabilityReal A := by
  exact ENNReal.toReal_nonneg

end

end MathlibAnalytic
end MGAP4D
