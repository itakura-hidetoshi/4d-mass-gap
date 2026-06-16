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
    (f : L.Configuration → ℝ) : ℝ :=
  ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A

/-- Gibbs variance of a real observable. -/
def FiniteLatticeWilsonSystem.gibbsVarianceReal
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ :=
  ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      (f A - L.gibbsExpectationReal f) ^ 2

/-- Every real finite Wilson Gibbs probability is nonnegative. -/
theorem finite_lattice_gibbsProbabilityReal_nonneg
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.gibbsProbabilityReal A := by
  exact ENNReal.toReal_nonneg

/-- Finite Wilson Gibbs variance is nonnegative. -/
theorem finite_lattice_gibbsVarianceReal_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsVarianceReal f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsVarianceReal
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg
      (finite_lattice_gibbsProbabilityReal_nonneg L A)
      (sq_nonneg _)

end

end MathlibAnalytic
end MGAP4D
