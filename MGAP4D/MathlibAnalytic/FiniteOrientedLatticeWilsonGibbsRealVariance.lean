import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsMeasure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real-valued probability of an oriented physical-link configuration. -/
def FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  (L.gibbsPMF A).toReal

/-- Gibbs expectation of a real observable on physical-link configurations. -/
def FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A * f A

/-- Every real oriented Gibbs probability is nonnegative. -/
theorem finite_oriented_gibbsProbabilityReal_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.gibbsProbabilityReal A := by
  exact ENNReal.toReal_nonneg

/-- Gibbs variance of a real observable on physical positive links. -/
def FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      (f A - L.gibbsExpectationReal f) ^ 2

/-- The oriented finite Wilson Gibbs variance is nonnegative. -/
theorem finite_oriented_gibbsVarianceReal_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsVarianceReal f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg
      (finite_oriented_gibbsProbabilityReal_nonneg L A)
      (sq_nonneg _)

end

end MathlibAnalytic
end MGAP4D
