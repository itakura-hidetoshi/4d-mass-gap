import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsMeasure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real probability mass of one finite orientation-correct configuration. -/
def FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  (L.gibbsPMF A).toReal

/-- Gibbs expectation of a real orientation-correct finite Wilson observable. -/
def FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A

/-- Every real orientation-correct Gibbs probability is nonnegative. -/
theorem finite_oriented_gibbsProbabilityReal_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 ≤ L.gibbsProbabilityReal A :=
  ENNReal.toReal_nonneg

/-- Gibbs pairing of two real orientation-correct finite Wilson observables. -/
def FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A * f A * g A

/-- Gibbs variance of a real orientation-correct finite Wilson observable. -/
def FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A *
      (f A - L.gibbsExpectationReal f) ^ 2

/-- Finite orientation-correct Gibbs variance is nonnegative. -/
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

/-- The Gibbs pairing is symmetric. -/
theorem finite_oriented_gibbsPairingReal_comm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g = L.gibbsPairingReal g f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- The Gibbs self-pairing is nonnegative. -/
theorem finite_oriented_gibbsPairingReal_self_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    0 ≤ L.gibbsPairingReal f f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  exact Finset.sum_nonneg fun A _hA => by
    rw [mul_assoc]
    exact mul_nonneg
      (finite_oriented_gibbsProbabilityReal_nonneg L A)
      (mul_self_nonneg (f A))

end

end MathlibAnalytic
end MGAP4D
