import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSingleLinkHeatBathDetailedBalance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Native Gibbs pairing on orientation-correct physical-link observables. -/
def FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A * f A * g A

/-- The native oriented Gibbs pairing is symmetric. -/
theorem finite_oriented_gibbsPairingReal_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g = L.gibbsPairingReal g f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

end

end MathlibAnalytic
end MGAP4D
