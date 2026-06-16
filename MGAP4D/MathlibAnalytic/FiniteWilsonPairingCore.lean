import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathDetailedBalance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

def FiniteLatticeWilsonSystem.gibbsPairingReal
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration, L.gibbsProbabilityReal A * f A * g A

theorem finite_lattice_gibbsPairingReal_symm
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g = L.gibbsPairingReal g f := by
  classical
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

end

end MathlibAnalytic
end MGAP4D
