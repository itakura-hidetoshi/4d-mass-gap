import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathFluctuationEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

@[simp] theorem finite_lattice_replaceLink_original
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) :
    L.replaceLink A e (A e) = A := by
  classical
  funext e'
  by_cases h : e' = e
  · subst e'
    simp
  · simp [FiniteLatticeWilsonSystem.replaceLink, h]

end

end MathlibAnalytic
end MGAP4D
