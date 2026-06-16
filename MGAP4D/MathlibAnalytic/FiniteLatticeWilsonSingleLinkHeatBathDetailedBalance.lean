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

@[simp] theorem finite_lattice_singleLinkBoltzmannWeight_original
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) :
    L.singleLinkBoltzmannWeight A e (A e) = L.boltzmannWeight A := by
  unfold FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight
  rw [finite_lattice_replaceLink_original]

theorem finite_lattice_singleLinkHeatBath_reversible_mass
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) (e : L.Edge) (g : L.Gauge) :
    L.gibbsPMF A * L.singleLinkConditionalPMF A e g =
      L.gibbsPMF (L.replaceLink A e g) *
        L.singleLinkConditionalPMF (L.replaceLink A e g) e (A e) := by
  rw [finite_lattice_singleLinkConditionalPMF_replaceLink]
  rw [finite_lattice_gibbsPMF_apply, finite_lattice_gibbsPMF_apply]
  rw [finite_lattice_singleLinkConditionalPMF_apply,
    finite_lattice_singleLinkConditionalPMF_apply]
  rw [finite_lattice_singleLinkBoltzmannWeight_original]
  unfold FiniteLatticeWilsonSystem.singleLinkBoltzmannWeight
  ac_rfl

end

end MathlibAnalytic
end MGAP4D
